#![allow(dead_code)]
use crate::context::*;
use crate::eval::*;
use crate::expr::*;
use html_escape::encode_safe;
#[cfg(test)]
use serde_json::Value;
use std::collections::{BTreeMap, HashMap};

// The executer that renders the template.
pub struct Executer<'a> {
    insts: Vec<Action<'a, Eval>>,

    // Tells where the instructor point to jump
    // - For, If, While: Tells where to jump if the condition is false.
    // - End: Tells where to jump if hit.
    jump_table: HashMap<usize, usize>,
}

impl<'a> Executer<'a> {
    pub fn new(mut parser: Parser<'a>) -> Result<Self, String> {
        let mut insts = Vec::new();

        while !parser.parse_tree.is_empty() {
            let expr = parser.parse_tree.pop().unwrap();
            insts.push(convert_expr_to_eval(expr)?)
        }

        insts.reverse();

        Ok(Executer {
            jump_table: Executer::compute_jump_table(&insts)?,
            insts,
        })
    }

    fn compute_jump_table(insts: &Vec<Action<'a, Eval>>) -> Result<HashMap<usize, usize>, String> {
        let mut inst_index = 0;

        let mut jump_table = HashMap::new();
        let mut if_matching_ends = BTreeMap::new();
        let mut opened = Vec::new();

        while inst_index < insts.len() {
            match insts.get(inst_index).unwrap() {
                Action::If(_) => opened.push(inst_index),
                Action::While(_) => opened.push(inst_index),
                Action::For(_) => opened.push(inst_index),
                Action::Else() => {
                    if let Some(Action::If(_)) = insts.get(inst_index + 1) {
                        inst_index += 1;
                        continue;
                    } else {
                        opened.push(inst_index)
                    }
                }

                Action::End() => {
                    if opened.is_empty() {
                        return Err(format!(
                            "Unmatched end found at {:?} for {:?}",
                            inst_index, insts
                        ));
                    }

                    let open_index = opened.pop().unwrap();
                    match insts.get(open_index).unwrap() {
                        Action::If(_) => {
                            if_matching_ends.insert(open_index, inst_index + 1);
                        }
                        Action::Else() => {
                            if_matching_ends.insert(open_index, inst_index + 1);
                        }
                        Action::For(_) => {
                            jump_table.insert(open_index, inst_index + 1);
                            jump_table.insert(inst_index, open_index);
                        }
                        Action::While(_) => {
                            jump_table.insert(open_index, inst_index + 1);
                            jump_table.insert(inst_index, open_index);
                        }
                        _ => {
                            return Err(format!(
                                "Unknown action {:?} with closing parentheses",
                                insts
                            ))
                        }
                    }
                }
                _ => {}
            }

            inst_index += 1;
        }

        if !opened.is_empty() {
            return Err(format!("No closing bracket found {:?}", insts));
        }

        // Now scan again to handle if-else.
        while !if_matching_ends.is_empty() {
            let (if_start, if_block_end) = if_matching_ends.iter().next().unwrap();
            let if_start = *if_start;
            let mut if_block_end = *if_block_end;

            let mut if_else_block_starts = vec![if_start];

            // Find the index of all "if"s in same if-else block.
            loop {
                if let Some(&Action::Else()) = insts.get(if_block_end) {
                    // If this is the if-else statement
                    if let Some(&Action::If(_)) = insts.get(if_block_end + 1) {
                        if_else_block_starts.push(if_block_end + 1);
                        if_block_end = *if_matching_ends.get(&(if_block_end + 1)).unwrap();
                    } else {
                        if_else_block_starts.push(if_block_end);

                        // Otherwise this is just else statement.
                        if_block_end = *if_matching_ends.get(&if_block_end).unwrap();
                        break;
                    }
                } else {
                    break;
                }
            }

            // "End" of if statement should point to next of the End of the if-else block.
            // "If" of the if statement should point to next of the End.
            for if_start in if_else_block_starts {
                let if_end = *if_matching_ends.get(&if_start).unwrap();

                // This is the case when the condition is true.
                jump_table.insert(if_end - 1, if_block_end);

                // This is the case when the condition is false.
                jump_table.insert(if_start, if_end);

                if_matching_ends.remove(&if_start);
            }
        }

        Ok(jump_table)
    }

    pub fn render(&self, context: &'a mut Context) -> Result<String, String> {
        let mut rendered = String::new();
        let mut for_index_counter = HashMap::new();

        let mut inst_index = 0;
        while inst_index < self.insts.len() {
            match self.insts.get(inst_index).unwrap() {
                Action::Show(show) => match show {
                    Show::Html(html) => {
                        rendered.push_str(html);
                    }
                    Show::ExprEscaped(eval) => {
                        rendered.push_str(&*encode_safe(&Executer::run_eval(context, &eval)?));
                    }
                    Show::ExprUnescaped(eval) => {
                        rendered.push_str(&Executer::run_eval(context, &eval)?);
                    }
                },
                Action::If(eval) | Action::While(eval) => {
                    // Jump only if the condition is false. Otherwise just go to next instruction.
                    if !eval.run(context)?.is_true() {
                        if let Some(next) = self.jump_table.get(&inst_index) {
                            inst_index = *next;
                            continue;
                        } else {
                            return Err(format!(
                                "Jump of the if statement is not set: {:?} index : {}",
                                self.insts, inst_index
                            ));
                        }
                    }
                }
                Action::For(eval) => {
                    let iter_index = match for_index_counter.get(&inst_index) {
                        Some(index) => *index,
                        None => 0usize,
                    };

                    for_index_counter.insert(inst_index, iter_index + 1);
                    if !eval.run_for_loop(context, iter_index)? {
                        if let Some(next) = self.jump_table.get(&inst_index) {
                            // Reset the index counter.
                            for_index_counter.insert(inst_index, 0);

                            inst_index = *next;

                            continue;
                        } else {
                            return Err(format!(
                                "Jump of the if statement is not set: {:?} index : {}",
                                self.insts, inst_index
                            ));
                        }
                    }
                }
                Action::End() => {
                    if let Some(next) = self.jump_table.get(&inst_index) {
                        inst_index = *next;
                        continue;
                    }
                }
                Action::Do(eval) => {
                    &Executer::run_eval(context, &eval)?;
                }
                Action::Else() => {}
            }

            inst_index += 1;
        }

        Ok(rendered)
    }

    // Runs Eval if it is not empty.
    fn run_eval(context: &mut Context, eval: &Eval) -> Result<String, String> {
        if eval.is_empty() {
            return Ok("".to_string());
        }

        Ok(eval.run(context)?.to_str())
    }
}

fn convert_expr_to_eval<'a>(action: Action<'a, Expr>) -> Result<Action<'a, Eval>, String> {
    match action {
        Action::Show(show) => match show {
            Show::Html(html) => Ok(Action::Show(Show::Html(html))),
            Show::ExprEscaped(expr) => Ok(Action::Show(Show::ExprEscaped(Eval::new(expr)?))),
            Show::ExprUnescaped(expr) => Ok(Action::Show(Show::ExprUnescaped(Eval::new(expr)?))),
        },
        Action::If(expr) => Ok(Action::If(Eval::new(expr)?)),
        Action::While(expr) => Ok(Action::While(Eval::new(expr)?)),
        Action::Do(expr) => Ok(Action::Do(Eval::new(expr)?)),
        Action::For(expr) => Ok(Action::For(Eval::new(expr)?)),
        Action::Else() => Ok(Action::Else()),
        Action::End() => Ok(Action::End()),
    }
}

#[test]
fn test_if_jump_table() {
    let executer = Executer::new(
        Parser::parse(r#"<% if var1>=var2{ "b" } else if var1==3{"a"}else{"c"}%>"#).unwrap(),
    )
    .unwrap();

    assert_eq!(
        executer.jump_table,
        [(1, 4), (3, 11), (5, 8), (7, 11), (8, 11), (10, 11)]
            .iter()
            .cloned()
            .collect()
    )
}

#[test]
fn test_multiple_ifs() {
    let executer = Executer::new(
        Parser::parse(r#"<% if a >= b {} else if c >= a {} if a > b {} %>"#).unwrap(),
    )
    .unwrap();

    assert_eq!(
        executer.jump_table,
        [(1, 4), (3, 8), (5, 8), (7, 8), (8, 11), (10, 11)]
            .iter()
            .cloned()
            .collect()
    )
}

#[test]
fn test_nested_ifs() {
    let executer = Executer::new(
        Parser::parse(
            r#"<% if a { if a {} else if b { if a {}} else {} if a {} } else { if a {}} %>"#,
        )
        .unwrap(),
    )
    .unwrap();

    assert_eq!(
        executer.jump_table,
        [
            (1, 20),
            (3, 6),
            (5, 16),
            (7, 13),
            (9, 12),
            (11, 12),
            (12, 16),
            (13, 16),
            (15, 16),
            (16, 19),
            (18, 19),
            (19, 26),
            (20, 26),
            (22, 25),
            (24, 25),
            (25, 26)
        ]
        .iter()
        .cloned()
        .collect()
    )
}

#[test]
fn test_while_and_if() {
    let executer =
        Executer::new(Parser::parse(r#"<% while a < 3 { if a < 2 {} else {} } %>"#).unwrap())
            .unwrap();

    assert_eq!(
        executer.jump_table,
        [(1, 10), (3, 6), (5, 9), (6, 9), (8, 9), (9, 1)]
            .iter()
            .cloned()
            .collect()
    )
}

#[test]
fn test_for_and_if() {
    let executer =
        Executer::new(Parser::parse(r#"<% for a in v { if a < 2 {} else {} } %>"#).unwrap())
            .unwrap();

    assert_eq!(
        executer.jump_table,
        [(1, 10), (3, 6), (5, 9), (6, 9), (8, 9), (9, 1)]
            .iter()
            .cloned()
            .collect()
    )
}

#[test]
fn test_arithmetic_exec() {
    let context_json = r#"{"a": 1, "b":2, "c": 3, "d" : 2, "e" : 6, "f" : 2}"#;
    {
        let context_value: Value = serde_json::from_str(context_json).unwrap();
        let mut context = Context::new(context_value);

        // b = a = (1 + 2 * 3 - 6 / 2) * 2  == 8
        let executer = Executer::new(
            Parser::parse(
                r"<% b = a = (a + b * c - e / d) * f;e=a+b; if e == 16 { g = 5; h = 6} %>g=<%= g %> h=<%= h %>",
            )
            .unwrap(),
        )
        .unwrap();

        let result = executer.render(&mut context).unwrap();

        assert_eq!(result, "g=5 h=6".to_string());
    }
}

#[test]
fn test_while_exec() {
    let executer = Executer::new(
        Parser::parse(r#"<% a = 0; while a < 3 { if a == 1 { %>One <% } else { %>a = <%= a %> <% } a = a + 1 } %>"#).unwrap(),
    )
    .unwrap();

    let mut context = Context::new(Value::from(""));
    let result = executer.render(&mut context).unwrap();

    assert_eq!(result, "a = 0 One a = 2 ".to_string());
}

#[test]
fn test_for_in_statement() {
    let executer =
        Executer::new(Parser::parse(r#"<% for x in arr { %><%= x %> <% } %>"#).unwrap()).unwrap();

    let context_json = r#"{"arr" : [1,2,3,4,5]}"#;
    let context_value: Value = serde_json::from_str(context_json).unwrap();
    let mut context = Context::new(context_value);

    let result = executer.render(&mut context).unwrap();

    assert_eq!(result, "1 2 3 4 5 ".to_string());
}

#[test]
fn test_nested_for_in_statement() {
    let executer = Executer::new(
        Parser::parse(
            r#"<% for x in arr { for y in arr2 { %><%= x %>*<%= y %>=<%= x * y %>,<% } } %>"#,
        )
        .unwrap(),
    )
    .unwrap();

    let context_json = r#"{"arr" : [1,2,3,4,5], "arr2" : [1,2]}"#;
    let context_value: Value = serde_json::from_str(context_json).unwrap();
    let mut context = Context::new(context_value);

    let result = executer.render(&mut context).unwrap();
    assert_eq!(
        result,
        "1*1=1,1*2=2,2*1=2,2*2=4,3*1=3,3*2=6,4*1=4,4*2=8,5*1=5,5*2=10,".to_string()
    );
}
