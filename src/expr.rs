#[derive(PartialEq, Debug)]
pub enum Op {
    Not,        // !
    Or,         // ||
    And,        // &&
    ParenOpen,  // (
    ParenClose, // )
    Equal,      // ==
    NotEqual,   // !=
    Less,       // <
    LessEq,     // <=
    Greater,    // >
    GreaterEq,  // >=,
    Assign,     // =
    Plus,       // +
    Minus,      // -
    Multiply,   // *
    Divide,     // /
    Operand(Operand),
}

#[derive(PartialEq, Debug, Clone)]
pub enum Operand {
    Literal(String),
    Number(i64),
    Decimal(f64),
    Array(Vec<Operand>),
    Object(Object),
}

#[derive(PartialEq, Debug)]
// Iterator constructed by for .. in .. syntax. Tuple of (name of the array, index)
pub struct Iter {
    pub container: String,
    pub index: usize,
}

// Name that will be found in the execution context.
#[derive(PartialEq, Debug, Clone)]
pub struct Object {
    pub name: String,
}

#[derive(PartialEq, Debug)]
pub struct Expr {
    pub ops: Vec<Op>,
}

#[derive(PartialEq, Debug)]
pub enum Action<'a, T> {
    Show(Show<'a, T>),
    If(T),    // If condition
    While(T), // Loop condition
    For(T),   // For condition
    Else(),   // Else
    End(),    // Closing }
    Do(T),
}

impl<'a> Action<'a, Expr> {
    pub fn add_op(&mut self, op: Op) {
        match self {
            Action::Show(show) => match show {
                Show::ExprEscaped(e) => e.ops.push(op),
                Show::ExprUnescaped(e) => e.ops.push(op),
                _ => panic!("Cannot add op to Show; op {:?}", op),
            },
            Action::If(expr) => {
                expr.ops.push(op);
            }
            Action::While(expr) => {
                expr.ops.push(op);
            }
            Action::For(expr) => {
                expr.ops.push(op);
            }
            Action::Do(expr) => {
                expr.ops.push(op);
            }
            _ => panic!("Cannot add op to {:?}; op {:?}", self, op),
        }
    }
}

#[derive(PartialEq, Debug)]
pub enum Show<'a, T> {
    Html(&'a str),
    ExprEscaped(T),
    ExprUnescaped(T),
}

#[derive(PartialEq, Debug)]
pub struct Parser<'a> {
    pub parse_tree: Vec<Action<'a, Expr>>,
}

impl<'a> Parser<'a> {
    pub fn parse(mut template: &'a str) -> Result<Self, String> {
        let mut parse_tree = Vec::new();
        while !template.is_empty() {
            match template.find("<%") {
                Some(tag_start) => {
                    let before_tag = &template[..tag_start];
                    if !before_tag.is_empty() {
                        parse_tree.push(Action::Show(Show::Html(before_tag)));
                    }

                    let after_tag = &template[tag_start + 2..];
                    match after_tag.find("%>") {
                        Some(tag_end) => {
                            let tag_to_parse;
                            match template.chars().nth(tag_start + 2).unwrap() {
                                '=' => {
                                    parse_tree.push(Action::Show(Show::ExprEscaped(Expr {
                                        ops: Vec::new(),
                                    })));
                                    tag_to_parse = &after_tag[1..tag_end];
                                }
                                '-' => {
                                    parse_tree.push(Action::Show(Show::ExprUnescaped(Expr {
                                        ops: Vec::new(),
                                    })));
                                    tag_to_parse = &after_tag[1..tag_end];
                                }
                                _ => {
                                    parse_tree.push(Action::Do(Expr { ops: Vec::new() }));
                                    tag_to_parse = &after_tag[..tag_end];
                                }
                            }

                            match Parser::parse_tag(tag_to_parse, &mut parse_tree) {
                                Err(s) => {
                                    return Err(s);
                                }
                                _ => {}
                            }
                            template = &after_tag[tag_end + 2..];
                        }
                        _ => {
                            return Err("Unmatched %> tag found".to_string());
                        }
                    }
                }
                _ => {
                    parse_tree.push(Action::Show(Show::Html(template)));
                    break;
                }
            }
        }

        Ok(Parser { parse_tree })
    }

    fn parse_tag(template: &'a str, parse_tree: &mut Vec<Action<'a, Expr>>) -> Result<(), String> {
        let mut current = 0;
        let mut token_begin = 0;

        while current < template.len() {
            let current_char = template.chars().nth(current).unwrap();

            // Check string literal.
            if current_char == '"' {
                match Parser::handle_string_literal(template, current, parse_tree) {
                    Ok(end_of_literal) => {
                        current = end_of_literal;
                        token_begin = current;
                        continue;
                    }
                    Err(e) => return Err(e),
                }
            }

            // Handle Operators.
            match template[current..current + 1]
                .find(&['&', '|', '(', ')', '!', '=', '<', '>', '+', '-', '*', '/'][..])
            {
                Some(_) => {
                    Parser::handle_operand(&template[token_begin..current], parse_tree);

                    match Parser::handle_operator(template, current, parse_tree.last_mut().unwrap())
                    {
                        Ok(end_of_op) => {
                            current = end_of_op;
                            token_begin = current;
                            continue;
                        }
                        Err(e) => return Err(e),
                    }
                }
                _ => {}
            }

            if current_char == ' ' {
                let token = &template[token_begin..current];
                Parser::handle_token(token, parse_tree);

                token_begin = current + 1;
            } else if current_char == '{' {
                Parser::handle_token(&template[token_begin..current], parse_tree);
                parse_tree.push(Action::Do(Expr { ops: Vec::new() }));
                token_begin = current + 1;
            } else if current_char == '}' {
                Parser::handle_token(&template[token_begin..current], parse_tree);
                parse_tree.push(Action::End());
                token_begin = current + 1;
            } else if current_char == ';' {
                Parser::handle_token(&template[token_begin..current], parse_tree);
                match parse_tree.pop().unwrap() {
                    Action::Do(expr) => {
                        parse_tree.push(Action::Do(expr));
                        parse_tree.push(Action::Do(Expr { ops: Vec::new() }));
                    }
                    Action::Show(show) => match show {
                        Show::Html(_) => {
                            panic!("Show should not contain html");
                        }
                        Show::ExprUnescaped(expr) => {
                            // For <%= ... %> tags, only the last expression will be shown.
                            // In other words, <%= a; b %> is identical to <%= b %>
                            parse_tree.push(Action::Do(expr));
                            parse_tree
                                .push(Action::Show(Show::ExprUnescaped(Expr { ops: Vec::new() })))
                        }
                        Show::ExprEscaped(expr) => {
                            parse_tree.push(Action::Do(expr));
                            parse_tree
                                .push(Action::Show(Show::ExprEscaped(Expr { ops: Vec::new() })))
                        }
                    },
                    _ => return Err(format!("Invalid position of ; at {}", template)),
                }
                token_begin = current + 1;
            }

            current += 1;
        }

        Parser::handle_token(&template[token_begin..template.len()], parse_tree);
        Ok(())
    }

    // Returns the next of the end of the string literal.
    fn handle_string_literal(
        template: &'a str,
        start: usize,
        parse_tree: &mut Vec<Action<'a, Expr>>,
    ) -> Result<usize, String> {
        assert!(template.chars().nth(start).unwrap() == '"');
        let string_literal_end;

        // Read until closing " is found.
        let mut find_end_quote_start = start + 1;
        loop {
            match template[find_end_quote_start..].find('"') {
                Some(end_quote_pos) => {
                    if end_quote_pos == 0
                        || template[find_end_quote_start..]
                            .chars()
                            .nth(end_quote_pos - 1)
                            .unwrap()
                            != '\\'
                    {
                        string_literal_end = find_end_quote_start + end_quote_pos;
                        break;
                    } else {
                        find_end_quote_start += end_quote_pos + 1;
                    }
                }
                _ => {
                    return Err(format!(
                        "template '{}' does not have terminated \" for string.",
                        template
                    ))
                }
            }
        }

        parse_tree
            .last_mut()
            .unwrap()
            .add_op(Op::Operand(Operand::Literal(
                template[start + 1..string_literal_end].to_string(),
            )));

        Ok(string_literal_end + 1)
    }

    fn handle_operator(
        template: &'a str,
        start: usize,
        action: &mut Action<'a, Expr>,
    ) -> Result<usize, String> {
        // Check for the binary operators.
        if template.len() >= start + 2 {
            if let Some(op) = check_2_char_op(&template[start..start + 2]) {
                action.add_op(op);
                return Ok(start + 2);
            }
        }

        // Check for the unary operators.
        match template.chars().nth(start).unwrap() {
            '!' => action.add_op(Op::Not),
            '(' => action.add_op(Op::ParenOpen),
            ')' => action.add_op(Op::ParenClose),
            '<' => action.add_op(Op::Less),
            '>' => action.add_op(Op::Greater),
            '=' => action.add_op(Op::Assign),
            '+' => action.add_op(Op::Plus),
            '-' => action.add_op(Op::Minus),
            '*' => action.add_op(Op::Multiply),
            '/' => action.add_op(Op::Divide),
            c => {
                return Err(format!(
                    "Unknown operator at '{}', unknown : {}",
                    template, c
                ));
            }
        }

        Ok(start + 1)
    }

    fn handle_token(token: &'a str, parse_tree: &mut Vec<Action<'a, Expr>>) {
        if token == "if" {
            parse_tree.push(Action::If(Expr { ops: Vec::new() }));
        } else if token == "while" {
            parse_tree.push(Action::While(Expr { ops: Vec::new() }));
        } else if token == "for" {
            parse_tree.push(Action::For(Expr { ops: Vec::new() }));
        } else if token == "else" {
            parse_tree.push(Action::Else());
        } else {
            Parser::handle_operand(token, parse_tree);
        }
    }

    fn handle_operand(mut operand: &'a str, parse_tree: &mut Vec<Action<'a, Expr>>) {
        if operand.is_empty() {
            return;
        }

        operand = operand.trim();

        if let Action::End() = parse_tree.last().unwrap() {
            parse_tree.push(Action::Do(Expr { ops: Vec::new() }));
        }

        let action = parse_tree.last_mut().unwrap();

        let first_char = operand.chars().nth(0).unwrap();
        if first_char.is_ascii_digit() {
            if operand.contains('.') {
                action.add_op(Op::Operand(Operand::Decimal(
                    operand.parse().unwrap_or(0.0),
                )));
            } else {
                action.add_op(Op::Operand(Operand::Number(operand.parse().unwrap_or(0))));
            }
        } else {
            action.add_op(Op::Operand(Operand::Object(Object {
                name: operand.to_string(),
            })))
        }
    }
}

fn check_2_char_op(s: &str) -> Option<Op> {
    if s.len() != 2 {
        return None;
    }

    if s == "&&" {
        return Some(Op::And);
    } else if s == "||" {
        return Some(Op::Or);
    } else if s == "==" {
        return Some(Op::Equal);
    } else if s == "!=" {
        return Some(Op::NotEqual);
    } else if s == "<=" {
        return Some(Op::LessEq);
    } else if s == ">=" {
        return Some(Op::GreaterEq);
    }

    None
}

// Returns the operator priority; Lower number == Higher priority.
// Used the precedance table at
//   https://en.cppreference.com/w/c/language/operator_precedence.
pub fn operator_priority(op: &Op) -> u32 {
    match op {
        Op::Not => 2,
        Op::Multiply => 3,
        Op::Divide => 3,
        Op::Plus => 4,
        Op::Minus => 4,
        Op::Greater => 6,
        Op::GreaterEq => 6,
        Op::Less => 6,
        Op::LessEq => 6,
        Op::Equal => 7,
        Op::NotEqual => 7,
        Op::And => 11,
        Op::Or => 12,
        Op::Assign => 14,
        Op::ParenOpen => 100,
        Op::ParenClose => 100,
        _ => panic!("Oops {:?}", op),
    }
}

pub fn operator_num_operands(op: &Op) -> usize {
    match op {
        Op::Not => 1,
        _ => 2,
    }
}

#[test]
fn parse_simple_expr_with_binary() {
    let result = Parser::parse("<% some == 3 %>");

    let expected_expr = Parser {
        parse_tree: vec![Action::Do(Expr {
            ops: vec![
                Op::Operand(Operand::Object(Object {
                    name: "some".to_string(),
                })),
                Op::Equal,
                Op::Operand(Operand::Number(3)),
            ],
        })],
    };
    assert_eq!(result.unwrap(), expected_expr);
}

#[test]
fn parse_simple_expr_with_unary() {
    let result = Parser::parse("<% !some_value %>");

    let expected_expr = Parser {
        parse_tree: vec![Action::Do(Expr {
            ops: vec![
                Op::Not,
                Op::Operand(Operand::Object(Object {
                    name: "some_value".to_string(),
                })),
            ],
        })],
    };

    assert_eq!(result.unwrap(), expected_expr);
}

#[test]
fn parse_complex_binary_and_unary() {
    let result = Parser::parse("<% (a + b * c - e / d) * f %>");

    let expected_expr = Parser {
        parse_tree: vec![Action::Do(Expr {
            ops: vec![
                Op::ParenOpen,
                Op::Operand(Operand::Object(Object {
                    name: "a".to_string(),
                })),
                Op::Plus,
                Op::Operand(Operand::Object(Object {
                    name: "b".to_string(),
                })),
                Op::Multiply,
                Op::Operand(Operand::Object(Object {
                    name: "c".to_string(),
                })),
                Op::Minus,
                Op::Operand(Operand::Object(Object {
                    name: "e".to_string(),
                })),
                Op::Divide,
                Op::Operand(Operand::Object(Object {
                    name: "d".to_string(),
                })),
                Op::ParenClose,
                Op::Multiply,
                Op::Operand(Operand::Object(Object {
                    name: "f".to_string(),
                })),
            ],
        })],
    };

    assert_eq!(result.unwrap(), expected_expr);
}

#[test]
fn parse_simple_literal() {
    let result = Parser::parse(r#"<% some_value == "abc" %>"#);
    let expected_expr = Parser {
        parse_tree: vec![Action::Do(Expr {
            ops: vec![
                Op::Operand(Operand::Object(Object {
                    name: "some_value".to_string(),
                })),
                Op::Equal,
                Op::Operand(Operand::Literal("abc".to_string())),
            ],
        })],
    };

    assert_eq!(result.unwrap(), expected_expr);
}

#[test]
fn parse_literal_with_escape() {
    let result = Parser::parse(r#"<% some_value == "a\"bc" abc %>"#);
    let expected_expr = Parser {
        parse_tree: vec![Action::Do(Expr {
            ops: vec![
                Op::Operand(Operand::Object(Object {
                    name: "some_value".to_string(),
                })),
                Op::Equal,
                Op::Operand(Operand::Literal("a\\\"bc".to_string())),
                Op::Operand(Operand::Object(Object {
                    name: "abc".to_string(),
                })),
            ],
        })],
    };

    assert_eq!(result.unwrap(), expected_expr);
}

#[test]
fn parse_complex_expr() {
    let result = Parser::parse("<% !some_value && ((var1 != var2) || some <= val) %>");
    let expected_expr = Parser {
        parse_tree: vec![Action::Do(Expr {
            ops: vec![
                Op::Not,
                Op::Operand(Operand::Object(Object {
                    name: "some_value".to_string(),
                })),
                Op::And,
                Op::ParenOpen,
                Op::ParenOpen,
                Op::Operand(Operand::Object(Object {
                    name: "var1".to_string(),
                })),
                Op::NotEqual,
                Op::Operand(Operand::Object(Object {
                    name: "var2".to_string(),
                })),
                Op::ParenClose,
                Op::Or,
                Op::Operand(Operand::Object(Object {
                    name: "some".to_string(),
                })),
                Op::LessEq,
                Op::Operand(Operand::Object(Object {
                    name: "val".to_string(),
                })),
                Op::ParenClose,
            ],
        })],
    };

    assert_eq!(result.unwrap(), expected_expr);
}

#[test]
fn parse_complex_expr2() {
    let result = Parser::parse(r"<% var1 >= var2 && var2 <= var3 || !var3  %>");
    let expected_expr = Parser {
        parse_tree: vec![Action::Do(Expr {
            ops: vec![
                Op::Operand(Operand::Object(Object {
                    name: "var1".to_string(),
                })),
                Op::GreaterEq,
                Op::Operand(Operand::Object(Object {
                    name: "var2".to_string(),
                })),
                Op::And,
                Op::Operand(Operand::Object(Object {
                    name: "var2".to_string(),
                })),
                Op::LessEq,
                Op::Operand(Operand::Object(Object {
                    name: "var3".to_string(),
                })),
                Op::Or,
                Op::Not,
                Op::Operand(Operand::Object(Object {
                    name: "var3".to_string(),
                })),
            ],
        })],
    };

    assert_eq!(result.unwrap(), expected_expr);
}

#[test]
fn parse_if_statement() {
    let result = Parser::parse(r#"<% if var1 >= var2 && var3 < "}" { "hello" } %>"#);
    let expected_expr = Parser {
        parse_tree: vec![
            Action::Do(Expr { ops: vec![] }),
            Action::If(Expr {
                ops: vec![
                    Op::Operand(Operand::Object(Object {
                        name: "var1".to_string(),
                    })),
                    Op::GreaterEq,
                    Op::Operand(Operand::Object(Object {
                        name: "var2".to_string(),
                    })),
                    Op::And,
                    Op::Operand(Operand::Object(Object {
                        name: "var3".to_string(),
                    })),
                    Op::Less,
                    Op::Operand(Operand::Literal("}".to_string())),
                ],
            }),
            Action::Do(Expr {
                ops: vec![Op::Operand(Operand::Literal("hello".to_string()))],
            }),
            Action::End(),
        ],
    };

    assert_eq!(result.unwrap(), expected_expr);
}

#[test]
fn parse_multiple_if_statement() {
    let result = Parser::parse(r#"<% if var1>=var2{if var2>var3{} if !var1 {}} %>"#);
    let expected_expr = Parser {
        parse_tree: vec![
            Action::Do(Expr { ops: vec![] }),
            Action::If(Expr {
                ops: vec![
                    Op::Operand(Operand::Object(Object {
                        name: "var1".to_string(),
                    })),
                    Op::GreaterEq,
                    Op::Operand(Operand::Object(Object {
                        name: "var2".to_string(),
                    })),
                ],
            }),
            Action::Do(Expr { ops: vec![] }),
            Action::If(Expr {
                ops: vec![
                    Op::Operand(Operand::Object(Object {
                        name: "var2".to_string(),
                    })),
                    Op::Greater,
                    Op::Operand(Operand::Object(Object {
                        name: "var3".to_string(),
                    })),
                ],
            }),
            Action::Do(Expr { ops: vec![] }),
            Action::End(),
            Action::If(Expr {
                ops: vec![
                    Op::Not,
                    Op::Operand(Operand::Object(Object {
                        name: "var1".to_string(),
                    })),
                ],
            }),
            Action::Do(Expr { ops: vec![] }),
            Action::End(),
            Action::End(),
        ],
    };

    assert_eq!(result.unwrap(), expected_expr);
}

#[test]
fn parse_if_else_statement() {
    let result = Parser::parse(r#"<% if var1>=var2{ "b" } else if var1==3{"a"}else{"c"}%>"#);
    let expected_expr = Parser {
        parse_tree: vec![
            Action::Do(Expr { ops: vec![] }),
            Action::If(Expr {
                ops: vec![
                    Op::Operand(Operand::Object(Object {
                        name: "var1".to_string(),
                    })),
                    Op::GreaterEq,
                    Op::Operand(Operand::Object(Object {
                        name: "var2".to_string(),
                    })),
                ],
            }),
            Action::Do(Expr {
                ops: vec![Op::Operand(Operand::Literal("b".to_string()))],
            }),
            Action::End(),
            Action::Else(),
            Action::If(Expr {
                ops: vec![
                    Op::Operand(Operand::Object(Object {
                        name: "var1".to_string(),
                    })),
                    Op::Equal,
                    Op::Operand(Operand::Number(3)),
                ],
            }),
            Action::Do(Expr {
                ops: vec![Op::Operand(Operand::Literal("a".to_string()))],
            }),
            Action::End(),
            Action::Else(),
            Action::Do(Expr {
                ops: vec![Op::Operand(Operand::Literal("c".to_string()))],
            }),
            Action::End(),
        ],
    };

    assert_eq!(result.unwrap(), expected_expr);
}

#[test]
fn parse_while_statement() {
    let result = Parser::parse(r#"<% while var1 >= var2{ "hello"} %>"#);
    let expected_expr = Parser {
        parse_tree: vec![
            Action::Do(Expr { ops: vec![] }),
            Action::While(Expr {
                ops: vec![
                    Op::Operand(Operand::Object(Object {
                        name: "var1".to_string(),
                    })),
                    Op::GreaterEq,
                    Op::Operand(Operand::Object(Object {
                        name: "var2".to_string(),
                    })),
                ],
            }),
            Action::Do(Expr {
                ops: vec![Op::Operand(Operand::Literal("hello".to_string()))],
            }),
            Action::End(),
        ],
    };

    assert_eq!(result.unwrap(), expected_expr);
}

#[test]
fn parse_for_statement() {
    let result = Parser::parse(r#"<% for a in vec{ "hello"} %>"#);
    let expected_expr = Parser {
        parse_tree: vec![
            Action::Do(Expr { ops: vec![] }),
            Action::For(Expr {
                ops: vec![
                    Op::Operand(Operand::Object(Object {
                        name: "a".to_string(),
                    })),
                    Op::Operand(Operand::Object(Object {
                        name: "in".to_string(),
                    })),
                    Op::Operand(Operand::Object(Object {
                        name: "vec".to_string(),
                    })),
                ],
            }),
            Action::Do(Expr {
                ops: vec![Op::Operand(Operand::Literal("hello".to_string()))],
            }),
            Action::End(),
        ],
    };

    assert_eq!(result.unwrap(), expected_expr);
}

#[test]
fn parse_tags_simple() {
    let result = Parser::parse(r#"<html><% if a { %>some tag<% } %>"#);
    let expected_expr = Parser {
        parse_tree: vec![
            Action::Show(Show::Html("<html>")),
            Action::Do(Expr { ops: vec![] }),
            Action::If(Expr {
                ops: vec![Op::Operand(Operand::Object(Object {
                    name: "a".to_string(),
                }))],
            }),
            Action::Do(Expr { ops: vec![] }),
            Action::Show(Show::Html("some tag")),
            Action::Do(Expr { ops: vec![] }),
            Action::End(),
        ],
    };

    assert_eq!(result.unwrap(), expected_expr);
}

#[test]
fn parse_tags_escaped() {
    let result = Parser::parse(r#"<html><% if a { %><%= data %><% } %>"#);
    let expected_expr = Parser {
        parse_tree: vec![
            Action::Show(Show::Html("<html>")),
            Action::Do(Expr { ops: vec![] }),
            Action::If(Expr {
                ops: vec![Op::Operand(Operand::Object(Object {
                    name: "a".to_string(),
                }))],
            }),
            Action::Do(Expr { ops: vec![] }),
            Action::Show(Show::ExprEscaped(Expr {
                ops: vec![Op::Operand(Operand::Object(Object {
                    name: "data".to_string(),
                }))],
            })),
            Action::Do(Expr { ops: vec![] }),
            Action::End(),
        ],
    };

    assert_eq!(result.unwrap(), expected_expr);
}

#[test]
fn parse_multipe_expressions() {
    let result = Parser::parse(r#"<html><% a; b; c %><%= a; b %><%- a; b  %>"#);
    let expected_expr = Parser {
        parse_tree: vec![
            Action::Show(Show::Html("<html>")),
            Action::Do(Expr {
                ops: vec![Op::Operand(Operand::Object(Object {
                    name: "a".to_string(),
                }))],
            }),
            Action::Do(Expr {
                ops: vec![Op::Operand(Operand::Object(Object {
                    name: "b".to_string(),
                }))],
            }),
            Action::Do(Expr {
                ops: vec![Op::Operand(Operand::Object(Object {
                    name: "c".to_string(),
                }))],
            }),
            Action::Do(Expr {
                ops: vec![Op::Operand(Operand::Object(Object {
                    name: "a".to_string(),
                }))],
            }),
            Action::Show(Show::ExprEscaped(Expr {
                ops: vec![Op::Operand(Operand::Object(Object {
                    name: "b".to_string(),
                }))],
            })),
            Action::Do(Expr {
                ops: vec![Op::Operand(Operand::Object(Object {
                    name: "a".to_string(),
                }))],
            }),
            Action::Show(Show::ExprUnescaped(Expr {
                ops: vec![Op::Operand(Operand::Object(Object {
                    name: "b".to_string(),
                }))],
            })),
        ],
    };

    assert_eq!(result.unwrap(), expected_expr);
}
