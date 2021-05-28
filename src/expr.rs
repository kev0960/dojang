#![allow(dead_code)]

#[derive(PartialEq, Debug)]
pub enum Op<'a> {
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
    GreaterEq,  // >=
    Operand(Operand<'a>),
}

#[derive(PartialEq, Debug, Clone)]
pub enum Operand<'a> {
    Literal(&'a str),
    Number(i64),
    Decimal(f64),
    Object(Object<'a>),
}

// Name that will be found in the execution context.
#[derive(PartialEq, Debug, Clone)]
pub struct Object<'a> {
    pub name: &'a str,
}

#[derive(PartialEq, Debug)]
pub struct Expr<'a> {
    pub ops: Vec<Op<'a>>,
}

#[derive(PartialEq, Debug)]
pub enum Action<'a> {
    Show(Show<'a>),
    If(Expr<'a>),    // If condition
    While(Expr<'a>), // Loop condition
    End(),           // Closing }
    Do(Expr<'a>),
    Null(),
}

impl<'a> Action<'a> {
    pub fn add_op(&mut self, op: Op<'a>) {
        match self {
            Action::Show(show) => match show {
                Show::Expr(e) => e.ops.push(op),
                _ => panic!("Cannot add op to Show; op {:?}", op),
            },
            Action::If(expr) => {
                expr.ops.push(op);
            }
            Action::While(expr) => {
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
pub enum Show<'a> {
    Html(&'a str),
    Expr(Expr<'a>),
}

#[derive(PartialEq, Debug)]
pub struct Parser<'a> {
    pub parse_tree: Vec<Action<'a>>,
}

impl<'a> Parser<'a> {
    pub fn parse(template: &'a str) -> Result<Self, String> {
        let mut current = 0;
        let mut token_begin = 0;

        let mut parse_tree = Vec::new();
        parse_tree.push(Action::Do(Expr { ops: Vec::new() }));

        while current < template.len() {
            let current_char = template.chars().nth(current).unwrap();

            // Check string literal.
            if current_char == '"' {
                match Parser::handle_string_literal(template, current, &mut parse_tree) {
                    Ok(end_of_literal) => {
                        current = end_of_literal;
                        token_begin = current;
                        continue;
                    }
                    Err(e) => return Err(e),
                }
            }

            // Handle Operators.
            match template[current..current + 1].find(&['&', '|', '(', ')', '!', '=', '<', '>'][..])
            {
                Some(_) => {
                    Parser::handle_operand(
                        &template[token_begin..current],
                        parse_tree.last_mut().unwrap(),
                    );

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
                if token == "if" {
                    parse_tree.push(Action::If(Expr { ops: Vec::new() }));
                } else if token == "while" {
                    parse_tree.push(Action::While(Expr { ops: Vec::new() }));
                } else {
                    Parser::handle_operand(token, parse_tree.last_mut().unwrap());
                }

                token_begin = current + 1;
            } else if current_char == '{' {
                Parser::handle_operand(
                    &template[token_begin..current],
                    parse_tree.last_mut().unwrap(),
                );

                parse_tree.push(Action::Do(Expr { ops: Vec::new() }));
                token_begin = current + 1;
            } else if current_char == '}' {
                Parser::handle_operand(
                    &template[token_begin..current],
                    parse_tree.last_mut().unwrap(),
                );

                parse_tree.push(Action::End());
                token_begin = current + 1;
            }

            current += 1;
        }

        Parser::handle_operand(
            &template[token_begin..template.len()],
            parse_tree.last_mut().unwrap(),
        );

        Ok(Parser { parse_tree })
    }

    // Returns the next of the end of the string literal.
    fn handle_string_literal(
        template: &'a str,
        start: usize,
        parse_tree: &mut Vec<Action<'a>>,
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
                &template[start + 1..string_literal_end],
            )));

        Ok(string_literal_end + 1)
    }

    fn handle_operator(
        template: &'a str,
        start: usize,
        action: &mut Action<'a>,
    ) -> Result<usize, String> {
        // Check for the binary operators.
        if template.len() >= start + 2 {
            if let Some(op) = check_binary_op(&template[start..start + 2]) {
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
            _ => {
                return Err(format!("Unknown operator at {}", template));
            }
        }

        Ok(start + 1)
    }

    fn handle_operand(mut operand: &'a str, action: &mut Action<'a>) {
        if operand.is_empty() {
            return;
        }

        operand = operand.trim();

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
            action.add_op(Op::Operand(Operand::Object(Object { name: operand })))
        }
    }
}

impl<'a> Expr<'a> {
    fn to_prefix(&mut self) {
        let mut operands = Vec::new();
        let mut operators = Vec::new();

        for op in &self.ops {
            match op {
                Op::Operand(operand) => {
                    operands.push(operand);
                }
                operator => operators.push(operator),
            }
        }
    }
}

fn check_binary_op(s: &str) -> Option<Op> {
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
        Op::Greater => 6,
        Op::GreaterEq => 6,
        Op::Less => 6,
        Op::LessEq => 6,
        Op::Equal => 7,
        Op::NotEqual => 7,
        Op::And => 11,
        Op::Or => 12,
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
    let result = Parser::parse("some == 3");

    let expected_expr = Parser {
        parse_tree: vec![Action::Do(Expr {
            ops: vec![
                Op::Operand(Operand::Object(Object { name: "some" })),
                Op::Equal,
                Op::Operand(Operand::Number(3)),
            ],
        })],
    };
    assert_eq!(result.unwrap(), expected_expr);
}

#[test]
fn parse_simple_expr_with_unary() {
    let result = Parser::parse("!some_value");

    let expected_expr = Parser {
        parse_tree: vec![Action::Do(Expr {
            ops: vec![
                Op::Not,
                Op::Operand(Operand::Object(Object { name: "some_value" })),
            ],
        })],
    };

    assert_eq!(result.unwrap(), expected_expr);
}

#[test]
fn parse_simple_literal() {
    let result = Parser::parse(r#"some_value == "abc""#);
    let expected_expr = Parser {
        parse_tree: vec![Action::Do(Expr {
            ops: vec![
                Op::Operand(Operand::Object(Object { name: "some_value" })),
                Op::Equal,
                Op::Operand(Operand::Literal("abc")),
            ],
        })],
    };

    assert_eq!(result.unwrap(), expected_expr);
}

#[test]
fn parse_literal_with_escape() {
    let result = Parser::parse(r#"some_value == "a\"bc" abc"#);
    let expected_expr = Parser {
        parse_tree: vec![Action::Do(Expr {
            ops: vec![
                Op::Operand(Operand::Object(Object { name: "some_value" })),
                Op::Equal,
                Op::Operand(Operand::Literal("a\\\"bc")),
                Op::Operand(Operand::Object(Object { name: "abc" })),
            ],
        })],
    };

    assert_eq!(result.unwrap(), expected_expr);
}

#[test]
fn parse_complex_expr() {
    let result = Parser::parse("!some_value && ((var1 != var2) || some <= val)");
    let expected_expr = Parser {
        parse_tree: vec![Action::Do(Expr {
            ops: vec![
                Op::Not,
                Op::Operand(Operand::Object(Object { name: "some_value" })),
                Op::And,
                Op::ParenOpen,
                Op::ParenOpen,
                Op::Operand(Operand::Object(Object { name: "var1" })),
                Op::NotEqual,
                Op::Operand(Operand::Object(Object { name: "var2" })),
                Op::ParenClose,
                Op::Or,
                Op::Operand(Operand::Object(Object { name: "some" })),
                Op::LessEq,
                Op::Operand(Operand::Object(Object { name: "val" })),
                Op::ParenClose,
            ],
        })],
    };

    assert_eq!(result.unwrap(), expected_expr);
}

#[test]
fn parse_complex_expr2() {
    let result = Parser::parse(r"var1 >= var2 && var2 <= var3 || !var3 ");
    let expected_expr = Parser {
        parse_tree: vec![Action::Do(Expr {
            ops: vec![
                Op::Operand(Operand::Object(Object { name: "var1" })),
                Op::GreaterEq,
                Op::Operand(Operand::Object(Object { name: "var2" })),
                Op::And,
                Op::Operand(Operand::Object(Object { name: "var2" })),
                Op::LessEq,
                Op::Operand(Operand::Object(Object { name: "var3" })),
                Op::Or,
                Op::Not,
                Op::Operand(Operand::Object(Object { name: "var3" })),
            ],
        })],
    };

    assert_eq!(result.unwrap(), expected_expr);
}

#[test]
fn parse_if_statement() {
    let result = Parser::parse(r#"if var1 >= var2 && var3 < "}" { "asdf" }"#);
    let expected_expr = Parser {
        parse_tree: vec![
            Action::Do(Expr { ops: vec![] }),
            Action::If(Expr {
                ops: vec![
                    Op::Operand(Operand::Object(Object { name: "var1" })),
                    Op::GreaterEq,
                    Op::Operand(Operand::Object(Object { name: "var2" })),
                    Op::And,
                    Op::Operand(Operand::Object(Object { name: "var3" })),
                    Op::Less,
                    Op::Operand(Operand::Literal("}")),
                ],
            }),
            Action::Do(Expr {
                ops: vec![Op::Operand(Operand::Literal("asdf"))],
            }),
            Action::End(),
        ],
    };

    assert_eq!(result.unwrap(), expected_expr);
}

#[test]
fn parse_multiple_if_statement() {
    let result = Parser::parse(r#"if var1>=var2{if var2>var3{} if !var1 {}}"#);
    let expected_expr = Parser {
        parse_tree: vec![
            Action::Do(Expr { ops: vec![] }),
            Action::If(Expr {
                ops: vec![
                    Op::Operand(Operand::Object(Object { name: "var1" })),
                    Op::GreaterEq,
                    Op::Operand(Operand::Object(Object { name: "var2" })),
                ],
            }),
            Action::Do(Expr { ops: vec![] }),
            Action::If(Expr {
                ops: vec![
                    Op::Operand(Operand::Object(Object { name: "var2" })),
                    Op::Greater,
                    Op::Operand(Operand::Object(Object { name: "var3" })),
                ],
            }),
            Action::Do(Expr { ops: vec![] }),
            Action::End(),
            Action::If(Expr {
                ops: vec![
                    Op::Not,
                    Op::Operand(Operand::Object(Object { name: "var1" })),
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
fn parse_while_statement() {
    let result = Parser::parse(r#"while var1 >= var2{"asdf"}"#);
    let expected_expr = Parser {
        parse_tree: vec![
            Action::Do(Expr { ops: vec![] }),
            Action::While(Expr {
                ops: vec![
                    Op::Operand(Operand::Object(Object { name: "var1" })),
                    Op::GreaterEq,
                    Op::Operand(Operand::Object(Object { name: "var2" })),
                ],
            }),
            Action::Do(Expr {
                ops: vec![Op::Operand(Operand::Literal("asdf"))],
            }),
            Action::End(),
        ],
    };

    assert_eq!(result.unwrap(), expected_expr);
}
