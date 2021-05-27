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

impl<'a> Expr<'a> {
    pub fn parse(mut expr: &'a str) -> Result<Self, String> {
        let mut ops = Vec::new();
        while !expr.is_empty() {
            match expr.find(&['&', '|', '(', ')', '!', '=', '<', '>'][..]) {
                Some(index) => {
                    match Expr::parse_operand(&expr[..index]) {
                        Some(operand) => {
                            ops.push(Op::Operand(operand));
                        }
                        _ => {}
                    }

                    // Check for the binary operators.
                    if expr.len() >= index + 2 {
                        if let Some(op) = check_binary_op(&expr[index..index + 2]) {
                            ops.push(op);
                            expr = &expr[index + 2..];
                            continue;
                        }
                    }

                    // Check for the unary operators.
                    match expr.chars().nth(index).unwrap() {
                        '!' => ops.push(Op::Not),
                        '(' => ops.push(Op::ParenOpen),
                        ')' => ops.push(Op::ParenClose),
                        '<' => ops.push(Op::Less),
                        '>' => ops.push(Op::Greater),
                        _ => {
                            return Err(format!("Unknown operator at {}", expr));
                        }
                    }

                    expr = &expr[index + 1..]
                }
                _ => {
                    match Expr::parse_operand(expr) {
                        Some(operand) => ops.push(Op::Operand(operand)),
                        _ => {
                            println!("Unable to parse : {}", expr);
                        }
                    }
                    break;
                }
            }
        }

        Ok(Expr { ops })
    }

    fn parse_operand(mut expr: &str) -> Option<Operand> {
        expr = expr.trim();

        if expr.is_empty() {
            return None;
        }

        let first_char = expr.chars().nth(0).unwrap();
        if first_char.is_ascii_digit() {
            if expr.contains('.') {
                return Some(Operand::Decimal(expr.parse().unwrap_or(0.0)));
            } else {
                return Some(Operand::Number(expr.parse().unwrap_or(0)));
            }
        } else if first_char == '"' {
            return Some(Operand::Literal(&expr[1..expr.len() - 1]));
        }

        Some(Operand::Object(Object { name: expr }))
    }

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
    let result = Expr::parse("some == 3");

    let expected_expr = Expr {
        ops: vec![
            Op::Operand(Operand::Object(Object { name: "some" })),
            Op::Equal,
            Op::Operand(Operand::Number(3)),
        ],
    };
    assert_eq!(result.unwrap(), expected_expr);
}

#[test]
fn parse_simple_expr_with_unary() {
    let result = Expr::parse("!some_value");

    let expected_expr = Expr {
        ops: vec![
            Op::Not,
            Op::Operand(Operand::Object(Object { name: "some_value" })),
        ],
    };
    assert_eq!(result.unwrap(), expected_expr);
}

#[test]
fn parse_simple_literal() {
    let result = Expr::parse(r#"some_value == "abc""#);

    let expected_expr = Expr {
        ops: vec![
            Op::Operand(Operand::Object(Object { name: "some_value" })),
            Op::Equal,
            Op::Operand(Operand::Literal("abc")),
        ],
    };
    assert_eq!(result.unwrap(), expected_expr);
}

#[test]
fn parse_complex_expr() {
    let result = Expr::parse("!some_value && ((var1 != var2) || some <= val)");

    let expected_expr = Expr {
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
    };

    assert_eq!(result.unwrap(), expected_expr);
}

#[test]
fn parse_complex_expr2() {
    let result = Expr::parse(r"var1 >= var2 && var2 <= var3 || !var3 ");

    let expected_expr = Expr {
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
    };

    assert_eq!(result.unwrap(), expected_expr);
}
