use crate::expr::*;

// Evaluate the parsed expression.
#[derive(PartialEq, Debug)]
pub struct Eval {
    pub expr: Vec<Op>,
}

impl Eval {
    pub fn new(mut expr: Tokens) -> Result<Eval, String> {
        let mut operands: Vec<Vec<Op>> = Vec::new();
        let mut operators = Vec::new();

        // Wrap the expression with ().
        expr.ops.push(Op::ParenClose);
        expr.ops.insert(0, Op::ParenOpen);

        // We have to scan from the back.
        expr.ops.reverse();
        while !expr.ops.is_empty() {
            let op = expr.ops.pop().unwrap();

            match op {
                Op::Operand(operand) => {
                    operands.push(vec![Op::Operand(operand)]);
                }
                optr => {
                    if optr == Op::ParenOpen {
                        operators.push(optr);
                        continue;
                    }

                    if operators.is_empty() {
                        operators.push(optr);
                        continue;
                    }

                    loop {
                        let last_op = operators.last().unwrap();
                        if is_second_priority_higher(last_op, &optr) {
                            operators.push(optr);
                            break;
                        } else if last_op == &Op::ParenOpen && optr == Op::ParenClose {
                            operators.pop();
                            break;
                        } else if (optr == Op::Not || optr == Op::Assign)
                            && is_second_priority_higher_or_equal(last_op, &optr)
                        {
                            operators.push(optr);
                            break;
                        }

                        let top_optr = operators.pop().unwrap();

                        let mut popped_operands: Vec<Vec<Op>> = Vec::new();
                        for _ in 0..operator_num_operands(&top_optr) {
                            match operands.pop() {
                                Some(operand) => {
                                    popped_operands.push(operand);
                                }
                                _ => {
                                    break;
                                }
                            }
                        }

                        popped_operands.push(vec![top_optr]);
                        popped_operands.reverse();

                        operands.push(popped_operands.into_iter().flatten().collect());
                    }
                }
            }
        }

        Ok(Eval {
            expr: operands.into_iter().flatten().collect(),
        })
    }

    pub fn is_empty(&self) -> bool {
        self.expr.is_empty()
    }

    pub fn get_keyword(&self) -> Option<Keyword> {
        if self.expr.len() != 1 {
            return None;
        }

        match self.expr.get(0).unwrap() {
            Op::Operand(operand) => match operand {
                Operand::Keyword(keyword) => Some(keyword.clone()),
                _ => None,
            },
            _ => None,
        }
    }
}

fn is_second_priority_higher(op1: &Op, op2: &Op) -> bool {
    return operator_priority(op1) > operator_priority(op2);
}

fn is_second_priority_higher_or_equal(op1: &Op, op2: &Op) -> bool {
    return operator_priority(op1) >= operator_priority(op2);
}

#[test]
fn create_simple_unary() {
    let expr = Tokens {
        ops: vec![
            Op::Not,
            Op::Operand(Operand::Object(Object {
                name: "some_value".to_string(),
            })),
        ],
    };

    let expected_eval = Eval {
        expr: vec![
            Op::Not,
            Op::Operand(Operand::Object(Object {
                name: "some_value".to_string(),
            })),
        ],
    };

    assert_eq!(Eval::new(expr).unwrap(), expected_eval);
}

#[test]
fn create_multiple_unary_expr() {
    let expr = Tokens {
        ops: vec![
            Op::Not,
            Op::Not,
            Op::Not,
            Op::Operand(Operand::Object(Object {
                name: "some_value".to_string(),
            })),
        ],
    };

    let expected_eval = Eval {
        expr: vec![
            Op::Not,
            Op::Not,
            Op::Not,
            Op::Operand(Operand::Object(Object {
                name: "some_value".to_string(),
            })),
        ],
    };
    assert_eq!(Eval::new(expr).unwrap(), expected_eval);
}

#[test]
fn create_simple_binary_expr() {
    let expr = Tokens {
        ops: vec![
            Op::Operand(Operand::Object(Object {
                name: "some".to_string(),
            })),
            Op::Equal,
            Op::Operand(Operand::Number(3)),
        ],
    };

    let expected_eval = Eval {
        expr: vec![
            Op::Equal,
            Op::Operand(Operand::Object(Object {
                name: "some".to_string(),
            })),
            Op::Operand(Operand::Number(3)),
        ],
    };
    assert_eq!(Eval::new(expr).unwrap(), expected_eval);
}

#[test]
fn create_binary_with_unary_expr() {
    let expr = Tokens {
        ops: vec![
            Op::Operand(Operand::Object(Object {
                name: "some".to_string(),
            })),
            Op::Equal,
            Op::Not,
            Op::Not,
            Op::Operand(Operand::Number(3)),
        ],
    };

    let expected_eval = Eval {
        expr: vec![
            Op::Equal,
            Op::Operand(Operand::Object(Object {
                name: "some".to_string(),
            })),
            Op::Not,
            Op::Not,
            Op::Operand(Operand::Number(3)),
        ],
    };
    assert_eq!(Eval::new(expr).unwrap(), expected_eval);
}

#[test]
fn create_complex_expr() {
    let expr = Tokens {
        ops: vec![
            Op::Not,
            Op::Operand(Operand::Object(Object {
                name: "some_value".to_string(),
            })),
            Op::And,
            Op::ParenOpen,
            Op::Not,
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
    };

    let expected_eval = Eval {
        expr: vec![
            Op::And,
            Op::Not,
            Op::Operand(Operand::Object(Object {
                name: "some_value".to_string(),
            })),
            Op::Or,
            Op::Not,
            Op::NotEqual,
            Op::Operand(Operand::Object(Object {
                name: "var1".to_string(),
            })),
            Op::Operand(Operand::Object(Object {
                name: "var2".to_string(),
            })),
            Op::LessEq,
            Op::Operand(Operand::Object(Object {
                name: "some".to_string(),
            })),
            Op::Operand(Operand::Object(Object {
                name: "val".to_string(),
            })),
        ],
    };
    assert_eq!(Eval::new(expr).unwrap(), expected_eval);
}

#[test]
fn create_complex_expr2() {
    let expr = Tokens {
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
    };

    let expected_eval = Eval {
        expr: vec![
            Op::Or,
            Op::And,
            Op::GreaterEq,
            Op::Operand(Operand::Object(Object {
                name: "var1".to_string(),
            })),
            Op::Operand(Operand::Object(Object {
                name: "var2".to_string(),
            })),
            Op::LessEq,
            Op::Operand(Operand::Object(Object {
                name: "var2".to_string(),
            })),
            Op::Operand(Operand::Object(Object {
                name: "var3".to_string(),
            })),
            Op::Not,
            Op::Operand(Operand::Object(Object {
                name: "var3".to_string(),
            })),
        ],
    };
    assert_eq!(Eval::new(expr).unwrap(), expected_eval);
}

#[test]
fn check_assign_op() {
    let expr = Tokens {
        ops: vec![
            Op::Operand(Operand::Object(Object {
                name: "a".to_string(),
            })),
            Op::Assign,
            Op::Operand(Operand::Object(Object {
                name: "a".to_string(),
            })),
            Op::And,
            Op::Operand(Operand::Number(3)),
        ],
    };

    let expected_eval = Eval {
        expr: vec![
            Op::Assign,
            Op::Operand(Operand::Object(Object {
                name: "a".to_string(),
            })),
            Op::And,
            Op::Operand(Operand::Object(Object {
                name: "a".to_string(),
            })),
            Op::Operand(Operand::Number(3)),
        ],
    };
    assert_eq!(Eval::new(expr).unwrap(), expected_eval);
}

#[test]
fn check_multiple_assign() {
    let expr = Tokens {
        ops: vec![
            Op::Operand(Operand::Object(Object {
                name: "a".to_string(),
            })),
            Op::Assign,
            Op::Operand(Operand::Object(Object {
                name: "b".to_string(),
            })),
            Op::Assign,
            Op::Operand(Operand::Object(Object {
                name: "c".to_string(),
            })),
        ],
    };

    let expected_eval = Eval {
        expr: vec![
            Op::Assign,
            Op::Operand(Operand::Object(Object {
                name: "a".to_string(),
            })),
            Op::Assign,
            Op::Operand(Operand::Object(Object {
                name: "b".to_string(),
            })),
            Op::Operand(Operand::Object(Object {
                name: "c".to_string(),
            })),
        ],
    };
    assert_eq!(Eval::new(expr).unwrap(), expected_eval);
}
#[test]
fn arithmetic_expression() {
    let expr = Tokens {
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
            Op::Plus,
            Op::Operand(Operand::Number(1)),
            Op::Plus,
            Op::Operand(Operand::Number(2)),
        ],
    };

    let expected_eval = Eval {
        expr: vec![
            Op::Plus,
            Op::Plus,
            Op::Multiply,
            Op::Minus,
            Op::Plus,
            Op::Operand(Operand::Object(Object {
                name: "a".to_string(),
            })),
            Op::Multiply,
            Op::Operand(Operand::Object(Object {
                name: "b".to_string(),
            })),
            Op::Operand(Operand::Object(Object {
                name: "c".to_string(),
            })),
            Op::Divide,
            Op::Operand(Operand::Object(Object {
                name: "e".to_string(),
            })),
            Op::Operand(Operand::Object(Object {
                name: "d".to_string(),
            })),
            Op::Operand(Operand::Object(Object {
                name: "f".to_string(),
            })),
            Op::Operand(Operand::Number(1)),
            Op::Operand(Operand::Number(2)),
        ],
    };
    assert_eq!(Eval::new(expr).unwrap(), expected_eval);
}
