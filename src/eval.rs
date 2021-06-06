use crate::expr::*;
#[cfg(test)]
use serde_json::Value;
use std::collections::HashMap;

// Evaluate the parsed expression.
#[derive(PartialEq, Debug)]
pub struct Eval {
    pub expr: Vec<Expr>,
}

#[derive(PartialEq, Debug)]
pub enum Expr {
    Op(Op),
    Function(Function),
}

#[derive(PartialEq, Debug)]
pub struct Function {
    pub name: String,
    pub params: Vec<Eval>,
}

impl Eval {
    pub fn new(mut expr: Tokens) -> Result<Eval, String> {
        let mut operands: Vec<Vec<Expr>> = Vec::new();
        let mut operators = Vec::new();

        // Wrap the expression with ().
        expr.ops.push(Op::ParenClose);
        expr.ops.insert(0, Op::ParenOpen);

        // Convert function calls into Operand::Function.
        // The correspoding Expr::Function object will be stored at the map.
        let mut function_name_to_function = HashMap::new();
        Eval::handle_functions(&mut expr, &mut function_name_to_function)?;

        // We have to scan from the back.
        expr.ops.reverse();
        while !expr.ops.is_empty() {
            let op = expr.ops.pop().unwrap();

            match op {
                Op::Operand(operand) => match operand {
                    Operand::Function(function_name) => {
                        let function = function_name_to_function.remove(&function_name);
                        if function.is_none() {
                            return Err(format!(
                                "Function {:?} does not have matching entry",
                                function_name
                            ));
                        }

                        operands.push(vec![Expr::Function(function.unwrap())]);
                    }
                    _ => {
                        operands.push(vec![Expr::Op(Op::Operand(operand))]);
                    }
                },
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

                        let mut popped_operands: Vec<Vec<Expr>> = Vec::new();
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

                        popped_operands.push(vec![Expr::Op(top_optr)]);
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

    fn handle_functions(
        expr: &mut Tokens,
        function_name_to_function: &mut HashMap<String, Function>,
    ) -> Result<(), String> {
        let mut inst_index = 0;
        while inst_index < expr.ops.len() {
            match expr.ops.get(inst_index).unwrap() {
                Op::Operand(operand) => match operand {
                    Operand::Object(_) => match expr.ops.get(inst_index + 1) {
                        Some(Op::ParenOpen) => {
                            // Then this is the start of the function.
                            let function_tokens =
                                get_tokens_belong_to_function(&mut expr.ops, inst_index)?;
                            println!("Func tokens :{:?}", function_tokens);
                            let function = handle_function_tokens(function_tokens)?;
                            println!("function {:?}", function);

                            // Now insert the Operand::Function as a placeholder.
                            expr.ops.insert(
                                inst_index,
                                Op::Operand(Operand::Function(function.name.clone())),
                            );

                            // Finally, register this function. Operator::Function will be later
                            // replaced by the Expr::Function.
                            function_name_to_function.insert(function.name.clone(), function);
                        }
                        _ => {}
                    },
                    _ => {}
                },
                _ => {}
            }

            inst_index += 1;
        }
        Ok(())
    }

    pub fn is_empty(&self) -> bool {
        self.expr.is_empty()
    }

    pub fn get_keyword(&self) -> Option<Keyword> {
        if self.expr.len() != 1 {
            return None;
        }

        match self.expr.get(0).unwrap() {
            Expr::Op(op) => match op {
                Op::Operand(operand) => match operand {
                    Operand::Keyword(keyword) => Some(keyword.clone()),
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        }
    }
}

fn get_tokens_belong_to_function(
    ops: &mut Vec<Op>,
    mut inst_index: usize,
) -> Result<Vec<Op>, String> {
    let function_start = inst_index;

    inst_index += 2;

    let mut opened_paren = 1;

    while inst_index < ops.len() {
        match ops.get(inst_index).unwrap() {
            Op::ParenOpen => {
                opened_paren += 1;
            }
            Op::ParenClose => {
                opened_paren -= 1;
                if opened_paren == 0 {
                    break;
                }
            }
            _ => {}
        }

        inst_index += 1;
    }

    if opened_paren != 0 {
        return Err(format!("Function does not have closing ): {:?}", ops));
    }

    Ok(ops.drain(function_start..inst_index + 1).collect())
}

fn handle_function_tokens(mut ops: Vec<Op>) -> Result<Function, String> {
    // Should be at least function_name, (, ).
    assert!(ops.len() >= 3);

    let function_name = match ops.get(0).unwrap() {
        Op::Operand(operand) => match operand {
            Operand::Object(object) => object.name.clone(),
            _ => panic!("Function name is not object."),
        },
        _ => panic!("Function name is not proper operator."),
    };

    let mut inst_index = 0;
    let mut opened_paren = 0;
    let mut params = Vec::new();

    // Remove function name and first (.
    ops.drain(0..2);

    while inst_index < ops.len() {
        match ops.get(inst_index).unwrap() {
            Op::ParenOpen => {
                opened_paren += 1;
            }
            Op::ParenClose => {
                opened_paren -= 1;
            }
            Op::Comma => {
                if opened_paren == 0 {
                    let tokens = Tokens {
                        ops: ops.drain(0..inst_index).collect(),
                    };

                    params.push(Eval::new(tokens)?);
                    inst_index = 0;

                    // Remove comma.
                    ops.drain(0..1);

                    continue;
                }
            }
            _ => {}
        }

        inst_index += 1;
    }

    let last_param: Vec<Op> = ops.drain(0..ops.len() - 1).collect();
    if !last_param.is_empty() {
        let tokens = Tokens { ops: last_param };

        params.push(Eval::new(tokens)?);
    }

    Ok(Function {
        name: function_name,
        params,
    })
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
            Expr::Op(Op::Not),
            Expr::Op(Op::Operand(Operand::Object(Object {
                name: "some_value".to_string(),
            }))),
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
            Expr::Op(Op::Not),
            Expr::Op(Op::Not),
            Expr::Op(Op::Not),
            Expr::Op(Op::Operand(Operand::Object(Object {
                name: "some_value".to_string(),
            }))),
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
            Op::Operand(Operand::Value(Value::from(3))),
        ],
    };

    let expected_eval = Eval {
        expr: vec![
            Expr::Op(Op::Equal),
            Expr::Op(Op::Operand(Operand::Object(Object {
                name: "some".to_string(),
            }))),
            Expr::Op(Op::Operand(Operand::Value(Value::from(3)))),
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
            Op::Operand(Operand::Value(Value::from(3))),
        ],
    };

    let expected_eval = Eval {
        expr: vec![
            Expr::Op(Op::Equal),
            Expr::Op(Op::Operand(Operand::Object(Object {
                name: "some".to_string(),
            }))),
            Expr::Op(Op::Not),
            Expr::Op(Op::Not),
            Expr::Op(Op::Operand(Operand::Value(Value::from(3)))),
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
            Expr::Op(Op::And),
            Expr::Op(Op::Not),
            Expr::Op(Op::Operand(Operand::Object(Object {
                name: "some_value".to_string(),
            }))),
            Expr::Op(Op::Or),
            Expr::Op(Op::Not),
            Expr::Op(Op::NotEqual),
            Expr::Op(Op::Operand(Operand::Object(Object {
                name: "var1".to_string(),
            }))),
            Expr::Op(Op::Operand(Operand::Object(Object {
                name: "var2".to_string(),
            }))),
            Expr::Op(Op::LessEq),
            Expr::Op(Op::Operand(Operand::Object(Object {
                name: "some".to_string(),
            }))),
            Expr::Op(Op::Operand(Operand::Object(Object {
                name: "val".to_string(),
            }))),
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
            Expr::Op(Op::Or),
            Expr::Op(Op::And),
            Expr::Op(Op::GreaterEq),
            Expr::Op(Op::Operand(Operand::Object(Object {
                name: "var1".to_string(),
            }))),
            Expr::Op(Op::Operand(Operand::Object(Object {
                name: "var2".to_string(),
            }))),
            Expr::Op(Op::LessEq),
            Expr::Op(Op::Operand(Operand::Object(Object {
                name: "var2".to_string(),
            }))),
            Expr::Op(Op::Operand(Operand::Object(Object {
                name: "var3".to_string(),
            }))),
            Expr::Op(Op::Not),
            Expr::Op(Op::Operand(Operand::Object(Object {
                name: "var3".to_string(),
            }))),
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
            Op::Operand(Operand::Value(Value::from(3))),
        ],
    };

    let expected_eval = Eval {
        expr: vec![
            Expr::Op(Op::Assign),
            Expr::Op(Op::Operand(Operand::Object(Object {
                name: "a".to_string(),
            }))),
            Expr::Op(Op::And),
            Expr::Op(Op::Operand(Operand::Object(Object {
                name: "a".to_string(),
            }))),
            Expr::Op(Op::Operand(Operand::Value(Value::from(3)))),
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
            Expr::Op(Op::Assign),
            Expr::Op(Op::Operand(Operand::Object(Object {
                name: "a".to_string(),
            }))),
            Expr::Op(Op::Assign),
            Expr::Op(Op::Operand(Operand::Object(Object {
                name: "b".to_string(),
            }))),
            Expr::Op(Op::Operand(Operand::Object(Object {
                name: "c".to_string(),
            }))),
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
            Op::Operand(Operand::Value(Value::from(1))),
            Op::Plus,
            Op::Operand(Operand::Value(Value::from(2))),
        ],
    };

    let expected_eval = Eval {
        expr: vec![
            Expr::Op(Op::Plus),
            Expr::Op(Op::Plus),
            Expr::Op(Op::Multiply),
            Expr::Op(Op::Minus),
            Expr::Op(Op::Plus),
            Expr::Op(Op::Operand(Operand::Object(Object {
                name: "a".to_string(),
            }))),
            Expr::Op(Op::Multiply),
            Expr::Op(Op::Operand(Operand::Object(Object {
                name: "b".to_string(),
            }))),
            Expr::Op(Op::Operand(Operand::Object(Object {
                name: "c".to_string(),
            }))),
            Expr::Op(Op::Divide),
            Expr::Op(Op::Operand(Operand::Object(Object {
                name: "e".to_string(),
            }))),
            Expr::Op(Op::Operand(Operand::Object(Object {
                name: "d".to_string(),
            }))),
            Expr::Op(Op::Operand(Operand::Object(Object {
                name: "f".to_string(),
            }))),
            Expr::Op(Op::Operand(Operand::Value(Value::from(1)))),
            Expr::Op(Op::Operand(Operand::Value(Value::from(2)))),
        ],
    };
    assert_eq!(Eval::new(expr).unwrap(), expected_eval);
}

#[test]
fn function_expr() {
    let expr = Tokens {
        ops: vec![
            Op::Operand(Operand::Object(Object {
                name: "func".to_string(),
            })),
            Op::ParenOpen,
            Op::Operand(Operand::Value(Value::from(1))),
            Op::Plus,
            Op::Operand(Operand::Value(Value::from(1))),
            Op::Comma,
            Op::Operand(Operand::Object(Object {
                name: "a".to_string(),
            })),
            Op::Comma,
            Op::Operand(Operand::Object(Object {
                name: "b".to_string(),
            })),
            Op::ParenClose,
            Op::Plus,
            Op::Operand(Operand::Object(Object {
                name: "x".to_string(),
            })),
        ],
    };

    let expected_eval = Eval {
        expr: vec![
            Expr::Op(Op::Plus),
            Expr::Function(Function {
                name: "func".to_string(),
                params: vec![
                    Eval {
                        expr: vec![
                            Expr::Op(Op::Plus),
                            Expr::Op(Op::Operand(Operand::Value(Value::from(1)))),
                            Expr::Op(Op::Operand(Operand::Value(Value::from(1)))),
                        ],
                    },
                    Eval {
                        expr: vec![Expr::Op(Op::Operand(Operand::Object(Object {
                            name: "a".to_string(),
                        })))],
                    },
                    Eval {
                        expr: vec![Expr::Op(Op::Operand(Operand::Object(Object {
                            name: "b".to_string(),
                        })))],
                    },
                ],
            }),
            Expr::Op(Op::Operand(Operand::Object(Object {
                name: "x".to_string(),
            }))),
        ],
    };
    assert_eq!(Eval::new(expr).unwrap(), expected_eval);
}
