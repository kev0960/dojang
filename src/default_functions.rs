use crate::expr::Operand;
use serde_json::Value;

pub fn val_length(op: Operand) -> Operand {
    match op {
        Operand::Value(val) => {
            if val.is_string() {
                return Operand::Value(Value::from(val.as_str().unwrap().len()));
            } else if val.is_array() {
                return Operand::Value(Value::from(val.as_array().unwrap().len()));
            } else {
                return Operand::Value(Value::from(0));
            }
        }
        Operand::Array(arr) => {
            return Operand::Value(Value::from(arr.len()));
        }
        _ => return Operand::Value(Value::from(0)),
    }
}

pub fn val_range(op: Operand) -> Operand {
    match op {
        Operand::Value(val) => {
            if val.is_i64() {
                return Operand::Value(Value::from(
                    (0..val.as_i64().unwrap()).collect::<Vec<i64>>(),
                ));
            }
        }
        _ => {}
    }

    return Operand::Value(Value::from(Vec::<i64>::new()));
}
