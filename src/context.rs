use crate::eval::*;
use crate::expr::*;
use serde_json::{Map, Value};

#[derive(Debug)]
pub struct Context {
    pub context: Value,
}

impl Context {
    pub fn new(context: Value) -> Self {
        Context { context }
    }

    fn get_value(&self, name: &str) -> Result<&Value, String> {
        let names = name.split(".").collect::<Vec<&str>>();
        if names.is_empty() {
            return Err(format!("Mapping not exist : {}", name));
        }

        let mut value;
        match self.context.get(names.get(0).unwrap()) {
            Some(v) => {
                value = v;
            }
            _ => {
                return Err(format!("Mapping not exist {:?}", names));
            }
        }

        for n in names.iter().skip(1) {
            match value.get(n) {
                Some(v) => {
                    value = v;
                }
                _ => return Err(format!("Mapping not exist : {} at {}", name, n)),
            }
        }

        Ok(value)
    }

    fn get_nth_from_array(&self, name: &str, index: usize) -> Result<Option<&Value>, String> {
        let value = self.get_value(name)?;
        match value {
            Value::Array(arr) => Ok(arr.get(index)),
            _ => {
                return Err(format!(
                    "in only works on the array; You gave : {:?}",
                    value
                ))
            }
        }
    }

    fn set_value(&mut self, name: &str, operand: Operand) -> Result<(), String> {
        let names = name.split(".").collect::<Vec<&str>>();
        if names.is_empty() {
            return Err(format!("Mapping not exist : {}", name));
        }

        let mut value: &mut Value;
        match self.context.get_mut(names.get(0).unwrap()) {
            Some(v) => {
                value = v;
            }
            _ => {
                if names.len() > 1 {
                    return Err(format!(
                        "Local variable should not use dot operator. {:?}",
                        name
                    ));
                }

                if !self.context.is_object() {
                    self.context = Value::Object(Map::new());
                }

                self.context.as_object_mut().unwrap().insert(
                    names.get(0).unwrap().to_string(),
                    convert_operand_to_value(operand),
                );

                return Ok(());
            }
        }

        for n in names.iter().skip(1) {
            match value.get_mut(n) {
                Some(v) => {
                    value = v;
                }
                _ => return Err(format!("Mapping not exist : {} at {}", name, n)),
            }
        }

        *value = convert_operand_to_value(operand);
        Ok(())
    }
}

pub trait ComputeExpr<'a> {
    fn run(&self, context: &'a mut Context) -> Result<Operand, String>;
    fn run_for_loop(&self, context: &'a mut Context, for_index: usize) -> Result<bool, String>;
}

impl<'a> ComputeExpr<'a> for Eval {
    fn run(&self, context: &'a mut Context) -> Result<Operand, String> {
        let mut operands: Vec<Operand> = Vec::new();

        for op in self.expr.iter().rev() {
            match op {
                Op::Operand(operand) => {
                    operands.push(operand.clone());
                }
                optr => {
                    let num_operands = operator_num_operands(optr);
                    if operands.len() < num_operands {
                        return Err(format!(
                            "Number of operands for {:?} is less than {}",
                            optr, num_operands
                        ));
                    }

                    if num_operands == 1 {
                        let op = operands.pop().unwrap();
                        match optr.compute_unary(context, op) {
                            Ok(operand) => {
                                operands.push(operand);
                            }
                            Err(e) => return Err(e),
                        }
                    } else if num_operands == 2 {
                        // Since we are iterating from back, left is the top most operand.
                        let left = operands.pop().unwrap();
                        let right = operands.pop().unwrap();

                        match optr.compute_binary(context, left, right) {
                            Ok(operand) => {
                                operands.push(operand);
                            }
                            Err(e) => return Err(e),
                        }
                    }
                }
            }
        }

        if operands.len() != 1 {
            return Err(format!(
                "# of operands after computing is not zero. {:?}",
                operands
            ));
        }

        match operands.pop().unwrap() {
            Operand::Object(obj) => Ok(convert_value_to_operand(context.get_value(&obj.name)?)),
            operand => Ok(operand),
        }
    }

    // Returns true if the for loop's condition is true.
    fn run_for_loop(&self, context: &'a mut Context, for_index: usize) -> Result<bool, String> {
        if self.expr.len() != 3 {
            return Err(format!(
                "For loop must use 'for a in b' format, yours use {:?}",
                self.expr
            ));
        }

        let object_name;
        match self.expr.get(0).unwrap() {
            Op::Operand(Operand::Object(object)) => {
                object_name = &object.name;
            }
            _ => {
                return Err(format!(
                    "Range declaration in for loop must be an object; Yours : {:?}",
                    self.expr
                ))
            }
        }

        if self.expr.get(1).unwrap() != &Op::Operand(Operand::Keyword(Keyword::In)) {
            return Err(format!(
                "'in' is missing in your for-loop. Yours : {:?}",
                self.expr
            ));
        }

        let container_name;
        match self.expr.get(2).unwrap() {
            Op::Operand(Operand::Object(object)) => {
                container_name = &object.name;
            }
            _ => {
                return Err(format!(
                    "Container in for loop must be an object; Yours : {:?}",
                    self.expr
                ))
            }
        }

        match context.get_nth_from_array(&container_name, for_index)? {
            Some(element) => {
                let operand = convert_value_to_operand(element);
                context.set_value(object_name, operand)?;
                Ok(true)
            }
            _ => Ok(false),
        }
    }
}

pub trait Convert {
    fn is_true(&self) -> bool;
    fn to_str(&self) -> String;
}

impl Convert for Operand {
    fn is_true(&self) -> bool {
        match &self {
            Operand::Literal(l) => !l.is_empty(),
            Operand::Number(n) => *n != 0,
            Operand::Decimal(d) => *d != 0.,
            Operand::Array(arr) => !arr.is_empty(),
            _ => {
                panic!("Unconvertible object {:?}", &self)
            }
        }
    }

    fn to_str(&self) -> String {
        match &self {
            Operand::Literal(l) => l.to_string(),
            Operand::Number(n) => n.to_string(),
            Operand::Decimal(d) => d.to_string(),
            Operand::Array(arr) => format!("{:?}", arr),
            _ => {
                panic!("Unconvertible object {:?}", &self)
            }
        }
    }
}

trait ComputeOp {
    fn compute_binary<'a>(
        &self,
        context: &'a mut Context,
        left: Operand,
        right: Operand,
    ) -> Result<Operand, String>;

    fn compute_unary<'a>(&self, context: &'a Context, op: Operand) -> Result<Operand, String>;
}

impl ComputeOp for Op {
    fn compute_binary<'a>(
        &self,
        context: &'a mut Context,
        left: Operand,
        right: Operand,
    ) -> Result<Operand, String> {
        match self {
            Op::And => return compute_binary(context, left, right, compute_and),
            Op::Or => return compute_binary(context, left, right, compute_or),
            Op::Equal => return compute_binary(context, left, right, compute_eq),
            Op::NotEqual => return compute_binary(context, left, right, compute_neq),
            Op::Greater => return compute_binary(context, left, right, compute_greater),
            Op::GreaterEq => return compute_binary(context, left, right, compute_greater_eq),
            Op::Less => return compute_binary(context, left, right, compute_less),
            Op::LessEq => return compute_binary(context, left, right, compute_less_eq),
            Op::Assign => return compute_simple_assign(context, left, right),
            Op::Plus => return compute_binary(context, left, right, compute_add),
            Op::Minus => return compute_binary(context, left, right, compute_minus),
            Op::Multiply => return compute_binary(context, left, right, compute_multiply),
            Op::Divide => return compute_binary(context, left, right, compute_divide),
            _ => {}
        }

        panic!("Binary {:?} is not implemented", self);
    }

    fn compute_unary<'a>(&self, context: &'a Context, op: Operand) -> Result<Operand, String> {
        match self {
            Op::Not => return compute_unary(context, op, compute_not),
            _ => {}
        }

        panic!("Unary {:?} is not implemented", self);
    }
}

fn convert_value_to_operand(value: &Value) -> Operand {
    match value {
        Value::Bool(b) => Operand::Number(*b as i64),
        Value::Number(n) => {
            if n.is_i64() {
                Operand::Number(n.as_i64().unwrap())
            } else {
                Operand::Decimal(n.as_f64().unwrap())
            }
        }
        Value::String(s) => Operand::Literal(s.clone()),
        Value::Array(arr) => {
            let mut vec = Vec::new();
            for elem in arr {
                vec.push(convert_value_to_operand(&elem))
            }

            Operand::Array(vec)
        }
        _ => {
            panic!("This should not happen")
        }
    }
}

fn convert_operand_to_value(operand: Operand) -> Value {
    match operand {
        Operand::Number(n) => Value::from(n),
        Operand::Decimal(d) => Value::from(d),
        Operand::Literal(l) => Value::from(l),
        Operand::Array(arr) => {
            let mut vec = Vec::new();
            for elem in arr {
                vec.push(convert_operand_to_value(elem));
            }
            Value::from(vec)
        }
        _ => {
            panic!("Unable to convert object to value.")
        }
    }
}

fn compute_unary<'a, ComputeFunc>(
    context: &'a Context,
    op: Operand,
    compute_func: ComputeFunc,
) -> Result<Operand, String>
where
    ComputeFunc: Fn(Operand) -> Result<Operand, String>,
{
    if let Operand::Object(obj) = op {
        match context.get_value(&obj.name) {
            Ok(v) => {
                return compute_unary(context, convert_value_to_operand(v), compute_func);
            }
            Err(e) => {
                return Err(e);
            }
        }
    }

    compute_func(op)
}

fn compute_binary<ComputeFunc>(
    context: &Context,
    left: Operand,
    right: Operand,
    compute_func: ComputeFunc,
) -> Result<Operand, String>
where
    ComputeFunc: Fn(Operand, Operand) -> Result<Operand, String>,
{
    if let Operand::Object(l) = left {
        match context.get_value(&l.name) {
            Ok(v) => {
                return compute_binary(context, convert_value_to_operand(v), right, compute_func);
            }
            Err(e) => {
                return Err(e);
            }
        }
    }

    if let Operand::Object(r) = right {
        match context.get_value(&r.name) {
            Ok(v) => {
                return compute_func(left, convert_value_to_operand(v));
            }
            Err(e) => {
                return Err(e);
            }
        }
    }

    compute_func(left, right)
}

fn compute_simple_assign(
    context: &mut Context,
    left: Operand,
    right: Operand,
) -> Result<Operand, String> {
    if let Operand::Object(ref object) = left {
        match right {
            Operand::Object(right_obj) => {
                context.set_value(
                    &object.name,
                    convert_value_to_operand(context.get_value(&right_obj.name)?),
                )?;
            }
            _ => {
                context.set_value(&object.name, right)?;
            }
        }
        Ok(left)
    } else {
        return Err(format!("Cannot assign to non-object {:?}", left));
    }
}

/*
fn compute_binary_assign<ComputeFunc>(
    context: &mut Context,
    left: Operand,
    right: Operand,
    compute_func: ComputeFunc,
) -> Result<Operand, String>
where
    ComputeFunc: Fn(Operand, Operand) -> Result<Operand, String>,
{
    if let Operand::Object(ref object) = left {
        match right {
            Operand::Object(right_obj) => {
                context.set_value(
                    &object.name,
                    compute_func(
                        convert_value_to_operand(context.get_value(&object.name)?),
                        convert_value_to_operand(context.get_value(&right_obj.name)?),
                    )?,
                )?;
            }
            _ => {
                context.set_value(
                    &object.name,
                    compute_func(
                        convert_value_to_operand(context.get_value(&object.name)?),
                        right,
                    )?,
                )?;
            }
        }
        Ok(left)
    } else {
        return Err(format!("Cannot assign to non-object {:?}", left));
    }
}
*/

fn compute_and(left: Operand, right: Operand) -> Result<Operand, String> {
    match (&left, &right) {
        (Operand::Literal(l), Operand::Literal(r)) => {
            Ok(Operand::Number(((l.len() != 0) && (r.len() != 0)) as i64))
        }
        (Operand::Number(l), Operand::Number(r)) => {
            Ok(Operand::Number(((l != &0) && (r != &0)) as i64))
        }
        (Operand::Decimal(l), Operand::Decimal(r)) => {
            Ok(Operand::Number(((l != &0.) && (r != &0.)) as i64))
        }
        _ => Err(format!("Invalid operation between {:?} {:?}", left, right)),
    }
}

fn compute_or(left: Operand, right: Operand) -> Result<Operand, String> {
    match (&left, &right) {
        (Operand::Literal(l), Operand::Literal(r)) => {
            Ok(Operand::Number(((l.len() != 0) || (r.len() != 0)) as i64))
        }
        (Operand::Number(l), Operand::Number(r)) => {
            Ok(Operand::Number(((l != &0) || (r != &0)) as i64))
        }
        (Operand::Decimal(l), Operand::Decimal(r)) => {
            Ok(Operand::Number(((l != &0.) || (r != &0.)) as i64))
        }
        _ => Err(format!("Invalid operation between {:?} {:?}", left, right)),
    }
}

fn compute_greater(left: Operand, right: Operand) -> Result<Operand, String> {
    match (&left, &right) {
        (Operand::Literal(l), Operand::Literal(r)) => Ok(Operand::Number((l > r) as i64)),
        (Operand::Number(l), Operand::Number(r)) => Ok(Operand::Number((l > r) as i64)),
        (Operand::Decimal(l), Operand::Decimal(r)) => Ok(Operand::Number((l > r) as i64)),
        _ => Err(format!("Invalid operation between {:?} {:?}", left, right)),
    }
}

fn compute_greater_eq(left: Operand, right: Operand) -> Result<Operand, String> {
    match (&left, &right) {
        (Operand::Literal(l), Operand::Literal(r)) => Ok(Operand::Number((l >= r) as i64)),
        (Operand::Number(l), Operand::Number(r)) => Ok(Operand::Number((l >= r) as i64)),
        (Operand::Decimal(l), Operand::Decimal(r)) => Ok(Operand::Number((l >= r) as i64)),
        _ => Err(format!("Invalid operation between {:?} {:?}", left, right)),
    }
}

fn compute_less(left: Operand, right: Operand) -> Result<Operand, String> {
    match (&left, &right) {
        (Operand::Literal(l), Operand::Literal(r)) => Ok(Operand::Number((l < r) as i64)),
        (Operand::Number(l), Operand::Number(r)) => Ok(Operand::Number((l < r) as i64)),
        (Operand::Decimal(l), Operand::Decimal(r)) => Ok(Operand::Number((l < r) as i64)),
        _ => Err(format!("Invalid operation between {:?} {:?}", left, right)),
    }
}

fn compute_less_eq(left: Operand, right: Operand) -> Result<Operand, String> {
    match (&left, &right) {
        (Operand::Literal(l), Operand::Literal(r)) => Ok(Operand::Number((l <= r) as i64)),
        (Operand::Number(l), Operand::Number(r)) => Ok(Operand::Number((l <= r) as i64)),
        (Operand::Decimal(l), Operand::Decimal(r)) => Ok(Operand::Number((l <= r) as i64)),
        _ => Err(format!("Invalid operation between {:?} {:?}", left, right)),
    }
}

fn compute_eq(left: Operand, right: Operand) -> Result<Operand, String> {
    match (&left, &right) {
        (Operand::Literal(l), Operand::Literal(r)) => Ok(Operand::Number((l == r) as i64)),
        (Operand::Number(l), Operand::Number(r)) => Ok(Operand::Number((l == r) as i64)),
        (Operand::Decimal(l), Operand::Decimal(r)) => Ok(Operand::Number((l == r) as i64)),
        _ => Err(format!("Invalid operation between {:?} {:?}", left, right)),
    }
}

fn compute_neq(left: Operand, right: Operand) -> Result<Operand, String> {
    match (&left, &right) {
        (Operand::Literal(l), Operand::Literal(r)) => Ok(Operand::Number((l != r) as i64)),
        (Operand::Number(l), Operand::Number(r)) => Ok(Operand::Number((l != r) as i64)),
        (Operand::Decimal(l), Operand::Decimal(r)) => Ok(Operand::Number((l != r) as i64)),
        _ => Err(format!("Invalid operation between {:?} {:?}", left, right)),
    }
}

fn compute_add(left: Operand, right: Operand) -> Result<Operand, String> {
    match (left, right) {
        (Operand::Literal(mut l), Operand::Literal(r)) => {
            l.push_str(&r);
            Ok(Operand::Literal(l))
        }
        (Operand::Number(l), Operand::Number(r)) => Ok(Operand::Number(l + r)),
        (Operand::Decimal(l), Operand::Decimal(r)) => Ok(Operand::Decimal(l + r)),
        (left, right) => Err(format!("Invalid operation between {:?} {:?}", left, right)),
    }
}

fn compute_minus(left: Operand, right: Operand) -> Result<Operand, String> {
    match (left, right) {
        (Operand::Literal(l), Operand::Literal(r)) => {
            Err(format!("Cannot use '-' between strings {:?} {:?}", l, r))
        }
        (Operand::Number(l), Operand::Number(r)) => Ok(Operand::Number(l - r)),
        (Operand::Decimal(l), Operand::Decimal(r)) => Ok(Operand::Decimal(l - r)),
        (left, right) => Err(format!("Invalid operation between {:?} {:?}", left, right)),
    }
}

fn compute_multiply(left: Operand, right: Operand) -> Result<Operand, String> {
    match (left, right) {
        (Operand::Literal(l), Operand::Literal(r)) => {
            Err(format!("Cannot use '*' between strings {:?} {:?}", l, r))
        }
        (Operand::Number(l), Operand::Number(r)) => Ok(Operand::Number(l * r)),
        (Operand::Decimal(l), Operand::Decimal(r)) => Ok(Operand::Decimal(l * r)),
        (left, right) => Err(format!("Invalid operation between {:?} {:?}", left, right)),
    }
}

fn compute_divide(left: Operand, right: Operand) -> Result<Operand, String> {
    match (left, right) {
        (Operand::Literal(l), Operand::Literal(r)) => {
            Err(format!("Cannot use '/' between strings {:?} {:?}", l, r))
        }
        (Operand::Number(l), Operand::Number(r)) => Ok(Operand::Number(l / r)),
        (Operand::Decimal(l), Operand::Decimal(r)) => Ok(Operand::Decimal(l / r)),
        (left, right) => Err(format!("Invalid operation between {:?} {:?}", left, right)),
    }
}

fn compute_not(operand: Operand) -> Result<Operand, String> {
    match &operand {
        Operand::Literal(s) => Ok(Operand::Number((s.len() == 0) as i64)),
        Operand::Number(n) => Ok(Operand::Number((n == &0) as i64)),
        Operand::Decimal(d) => Ok(Operand::Number((d == &0.) as i64)),
        _ => Err(format!("Invalid operation NOT {:?}", operand)),
    }
}

#[cfg(test)]
fn get_expr<'a>(s: &'a str) -> Expr {
    let mut res = Parser::parse(s).unwrap();
    match res.parse_tree.pop().unwrap() {
        Action::Do(expr) => expr,
        _ => panic!("No expr found"),
    }
}

#[test]
fn compute_and_test() {
    let context_json = r#"{"a": 1, "b":0, "c":"abc", "d":"", "e": "def"}"#;
    let context_value: Value = serde_json::from_str(context_json).unwrap();
    let mut context = Context::new(context_value);

    {
        let eval = Eval::new(get_expr(r"<% a && b %>")).unwrap();
        let result = eval.run(&mut context);

        assert_eq!(result.unwrap(), Operand::Number(0));
    }
    {
        let eval = Eval::new(get_expr(r"<% c && d %>")).unwrap();
        let result = eval.run(&mut context);

        assert_eq!(result.unwrap(), Operand::Number(0));
    }
    {
        let eval = Eval::new(get_expr(r"<% c && e %>")).unwrap();
        let result = eval.run(&mut context);

        assert_eq!(result.unwrap(), Operand::Number(1));
    }
}

#[test]
fn compute_or_test() {
    let context_json = r#"{"a": 1, "b":0, "c":"abc", "d":"", "e": "def"}"#;
    let context_value: Value = serde_json::from_str(context_json).unwrap();
    let mut context = Context::new(context_value);

    {
        let eval = Eval::new(get_expr(r"<% (a && b) || (c && e) %>")).unwrap();
        let result = eval.run(&mut context);

        assert_eq!(result.unwrap(), Operand::Number(1));
    }
    {
        let eval = Eval::new(get_expr(r"<% (a && b) || (c && d) %>")).unwrap();
        let result = eval.run(&mut context);

        assert_eq!(result.unwrap(), Operand::Number(0));
    }
    {
        let eval = Eval::new(get_expr(r"<% c || e %>")).unwrap();
        let result = eval.run(&mut context);

        assert_eq!(result.unwrap(), Operand::Number(1));
    }
}

#[test]
fn compute_complex() {
    let context_json = r#"{"a": 1, "b":0, "c":"abc", "d":"", "e": "def"}"#;
    let context_value: Value = serde_json::from_str(context_json).unwrap();
    let mut context = Context::new(context_value);

    {
        let eval = Eval::new(get_expr(r"<% !a && ((b != a) || c <= e) %>")).unwrap();
        let result = eval.run(&mut context);

        assert_eq!(result.unwrap(), Operand::Number(0));
    }
    {
        let eval = Eval::new(get_expr(r"<% !b && ((b != a) || c <= e && !d) %>")).unwrap();
        let result = eval.run(&mut context);

        assert_eq!(result.unwrap(), Operand::Number(1));
    }
    {
        let eval = Eval::new(get_expr(
            r#"<% (a == 1) && (b == 0) && (c == "abc") && !d && e == "def" %>"#,
        ))
        .unwrap();
        let result = eval.run(&mut context);

        assert_eq!(result.unwrap(), Operand::Number(1));
    }
}

#[test]
fn compute_complex_object_name() {
    let context_json = r#"{"a": {"b" : 2, "c" : {"d" : 3 }}, "b" : 1}"#;
    let context_value: Value = serde_json::from_str(context_json).unwrap();
    let mut context = Context::new(context_value);

    {
        let eval = Eval::new(get_expr(r"<% a.b %>")).unwrap();
        let result = eval.run(&mut context);

        assert_eq!(result.unwrap(), Operand::Number(2));
    }
    {
        let eval = Eval::new(get_expr(r"<% a.c.d %>")).unwrap();
        let result = eval.run(&mut context);

        assert_eq!(result.unwrap(), Operand::Number(3));
    }
    {
        let eval = Eval::new(get_expr(r#"<% b %>"#)).unwrap();
        let result = eval.run(&mut context);

        assert_eq!(result.unwrap(), Operand::Number(1));
    }
}

#[test]
fn compute_assign_test() {
    let context_json = r#"{"a": 1, "b":0, "c": 1}"#;
    {
        let context_value: Value = serde_json::from_str(context_json).unwrap();
        let mut context = Context::new(context_value);

        let eval = Eval::new(get_expr(r"<% a = a && b %>")).unwrap();
        let result = eval.run(&mut context);

        assert_eq!(result.unwrap(), Operand::Number(0));
        assert_eq!(context.context.get("a").unwrap().as_i64().unwrap(), 0);
    }
    {
        let context_value: Value = serde_json::from_str(context_json).unwrap();
        let mut context = Context::new(context_value);

        let eval = Eval::new(get_expr(r"<% a = a && c %>")).unwrap();
        let result = eval.run(&mut context);

        assert_eq!(result.unwrap(), Operand::Number(1));
        assert_eq!(context.context.get("a").unwrap().as_i64().unwrap(), 1);
    }
    {
        let context_value: Value = serde_json::from_str(context_json).unwrap();
        let mut context = Context::new(context_value);

        let eval = Eval::new(get_expr(r"<% d = a && c %>")).unwrap();
        let result = eval.run(&mut context);

        assert_eq!(result.unwrap(), Operand::Number(1));
        assert_eq!(context.context.get("d").unwrap().as_i64().unwrap(), 1);
    }
}

#[test]
fn compute_arithmetic() {
    let context_json = r#"{"a": 1, "b":2, "c": 3, "d" : 2, "e" : 6, "f" : 2}"#;
    {
        let context_value: Value = serde_json::from_str(context_json).unwrap();
        let mut context = Context::new(context_value);

        // (1 + 2 * 3 - 6 / 2) * 2
        let eval = Eval::new(get_expr(r"<% b = a = (a + b * c - e / d) * f %>")).unwrap();
        let result = eval.run(&mut context);

        assert_eq!(result.unwrap(), Operand::Number(8));
        assert_eq!(context.context.get("a").unwrap().as_i64().unwrap(), 8);
        assert_eq!(context.context.get("b").unwrap().as_i64().unwrap(), 8);
    }
}
