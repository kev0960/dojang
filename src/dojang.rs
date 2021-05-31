use crate::context::*;
use crate::exec::*;
use crate::expr::*;
use serde_json::Value;
use std::collections::HashMap;

pub struct Dojang<'a> {
    templates: HashMap<String, Executer<'a>>,
}

impl<'a> Dojang<'a> {
    pub fn new() -> Self {
        Dojang {
            templates: HashMap::new(),
        }
    }

    pub fn add(&mut self, file_name: &str, file_content: &'a str) -> Result<(), String> {
        self.templates.insert(
            file_name.to_string(),
            Executer::new(Parser::parse(file_content)?)?,
        );

        Ok(())
    }

    pub fn render(&self, file_name: &str, value: Value) -> Result<String, String> {
        if let Some(executer) = self.templates.get(&file_name.to_string()) {
            executer.render(&mut Context::new(value))
        } else {
            Err(format!("Template {} is not found", file_name))
        }
    }
}
