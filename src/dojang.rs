use crate::context::*;
use crate::exec::*;
use crate::expr::*;
use serde_json::Value;
use std::collections::HashMap;
use std::fs;
use std::io;
use std::path::PathBuf;

/// HTML template rendering engine that should be constructed for once.
pub struct Dojang {
    /// Mapping between the template file name and the renderer along with the file content.
    templates: HashMap<String, (Executer, String)>,
    functions: HashMap<String, FunctionContainer>,
}

impl Dojang {
    /// Creates a template engine.
    pub fn new() -> Self {
        Dojang {
            templates: HashMap::new(),
            functions: HashMap::new(),
        }
    }

    /// Adds a template file to the engine.
    ///
    /// If there is already an existing template with same name, this will return error.
    ///
    /// # Arguments
    ///
    /// * `file_name` - Name of the template file. Template datas are identified by this name.
    /// * `template` - Actual template data. Should be using EJS syntax.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut dojang = dojang::Dojang::new();
    ///
    /// // Constructs the template "tmpl" with the content "<%= 1 + 1 %>".
    /// dojang.add("tmpl".to_string(), "<%= 1 + 1 %>".to_string());
    /// ```
    pub fn add(&mut self, file_name: String, template: String) -> Result<&Self, String> {
        if self.templates.contains_key(&file_name) {
            return Err(format!("{} is already added as a template", file_name));
        }

        self.templates.insert(
            file_name,
            (Executer::new(Parser::parse(&template)?)?, template),
        );

        Ok(self)
    }

    /// Adds a function that can be used in the template.
    ///
    /// If there is already an existing function with same name, this will return error.
    ///
    /// # Arguments
    ///
    /// * `function_name` - Name of the function.
    /// * `function` - The body of the function. Function must be taking `serde_json::Value` as a
    /// parameters and return `serde_json::Value`. Also, the function must be one of enum values
    /// defined in `FunctionContainer`, which are categorized by the number of parameters.
    ///
    /// For example, if the function takes 2 params, it must be `FunctionContainer::F2`.
    ///
    /// # Examples
    ///
    /// ```
    /// use serde_json::Value;
    /// let mut dojang = dojang::Dojang::new();
    ///
    /// // Register a function that takes two numeric values and returns the sum of it.
    /// dojang.add_function("func".to_string(), dojang::FunctionContainer::F2(|a: Value, b: Value| -> Value {
    ///        Value::Number(serde_json::Number::from(
    ///            a.as_i64().unwrap() + b.as_i64().unwrap(),
    ///        ))
    ///    }));
    /// ```
    pub fn add_function(
        &mut self,
        function_name: String,
        function: FunctionContainer,
    ) -> Result<&Self, String> {
        if self.functions.contains_key(&function_name) {
            return Err(format!("{} is already added as a function", function_name));
        }

        self.functions.insert(function_name, function);
        Ok(self)
    }

    /// Load files under the provided directory as templates.
    ///
    /// Note that it does not recursively visit every underlying directories. Only the files that
    /// live in the current directory will be added to the engine.
    ///
    /// If the file is not readable, then it will be ignored (will show an error message)
    ///
    /// # Arguments
    ///
    /// * `dir_name` - Name of the directory.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut dojang = dojang::Dojang::new();
    ///
    /// // Add every files under ./tests as a template.
    /// dojang.load("./tests");
    /// ```
    pub fn load(&mut self, dir_name: &str) -> Result<&Self, String> {
        match get_all_file_path_under_dir(dir_name) {
            Ok(files) => {
                for file in files {
                    let file_name = file
                        .file_name()
                        .unwrap()
                        .to_os_string()
                        .into_string()
                        .unwrap();

                    if self.templates.contains_key(&file_name) {
                        println!("Template {} is already added", file_name);
                        continue;
                    }

                    let file_content = std::fs::read_to_string(&file);

                    if file_content.is_err() {
                        println!(
                            "Unable to read file '{:?}', error : {:?}",
                            file, file_content
                        );
                        continue;
                    }

                    let file_content = file_content.unwrap();
                    self.templates.insert(
                        file_name,
                        (Executer::new(Parser::parse(&file_content)?)?, file_content),
                    );
                }
            }
            Err(e) => return Err(e.to_string()),
        }

        Ok(self)
    }

    /// Render the page with the provided context.
    ///
    /// # Arguments
    ///
    /// * `file_name` : Name of the template file that should be rendered.
    /// * `value` : JSON value that is provided as a context. Note that this function consumes the
    /// json data.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut dojang = dojang::Dojang::new();
    ///
    /// // Render 'template_file' with the provided context.
    /// dojang.load("./tests").unwrap().render("template_file", serde_json::from_str(r#"{ "test" : { "title" : "Welcome to Dojang"} }"#).unwrap());
    /// ```
    pub fn render(&self, file_name: &str, value: Value) -> Result<String, String> {
        if let Some((executer, file_content)) = self.templates.get(&file_name.to_string()) {
            executer.render(&mut Context::new(value), &self.functions, file_content)
        } else {
            Err(format!("Template {} is not found", file_name))
        }
    }
}

fn get_all_file_path_under_dir(dir_name: &str) -> io::Result<Vec<PathBuf>> {
    fs::read_dir(dir_name)?
        .into_iter()
        .map(|x| x.map(|entry| entry.path()))
        .collect()
}

#[test]
fn render() {
    let template = "<% if a == 1 { %> Hi <% } else { %><%= a %><% } %>".to_string();
    let mut dojang = Dojang::new();
    assert!(dojang.add("some_template".to_string(), template).is_ok());

    assert_eq!(
        dojang
            .render(
                "some_template",
                serde_json::from_str(r#"{ "a" : 1 }"#).unwrap()
            )
            .unwrap(),
        " Hi "
    );

    assert_eq!(
        dojang
            .render(
                "some_template",
                serde_json::from_str(r#"{ "a" : 2 }"#).unwrap()
            )
            .unwrap(),
        "2"
    );
}

#[test]
fn render_from_dir() {
    let mut dojang = Dojang::new();
    assert!(dojang.load("./tests").is_ok());

    println!(
        "{}",
        dojang
            .render(
                "test.html",
                serde_json::from_str(r#"{ "test" : { "title" : "Welcome to Dojang"} }"#).unwrap()
            )
            .unwrap()
    );

    assert_eq!(
        dojang
            .render(
                "test.html",
                serde_json::from_str(r#"{ "test" : { "title" : "Welcome to Dojang"} }"#).unwrap()
            )
            .unwrap(),
        r#"<html>
  Welcome to Dojang
  <body>
    <p>some content</p><p>x is0</p><p>x is1</p><p>x is2</p><p>x is3</p><p>x is4</p><p>x is5</p><p>x is6</p><p>x is7</p><p>x is8</p><p>x is9</p>
  </body>
</html>
"#
    );
}
