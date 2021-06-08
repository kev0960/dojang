use crate::context::*;
use crate::exec::*;
use crate::expr::*;
use serde_json::Value;
use std::collections::HashMap;
use std::fs;
use std::io;
use std::path::PathBuf;

/// HTML template rendering engine that should be constructed for once.
pub struct Dojang<'a> {
    /// Mapping between the template file name and the renderer along with the file content.
    templates: HashMap<String, (Executer, String)>,
    functions: HashMap<String, FunctionContainer<'a>>,
}

impl<'a> Dojang<'a> {
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
    /// Use the appropriate function based on the number of parameters that the function take.
    /// (e.g for functions taking 2 params, use add_function_2). Functions with 4 params are
    /// supported at max.
    ///
    /// Note that the parameter of the function must be convertible to Value. Supported types are
    /// String, i64, f64 and boolean.
    ///
    /// # Arguments
    ///
    /// * `function_name` - Name of the function.
    /// * `function` - The body of the function.
    ///
    /// # Examples
    ///
    /// ```
    /// use serde_json::Value;
    /// use dojang::dojang::Dojang;
    ///
    /// fn func(a: i64) -> i64 { a + 1 }
    ///
    /// let mut dj = Dojang::new();
    ///
    /// dj.add_function_1("func".to_string(), &func);
    /// dj.add_function_2("func2".to_string(), &|a: i64, b: i64| -> i64 { a + b });
    /// ```

    pub fn add_function_1<T, V>(
        &mut self,
        function_name: String,
        function: &'a (dyn Fn(T) -> V + Send + Sync),
    ) -> Result<&Self, String>
    where
        T: From<Operand>,
        V: Into<Operand>,
    {
        if self.functions.contains_key(&function_name) {
            return Err(format!("{} is already added as a function", function_name));
        }

        self.functions
            .insert(function_name, to_function_container1(function));
        Ok(self)
    }

    pub fn add_function_2<T1, T2, V>(
        &mut self,
        function_name: String,
        function: &'a (dyn Fn(T1, T2) -> V + Send + Sync),
    ) -> Result<&Self, String>
    where
        T1: From<Operand>,
        T2: From<Operand>,
        V: Into<Operand>,
    {
        if self.functions.contains_key(&function_name) {
            return Err(format!("{} is already added as a function", function_name));
        }

        self.functions
            .insert(function_name, to_function_container2(function));
        Ok(self)
    }

    pub fn add_function_3<T1, T2, T3, V>(
        &mut self,
        function_name: String,
        function: &'a (dyn Fn(T1, T2, T3) -> V + Send + Sync),
    ) -> Result<&Self, String>
    where
        T1: From<Operand>,
        T2: From<Operand>,
        T3: From<Operand>,
        V: Into<Operand>,
    {
        if self.functions.contains_key(&function_name) {
            return Err(format!("{} is already added as a function", function_name));
        }

        self.functions
            .insert(function_name, to_function_container3(function));
        Ok(self)
    }

    pub fn add_function_4<T1, T2, T3, T4, V>(
        &mut self,
        function_name: String,
        function: &'a (dyn Fn(T1, T2, T3, T4) -> V + Send + Sync),
    ) -> Result<&Self, String>
    where
        T1: From<Operand>,
        T2: From<Operand>,
        T3: From<Operand>,
        T4: From<Operand>,
        V: Into<Operand>,
    {
        if self.functions.contains_key(&function_name) {
            return Err(format!("{} is already added as a function", function_name));
        }

        self.functions
            .insert(function_name, to_function_container4(function));
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

pub fn to_function_container1<'a, T: From<Operand>, V: Into<Operand>>(
    func: &'a (dyn Fn(T) -> V + Send + Sync),
) -> FunctionContainer {
    FunctionContainer::F1(Box::new(move |v: Operand| -> Operand {
        func(v.into()).into()
    }))
}

pub fn to_function_container2<'a, T1: From<Operand>, T2: From<Operand>, V: Into<Operand>>(
    func: &'a (dyn Fn(T1, T2) -> V + Send + Sync),
) -> FunctionContainer {
    FunctionContainer::F2(Box::new(move |v1: Operand, v2: Operand| -> Operand {
        func(v1.into(), v2.into()).into()
    }))
}

pub fn to_function_container3<
    'a,
    T1: From<Operand>,
    T2: From<Operand>,
    T3: From<Operand>,
    V: Into<Operand>,
>(
    func: &'a (dyn Fn(T1, T2, T3) -> V + Send + Sync),
) -> FunctionContainer {
    FunctionContainer::F3(Box::new(
        move |v1: Operand, v2: Operand, v3: Operand| -> Operand {
            func(v1.into(), v2.into(), v3.into()).into()
        },
    ))
}

pub fn to_function_container4<
    'a,
    T1: From<Operand>,
    T2: From<Operand>,
    T3: From<Operand>,
    T4: From<Operand>,
    V: Into<Operand>,
>(
    func: &'a (dyn Fn(T1, T2, T3, T4) -> V + Send + Sync),
) -> FunctionContainer {
    FunctionContainer::F4(Box::new(
        move |v1: Operand, v2: Operand, v3: Operand, v4: Operand| -> Operand {
            func(v1.into(), v2.into(), v3.into(), v4.into()).into()
        },
    ))
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

#[cfg(test)]
fn func(a: i64, b: i64) -> i64 {
    a + b
}

#[test]
fn render_function() {
    let template = r#"func(a,b) = <%= func(a, b) %>"#.to_string();
    let mut dojang = Dojang::new();
    assert!(dojang.add("some_template".to_string(), template).is_ok());
    assert!(dojang.add_function_2("func".to_string(), &func).is_ok());

    assert_eq!(
        dojang
            .render(
                "some_template",
                serde_json::from_str(r#"{ "a" : 1, "b" : 2 }"#).unwrap()
            )
            .unwrap(),
        "func(a,b) = 3"
    );
}
