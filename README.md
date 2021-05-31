# Dojang

[crates.io]: https://crates.io/crates/dojang

**Dojang** is a Html template engine, as a drop in replacement for [EJS](https://ejs.co/). Though it does not supports 100% of the javascript syntax, it supports enough to cover the basic usages.

## Features

* Supports basic javascript. (if, for, while, etc.)
* Supports script and output tags. (<%, <%-, <%=)

## How to use?

```
use dojang::Dojang;
use serde_json::Value;

let template = "<% if a == 1 { %> Hi <% } else { %><%= a %><% } %>";

// Create a template engine Dojang.
let mut dojang = Dojang::new();

// Add a template file.
assert!(dojang.add("some_template", template).is_ok());

// Render a template. Note that the context should be provided as a serde_json value.
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
```

## Features coming soon.

* Support for file includes (<%- .. >)
* Function calling.
* break, continue keywords.
* Optimization.
