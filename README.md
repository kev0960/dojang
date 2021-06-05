# Dojang

![Test and Coverage](https://github.com/kev0960/dojang/actions/workflows/test.yaml/badge.svg)

[crates.io]: https://crates.io/crates/dojang

**Dojang** is a Html template engine, as a drop in replacement for [EJS](https://ejs.co/). Though it does not supports 100% of the javascript syntax, it supports enough to cover the basic usages.

## Features

* Supports basic javascript. (if, for, while, etc.)
* Supports script and output tags. (<%, <%-, <%=)
* Supports calling external functions.

## How to use?

```rust
use dojang::Dojang;
use serde_json::Value;

// Create a template engine Dojang.
let mut dojang = Dojang::new();

// Load template file under '/my/template/files'
assert!(dojang.load("/my/template/files").is_ok());

// Render a template. "some_template" is the one of the template file under /my/template/files. 
// Note that the context should be provided as a serde_json value.
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
* Optimization.
