//! Dojang, a EJS inspired HTML template engine.
//!
//! Dojang is a html template engine, which aims to be an drop-in replacement for the EJS html
//! template engine. It follows the syntax of the EJS while adopting Rust for the embedded code.
mod context;
pub mod dojang;
mod eval;
mod exec;
mod expr;
pub mod func_helper;

pub use crate::context::FunctionContainer;
pub use crate::dojang::Dojang;
