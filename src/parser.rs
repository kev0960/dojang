#![allow(dead_code)]

enum Action<'a> {
    Show(Show<'a>),
    If(If<'a>),
    Loop(Loop<'a>),
    Null(),
}

struct If<'a> {
    cond: Box<Action<'a>>,
    when_true: Box<Action<'a>>,
    when_false: Box<Action<'a>>,
}

struct Loop<'a> {
    cond: Box<Action<'a>>,
    exec: Box<Action<'a>>,
}

enum Show<'a> {
    Html(&'a str),
    Expr(Box<Action<'a>>),
}

pub struct Parser<'a> {
    parse_tree: Vec<Action<'a>>,
}

impl<'a> Parser<'a> {
    pub fn parse(template: &'a str) -> Result<Self, String> {
        match Parser::recursive_parser(template) {
            Ok(parse_tree) => Ok(Parser { parse_tree }),
            Err(e) => Err(e),
        }
    }

    fn recursive_parser(mut template: &'a str) -> Result<Vec<Action<'a>>, String> {
        let mut parse_tree = Vec::new();
        while !template.is_empty() {
            match template.find("<%") {
                Some(tag_start) => {
                    let before_tag = &template[..tag_start];
                    parse_tree.push(Action::Show(Show::Html(before_tag)));

                    let after_tag = &template[tag_start + 2..];
                    match after_tag.find("%>") {
                        Some(tag_end) => {
                            let parsed_tag = Parser::parse_tag(&after_tag[..tag_end]);
                            match parsed_tag {
                                Ok(mut tree) => {
                                    parse_tree.append(&mut tree);
                                }
                                Err(s) => {
                                    return Err(s.to_string());
                                }
                            }
                            template = &after_tag[tag_end + 2..];
                        }
                        _ => {
                            return Err("Unmatched %> tag found".to_string());
                        }
                    }
                }
                _ => {
                    parse_tree.push(Action::Show(Show::Html(template)));
                    break;
                }
            }
        }

        Ok(parse_tree)
    }

    fn parse_tag(tag_to_parse: &'a str) -> Result<Vec<Action<'a>>, String> {
        println!("Tag to parse: '{}'", tag_to_parse);
        return Ok(Vec::new());
    }
}

#[test]
fn parse_tag() {
    Parser::parse("this <%sometag%> abc");
}
