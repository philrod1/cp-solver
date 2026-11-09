//! S-expressions: atoms and lists, nothing more.
//!
//! Whitespace and brackets are the only delimiters; every other run of
//! characters is an atom. Atoms carry no type: `_1`, `-3`, `all_different`
//! and `*` are all just text, and meaning is decided by whoever reads them.
//! `Display` prints the canonical single-line form, so parsing a canonical
//! string and printing it gives back the same string.

use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SExpr {
    Atom(String),
    List(Vec<SExpr>),
}

/// Text that isn't exactly one well-formed s-expression.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SExprError(pub String);

impl fmt::Display for SExprError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for SExprError {}

impl SExpr {
    pub fn as_atom(&self) -> Option<&str> {
        match self {
            SExpr::Atom(a) => Some(a),
            SExpr::List(_) => None,
        }
    }

    pub fn as_list(&self) -> Option<&[SExpr]> {
        match self {
            SExpr::Atom(_) => None,
            SExpr::List(items) => Some(items),
        }
    }
}

impl fmt::Display for SExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SExpr::Atom(a) => f.write_str(a),
            SExpr::List(items) => {
                f.write_str("(")?;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        f.write_str(" ")?;
                    }
                    write!(f, "{item}")?;
                }
                f.write_str(")")
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Token<'a> {
    Open,
    Close,
    Atom(&'a str),
}

fn tokenise(text: &str) -> Vec<Token<'_>> {
    let mut tokens = Vec::new();
    let mut rest = text;
    loop {
        rest = rest.trim_start();
        let Some(c) = rest.chars().next() else {
            return tokens;
        };
        match c {
            '(' => {
                tokens.push(Token::Open);
                rest = &rest[1..];
            }
            ')' => {
                tokens.push(Token::Close);
                rest = &rest[1..];
            }
            _ => {
                let end = rest
                    .find(|c: char| c.is_whitespace() || c == '(' || c == ')')
                    .unwrap_or(rest.len());
                tokens.push(Token::Atom(&rest[..end]));
                rest = &rest[end..];
            }
        }
    }
}

/// Parse exactly one s-expression, ignoring surrounding whitespace.
pub fn parse(text: &str) -> Result<SExpr, SExprError> {
    let tokens = tokenise(text);
    if tokens.is_empty() {
        return Err(SExprError("empty input".into()));
    }
    let (expr, used) = parse_at(&tokens, 0)?;
    if used != tokens.len() {
        return Err(SExprError("more than one top-level expression".into()));
    }
    Ok(expr)
}

/// Parse the expression starting at `tokens[i]`, returning it and the index
/// just past it.
fn parse_at(tokens: &[Token<'_>], i: usize) -> Result<(SExpr, usize), SExprError> {
    match tokens.get(i) {
        None => Err(SExprError("unexpected end of input".into())),
        Some(Token::Close) => Err(SExprError("unexpected ')'".into())),
        Some(Token::Atom(a)) => Ok((SExpr::Atom(a.to_string()), i + 1)),
        Some(Token::Open) => {
            let mut items = Vec::new();
            let mut i = i + 1;
            loop {
                match tokens.get(i) {
                    None => return Err(SExprError("unclosed '('".into())),
                    Some(Token::Close) => return Ok((SExpr::List(items), i + 1)),
                    Some(_) => {
                        let (item, next) = parse_at(tokens, i)?;
                        items.push(item);
                        i = next;
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn atom(a: &str) -> SExpr {
        SExpr::Atom(a.into())
    }

    #[test]
    fn atoms_and_lists() {
        assert_eq!(parse("abc").unwrap(), atom("abc"));
        assert_eq!(parse("-17").unwrap(), atom("-17"));
        assert_eq!(parse("()").unwrap(), SExpr::List(vec![]));
        assert_eq!(
            parse("(a (b -1) *)").unwrap(),
            SExpr::List(vec![atom("a"), SExpr::List(vec![atom("b"), atom("-1")]), atom("*")])
        );
    }

    #[test]
    fn brackets_end_atoms_without_spaces() {
        // GCS has written `negative_table(` with no space before the bracket.
        assert_eq!(
            parse("(x negative_table((1 2)) (a b))").unwrap(),
            parse("(x negative_table ( (1 2) ) (a b))").unwrap()
        );
    }

    #[test]
    fn whitespace_of_any_kind_is_ignored() {
        assert_eq!(parse("  (a\n\tb )  \n").unwrap(), parse("(a b)").unwrap());
    }

    #[test]
    fn canonical_text_round_trips() {
        let text = "((version 1) (variables (x 0 10)) (constraints (c1 lin_equals (2 x 1 y) 12)) (prob_type enumerate))";
        assert_eq!(parse(text).unwrap().to_string(), text);
    }

    #[test]
    fn malformed_input_is_rejected() {
        for bad in ["", "   ", "(", "(a (b)", ")", "(a))", "a b", "(a) (b)"] {
            assert!(parse(bad).is_err(), "accepted {bad:?}");
        }
    }
}
