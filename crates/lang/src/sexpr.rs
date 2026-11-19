//! S-expressions: atoms and lists, nothing more.
//!
//! Whitespace and brackets are the only delimiters; every other run of
//! characters is an atom. Atoms carry no type: `_1`, `-3`, `all_different`
//! and `*` are all just text, and meaning is decided by whoever reads them.
//! `Display` prints the canonical single-line form, so parsing a canonical
//! string and printing it gives back the same string. Every expression
//! knows where in the text it came from, for error messages.

use std::fmt;

/// An expression and the text it was parsed from. Equality ignores where
/// the text was: `(a  b)` on line 3 equals `(a b)` on line 1.
#[derive(Clone, Debug)]
pub struct SExpr {
    pub node: Node,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Node {
    Atom(String),
    List(Vec<SExpr>),
}

impl PartialEq for SExpr {
    fn eq(&self, other: &Self) -> bool {
        self.node == other.node
    }
}

impl Eq for SExpr {}

/// A place in the text. `offset` is in bytes; lines and columns count from
/// 1, and columns count characters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Position {
    pub offset: usize,
    pub line: usize,
    pub column: usize,
}

impl Position {
    const START: Position = Position {
        offset: 0,
        line: 1,
        column: 1,
    };

    /// The position just past `c`, which starts here.
    fn after(self, c: char) -> Position {
        if c == '\n' {
            Position {
                offset: self.offset + 1,
                line: self.line + 1,
                column: 1,
            }
        } else {
            Position {
                offset: self.offset + c.len_utf8(),
                line: self.line,
                column: self.column + 1,
            }
        }
    }
}

/// The text from `start` up to, but not including, `end`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    pub start: Position,
    pub end: Position,
}

/// Text that isn't exactly one well-formed s-expression, and the part of
/// it at fault.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SExprError {
    pub message: String,
    pub span: Span,
}

impl SExprError {
    fn new(message: &str, span: Span) -> Self {
        SExprError {
            message: message.into(),
            span,
        }
    }
}

impl fmt::Display for SExprError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Position { line, column, .. } = self.span.start;
        write!(f, "line {line}, column {column}: {}", self.message)
    }
}

impl std::error::Error for SExprError {}

impl SExpr {
    pub fn as_atom(&self) -> Option<&str> {
        match &self.node {
            Node::Atom(a) => Some(a),
            Node::List(_) => None,
        }
    }

    pub fn as_list(&self) -> Option<&[SExpr]> {
        match &self.node {
            Node::Atom(_) => None,
            Node::List(items) => Some(items),
        }
    }
}

impl fmt::Display for SExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.node {
            Node::Atom(a) => f.write_str(a),
            Node::List(items) => {
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
enum Kind<'a> {
    Open,
    Close,
    Atom(&'a str),
}

#[derive(Debug)]
struct Token<'a> {
    kind: Kind<'a>,
    span: Span,
}

/// The tokens, and the position at the end of the text.
fn tokenise(text: &str) -> (Vec<Token<'_>>, Position) {
    let mut tokens = Vec::new();
    let mut chars = text.chars().peekable();
    let mut at = Position::START;
    while let Some(&c) = chars.peek() {
        let start = at;
        chars.next();
        at = at.after(c);
        let kind = match c {
            _ if c.is_whitespace() => continue,
            '(' => Kind::Open,
            ')' => Kind::Close,
            _ => {
                while let Some(&c) = chars.peek() {
                    if c.is_whitespace() || c == '(' || c == ')' {
                        break;
                    }
                    chars.next();
                    at = at.after(c);
                }
                Kind::Atom(&text[start.offset..at.offset])
            }
        };
        tokens.push(Token {
            kind,
            span: Span { start, end: at },
        });
    }
    (tokens, at)
}

/// Parse exactly one s-expression, ignoring surrounding whitespace.
pub fn parse(text: &str) -> Result<SExpr, SExprError> {
    let (tokens, end) = tokenise(text);
    let Some(last) = tokens.last() else {
        let nowhere = Span { start: end, end };
        return Err(SExprError::new("empty input", nowhere));
    };
    let (expr, used) = parse_at(&tokens, 0)?;
    if let Some(Token {
        kind: Kind::Close,
        span,
    }) = tokens.get(used)
    {
        return Err(SExprError::new("unexpected ')'", *span));
    }
    if used != tokens.len() {
        let extra = Span {
            start: tokens[used].span.start,
            end: last.span.end,
        };
        let message = "more than one top-level expression";
        return Err(SExprError::new(message, extra));
    }
    Ok(expr)
}

/// Parse the expression starting at `tokens[i]`, which must exist,
/// returning it and the index just past it.
fn parse_at(tokens: &[Token<'_>], i: usize) -> Result<(SExpr, usize), SExprError> {
    let token = &tokens[i];
    match token.kind {
        Kind::Close => Err(SExprError::new("unexpected ')'", token.span)),
        Kind::Atom(a) => {
            let node = Node::Atom(a.to_string());
            Ok((
                SExpr {
                    node,
                    span: token.span,
                },
                i + 1,
            ))
        }
        Kind::Open => {
            let mut items = Vec::new();
            let mut i = i + 1;
            loop {
                match tokens.get(i).map(|t| &t.kind) {
                    // The innermost bracket left open is the one reported.
                    None => return Err(SExprError::new("unclosed '('", token.span)),
                    Some(Kind::Close) => {
                        let span = Span {
                            start: token.span.start,
                            end: tokens[i].span.end,
                        };
                        let node = Node::List(items);
                        return Ok((SExpr { node, span }, i + 1));
                    }
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

    /// Expressions built here have no text, so they are placed nowhere.
    const NOWHERE: Span = Span {
        start: Position::START,
        end: Position::START,
    };

    fn atom(a: &str) -> SExpr {
        let node = Node::Atom(a.into());
        SExpr {
            node,
            span: NOWHERE,
        }
    }

    fn list(items: Vec<SExpr>) -> SExpr {
        let node = Node::List(items);
        SExpr {
            node,
            span: NOWHERE,
        }
    }

    #[test]
    fn atoms_and_lists() {
        assert_eq!(parse("abc").unwrap(), atom("abc"));
        assert_eq!(parse("-17").unwrap(), atom("-17"));
        assert_eq!(parse("()").unwrap(), list(vec![]));
        assert_eq!(
            parse("(a (b -1) *)").unwrap(),
            list(vec![
                atom("a"),
                list(vec![atom("b"), atom("-1")]),
                atom("*")
            ])
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

    /// The error for `text`: its message, and where its span starts and
    /// ends as (line, column).
    fn error(text: &str) -> (String, (usize, usize), (usize, usize)) {
        let e = parse(text).unwrap_err();
        let at = |p: Position| (p.line, p.column);
        (e.message, at(e.span.start), at(e.span.end))
    }

    #[test]
    fn errors_say_where() {
        let unclosed = "unclosed '('".to_string();
        let unexpected = "unexpected ')'".to_string();
        let more = "more than one top-level expression".to_string();
        // Nothing at all: the end of the text.
        assert_eq!(error(""), ("empty input".into(), (1, 1), (1, 1)));
        assert_eq!(error("  \n "), ("empty input".into(), (2, 2), (2, 2)));
        // The innermost bracket left open.
        assert_eq!(error("(a\n  (b c"), (unclosed.clone(), (2, 3), (2, 4)));
        assert_eq!(error("(a (b)"), (unclosed, (1, 1), (1, 2)));
        // A stray close, alone or after a complete expression.
        assert_eq!(error(")"), (unexpected.clone(), (1, 1), (1, 2)));
        assert_eq!(error("(a)\n)"), (unexpected, (2, 1), (2, 2)));
        // Everything after the first expression.
        assert_eq!(error("a bc"), (more.clone(), (1, 3), (1, 5)));
        assert_eq!(error("(a) (b)\n(c)"), (more, (1, 5), (2, 4)));
    }

    #[test]
    fn every_expression_knows_where_it_is() {
        let text = "(a\n  (bc -1))";
        let top = parse(text).unwrap();
        let at = |e: &SExpr| {
            let Span { start, end } = e.span;
            ((start.line, start.column), (end.line, end.column))
        };
        let shown = |e: &SExpr| &text[e.span.start.offset..e.span.end.offset];
        assert_eq!(at(&top), ((1, 1), (2, 11)));
        let items = top.as_list().unwrap();
        assert_eq!(at(&items[0]), ((1, 2), (1, 3)));
        assert_eq!(at(&items[1]), ((2, 3), (2, 10)));
        assert_eq!(shown(&items[1]), "(bc -1)");
        assert_eq!(shown(&items[1].as_list().unwrap()[1]), "-1");
        // Where an expression is doesn't affect equality.
        assert_eq!(top, parse("(a (bc -1))").unwrap());
    }

    #[test]
    fn columns_count_characters_and_offsets_count_bytes() {
        // `é` is one character but two bytes.
        let e = parse("(é (").unwrap_err();
        assert_eq!((e.span.start.column, e.span.start.offset), (4, 4));
        assert_eq!(e.to_string(), "line 1, column 4: unclosed '('");
    }
}
