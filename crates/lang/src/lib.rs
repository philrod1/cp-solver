//! Front ends that turn text into a solver `Model`.
//!
//! - [`sexpr`]: a generic s-expression parser.
//! - [`scp`]: the `.scp` format used by the Glasgow Constraint Solver and the
//!   verified CakePB-CP encoder.

pub mod scp;
pub mod sexpr;

pub use scp::{ProbType, ScpError, ScpModel, read_scp};
