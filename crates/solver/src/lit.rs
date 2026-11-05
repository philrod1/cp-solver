use crate::model::VarId;

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub(crate) enum Lit {
    Eq(VarId, i64),
    Neq(VarId, i64),
}

impl Lit {
    pub(crate) fn negated(self) -> Self {
        match self {
            Lit::Eq(var, val) => Lit::Neq(var, val),
            Lit::Neq(var, val) => Lit::Eq(var, val),
        }
    }
}
