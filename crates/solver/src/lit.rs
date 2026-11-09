use crate::model::VarId;

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub(crate) enum Lit {
    Eq(VarId, i64),
    Neq(VarId, i64),
    Ge(VarId, i64),
    Lt(VarId, i64),
}

impl Lit {
    pub(crate) fn negated(self) -> Self {
        match self {
            Lit::Eq(var, val) => Lit::Neq(var, val),
            Lit::Neq(var, val) => Lit::Eq(var, val),
            Lit::Ge(var, val) => Lit::Lt(var, val),
            Lit::Lt(var, val) => Lit::Ge(var, val),
        }
    }

    pub(crate) fn var(self) -> VarId {
        match self {
            Lit::Eq(var, _) | Lit::Neq(var, _) | Lit::Ge(var, _) | Lit::Lt(var, _) => var,
        }
    }
}
