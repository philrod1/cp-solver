//! Integer domains as sparse sets.
//!
//! Values are stored as indices `value - offset`, where `offset` is the
//! initial lower bound. `dense[..size]` holds the indices currently in the
//! domain; `sparse[i]` is the position of index `i` in `dense`. Removals only
//! swap within `dense[..size]`, so restoring an old `size` (plus the cached
//! bounds) brings back exactly the removed values.

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Conflict;

/// Everything needed to undo changes to a `SparseDomain`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) struct DomainState {
    size: u32,
    lower: i64,
    upper: i64,
}

#[derive(Clone, Debug)]
pub struct SparseDomain {
    offset: i64,
    lower: i64,
    upper: i64,
    dense: Vec<u32>,
    sparse: Vec<u32>,
    size: u32,
}

impl SparseDomain {
    /// A domain containing `lo..=hi`.
    pub fn new(lo: i64, hi: i64) -> Self {
        assert!(lo <= hi, "empty domain {lo}..={hi}");
        let n = u32::try_from(hi - lo + 1).expect("domain too large");
        Self {
            offset: lo,
            lower: lo,
            upper: hi,
            dense: (0..n).collect(),
            sparse: (0..n).collect(),
            size: n,
        }
    }

    pub fn lower(&self) -> i64 {
        self.lower
    }

    pub fn upper(&self) -> i64 {
        self.upper
    }

    pub fn size(&self) -> u32 {
        self.size
    }

    pub fn fixed_value(&self) -> Option<i64> {
        (self.size == 1).then_some(self.lower)
    }

    pub fn contains(&self, val: i64) -> bool {
        // The bounds check also keeps `val - offset` inside the arrays.
        val >= self.lower
            && val <= self.upper
            && self.sparse[(val - self.offset) as usize] < self.size
    }

    /// Current values in no particular order.
    pub fn iter(&self) -> impl Iterator<Item = i64> + '_ {
        self.dense[..self.size as usize]
            .iter()
            .map(move |&i| i as i64 + self.offset)
    }

    /// Remove `val` ...
    /// Ok(true) if the domain changed
    /// Ok(false) if `val` wasn't there
    /// Err(Conflict) if it was the last value
    pub fn remove(&mut self, val: i64) -> Result<bool, Conflict> {
        if !self.contains(val) {
            return Ok(false);
        }
        if self.size == 1 {
            return Err(Conflict);
        }
        let pos = self.position(val);
        self.swap(pos, self.size as usize - 1);
        self.size -= 1;

        if val == self.lower {
            while !self.contains(self.lower) {
                self.lower += 1;
            }
        } else if val == self.upper {
            while !self.contains(self.upper) {
                self.upper -= 1;
            }
        }
        Ok(true)
    }

    /// Reduce the domain to `{val}`
    /// Ok(false) if it already was
    /// Err(Conflict) if `val` isn't in the domain
    pub fn fix(&mut self, val: i64) -> Result<bool, Conflict> {
        if !self.contains(val) {
            return Err(Conflict);
        }
        if self.size == 1 {
            return Ok(false);
        }
        let pos = self.position(val);
        self.swap(pos, 0);
        self.size = 1;
        self.lower = val;
        self.upper = val;
        Ok(true)
    }

    /// Remove every value below `k`. `Ok(false)` if there were none,
    /// `Err(Conflict)` if no value would be left.
    pub fn set_lower(&mut self, k: i64) -> Result<bool, Conflict> {
        if k <= self.lower {
            return Ok(false);
        }
        if k > self.upper {
            return Err(Conflict);
        }
        self.keep_range(k, self.upper);
        Ok(true)
    }

    /// Remove every value above `k`. `Ok(false)` if there were none,
    /// `Err(Conflict)` if no value would be left.
    pub fn set_upper(&mut self, k: i64) -> Result<bool, Conflict> {
        if k >= self.upper {
            return Ok(false);
        }
        if k < self.lower {
            return Err(Conflict);
        }
        self.keep_range(self.lower, k);
        Ok(true)
    }

    /// Remove every value outside `lo..=hi`. The caller guarantees at least
    /// one value survives: the bound that isn't moving is still in the domain.
    fn keep_range(&mut self, lo: i64, hi: i64) {
        // Values in the range being cut, present or not.
        let cut = (lo - self.lower) + (self.upper - hi);
        if cut < self.size as i64 {
            // Few to cut: visit each candidate value.
            for v in (self.lower..lo).chain(hi + 1..=self.upper) {
                if self.contains(v) {
                    let pos = self.position(v);
                    self.swap(pos, self.size as usize - 1);
                    self.size -= 1;
                }
            }
        } else {
            // Many to cut: scan the values still in the domain instead.
            let mut i = 0;
            while i < self.size as usize {
                let v = self.dense[i] as i64 + self.offset;
                if v < lo || v > hi {
                    self.swap(i, self.size as usize - 1);
                    self.size -= 1;
                } else {
                    i += 1;
                }
            }
        }
        // Both scans stop: `lo..=hi` still holds a value.
        self.lower = lo;
        while !self.contains(self.lower) {
            self.lower += 1;
        }
        self.upper = hi;
        while !self.contains(self.upper) {
            self.upper -= 1;
        }
    }

    /// The state the trail needs to save.
    pub(crate) fn snapshot(&self) -> DomainState {
        DomainState {
            size: self.size,
            lower: self.lower,
            upper: self.upper,
        }
    }

    /// Undo back to a saved state. Only valid in LIFO order.
    pub(crate) fn restore(&mut self, state: DomainState) {
        self.size = state.size;
        self.lower = state.lower;
        self.upper = state.upper;
    }

    fn position(&self, val: i64) -> usize {
        self.sparse[(val - self.offset) as usize] as usize
    }

    /// Swap two positions in `dense`, keeping `sparse` consistent.
    fn swap(&mut self, a: usize, b: usize) {
        let (ia, ib) = (self.dense[a] as usize, self.dense[b] as usize);
        self.dense.swap(a, b);
        self.sparse[ia] = b as u32;
        self.sparse[ib] = a as u32;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    fn values(d: &SparseDomain) -> BTreeSet<i64> {
        d.iter().collect()
    }

    #[test]
    fn new_domain_has_all_values() {
        let d = SparseDomain::new(-3, 3);
        assert_eq!(values(&d), (-3..=3).collect());
        assert_eq!((d.lower(), d.upper(), d.size()), (-3, 3, 7));
    }

    #[test]
    fn remove_middle_value() {
        let mut d = SparseDomain::new(0, 4);
        assert_eq!(d.remove(2), Ok(true));
        assert!(!d.contains(2));
        assert_eq!(d.size(), 4);
        assert_eq!(d.remove(2), Ok(false));
        assert_eq!(values(&d), [0, 1, 3, 4].into());
    }

    #[test]
    fn removing_bounds_updates_them() {
        let mut d = SparseDomain::new(-2, 5);
        d.remove(-1).unwrap();
        d.remove(-2).unwrap(); // lower skips the gap at -1
        assert_eq!(d.lower(), 0);
        d.remove(4).unwrap();
        d.remove(5).unwrap();
        assert_eq!(d.upper(), 3);
    }

    #[test]
    fn out_of_range_values_are_absent() {
        let mut d = SparseDomain::new(1, 3);
        assert!(!d.contains(0));
        assert!(!d.contains(4));
        assert_eq!(d.remove(-10), Ok(false));
        assert_eq!(d.fix(99), Err(Conflict));
    }

    #[test]
    fn fix_and_conflict() {
        let mut d = SparseDomain::new(0, 9);
        assert_eq!(d.fix(7), Ok(true));
        assert_eq!(d.fixed_value(), Some(7));
        assert_eq!(d.fix(7), Ok(false));
        assert_eq!(d.fix(3), Err(Conflict));
        assert_eq!(d.remove(7), Err(Conflict));
    }

    #[test]
    fn restore_brings_back_exactly_the_removed_values() {
        let mut d = SparseDomain::new(-4, 4);
        let level0 = d.snapshot();
        let all = values(&d);

        d.remove(0).unwrap();
        d.remove(-4).unwrap();
        let level1 = d.snapshot();
        let after1 = values(&d);

        d.remove(3).unwrap();
        d.fix(-2).unwrap();
        assert_eq!(values(&d), [-2].into());

        d.restore(level1);
        assert_eq!(values(&d), after1);
        assert_eq!((d.lower(), d.upper()), (-3, 4));

        d.restore(level0);
        assert_eq!(values(&d), all);
        for v in -4..=4 {
            assert!(d.contains(v));
        }
    }

    #[test]
    fn set_lower_and_upper_skip_holes() {
        let mut d = SparseDomain::new(0, 9);
        d.remove(4).unwrap();
        d.remove(6).unwrap();
        assert_eq!(d.set_lower(4), Ok(true)); //    4 is a hole, so lower is 5
        assert_eq!(d.lower(), 5);
        assert_eq!(d.set_upper(6), Ok(true)); //    6 is a hole, so upper is 5
        assert_eq!(values(&d), [5].into());
        assert_eq!(d.fixed_value(), Some(5));
    }

    #[test]
    fn bounds_that_change_nothing() {
        let mut d = SparseDomain::new(2, 8);
        assert_eq!(d.set_lower(-5), Ok(false));
        assert_eq!(d.set_lower(2), Ok(false));
        assert_eq!(d.set_upper(8), Ok(false));
        assert_eq!(d.set_upper(100), Ok(false));
        assert_eq!(d.size(), 7);
    }

    #[test]
    fn bounds_past_each_other_conflict() {
        let mut d = SparseDomain::new(0, 5);
        assert_eq!(d.set_lower(6), Err(Conflict));
        assert_eq!(d.set_upper(-1), Err(Conflict));
        d.set_lower(3).unwrap();
        assert_eq!(d.set_upper(2), Err(Conflict));
    }

    #[test]
    fn big_cut_uses_the_scan_and_still_restores() {
        // 80 holes, so cutting 0..95 is more values than remain: scan path.
        let mut d = SparseDomain::new(0, 99);
        let before = d.snapshot();
        for v in 10..90 {
            d.remove(v).unwrap();
        }
        d.set_lower(95).unwrap();
        assert_eq!(values(&d), (95..=99).collect());
        d.restore(before);
        assert_eq!(values(&d), (0..=99).collect());
    }

    #[test]
    fn small_cut_uses_values_and_still_restores() {
        let mut d = SparseDomain::new(-5, 5);
        let before = d.snapshot();
        d.set_lower(-3).unwrap();
        d.set_upper(2).unwrap();
        assert_eq!(values(&d), (-3..=2).collect());
        assert_eq!((d.lower(), d.upper()), (-3, 2));
        d.restore(before);
        assert_eq!(values(&d), (-5..=5).collect());
    }
}
