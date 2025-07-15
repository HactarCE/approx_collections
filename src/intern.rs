//! Interner that canonicalizes similar floats.

use crate::{Precision, VisitFloats};

#[cfg(feature = "rustc-hash")]
type HashMap<K, V> = rustc_hash::FxHashMap<K, V>;
#[cfg(not(feature = "rustc-hash"))]
type HashMap<K, V> = std::collections::HashMap<K, V>;

/// Structure for interning floats based on approximate equality.
///
/// # Examples
#[derive(Debug, Clone)]
pub struct FloatInterner {
    prec: Precision,
    floats: HashMap<u64, f64>,
}

impl Default for FloatInterner {
    /// Constructs a float interner using [`Precision::default()`].
    fn default() -> Self {
        Self::new(Precision::default())
    }
}

impl FloatInterner {
    /// Constructs a new float interner with the given precision.
    pub fn new(prec: Precision) -> Self {
        // Start with 0 because that should always be exact.
        let floats = HashMap::from_iter([(0, 0.0)]);
        Self { prec, floats }
    }

    /// Returns the precision level used by the interner.
    pub fn prec(&self) -> Precision {
        self.prec
    }

    /// Canonicalizes all floats in `value`, returning a mutated copy of
    /// `value`.
    #[must_use = "canonicalize() returns a mutated copy"]
    pub fn canonicalize<V: VisitFloats>(&mut self, mut value: V) -> V {
        self.canonicalize_in_place(&mut value);
        value
    }
    /// Canonicalizes all floats in `value`.
    pub fn canonicalize_in_place<V: VisitFloats>(&mut self, value: &mut V) {
        value.visit_floats_mut(|x| {
            let (f, _) = self.insert(*x);
            *x = f;
        });
    }

    /// Searches for an existing hash value for a float that is approximately
    /// equal to `x`, and returns it and its bucket if found. Returns `None` if
    /// there is no existing value that is close to `x`.
    pub(crate) fn get(&self, x: f64) -> Option<(f64, u64)> {
        self.floats
            .get(&self.prec.bucket(x))
            .map(|&f| (f, self.prec.bucket(f)))
    }

    /// Searches for an existing bucket value for a float that is approximately
    /// equal to `x`, and returns the existing float and its bucket if found. If
    /// none is found, inserts it and returns itself and its bucket.
    pub(crate) fn insert(&mut self, x: f64) -> (f64, u64) {
        let (lo, mid, hi) = self.prec.nearby_buckets(x);
        match self.floats.entry(mid) {
            std::collections::hash_map::Entry::Occupied(e) => {
                let f = *e.get();
                (f, self.prec.bucket(f))
            }
            std::collections::hash_map::Entry::Vacant(e) => {
                e.insert(x);
                if let Some(k) = lo {
                    self.floats.insert(k, x);
                }
                if let Some(k) = hi {
                    self.floats.insert(k, x);
                }
                (x, mid)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_float_interning() {
        let mut interner = FloatInterner::new(Precision::absolute(3)); // bucket size = 0.125
        assert_eq!(1.0, interner.canonicalize(1.0));
        assert_eq!(1.0, interner.canonicalize(1.1));
        assert_eq!(2.1, interner.canonicalize(2.1));
        assert_eq!(2.1, interner.canonicalize(1.9));
        assert_eq!(0.73, interner.canonicalize(0.73));
        assert_eq!(0.73, interner.canonicalize(0.8));
        assert_eq!(0.49, interner.canonicalize(0.49));
    }

    #[test]
    fn test_struct_float_interning() {
        let mut interner = FloatInterner::new(Precision::absolute(3)); // bucket size = 0.125
        assert_eq!([0.0, 0.0, 0.5], interner.canonicalize([0.1, 0.0, 0.5]));
        assert_eq!([0.5, 0.8, 0.8], interner.canonicalize([0.6, 0.8, 0.75]));
    }
}
