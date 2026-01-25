//! Interner that canonicalizes similar floats.

use std::collections::hash_map;
use std::fmt;
use std::iter::FusedIterator;

use crate::{ApproxHash, Precision};

#[cfg(feature = "rustc-hash")]
type HashMap<K, V> = rustc_hash::FxHashMap<K, V>;
#[cfg(not(feature = "rustc-hash"))]
type HashMap<K, V> = std::collections::HashMap<K, V>;

/// Structure for interning similar floats based on approximate equality.
///
/// # Examples
///
/// ```
/// use approx_collections::FloatPool;
///
/// let mut pool = FloatPool::default();
///
/// let very_small_delta = 0.0000000001;
///
/// assert_eq!(pool.intern(4.0), 4.0);
/// assert_eq!(pool.intern(4.0 + very_small_delta), 4.0);
/// assert_eq!(pool.intern(4.0 - very_small_delta), 4.0);
///
/// assert_eq!(pool.intern(3.0 - very_small_delta), 3.0 - very_small_delta);
/// assert_eq!(pool.intern(3.0), 3.0 - very_small_delta);
/// ```
#[derive(Clone)]
pub struct FloatPool {
    prec: Precision,
    floats: HashMap<u64, f64>,
}

impl fmt::Debug for FloatPool {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let floats: std::collections::BTreeMap<_, _> =
            self.floats.iter().map(|(&k, &v)| (k, v)).collect();
        f.debug_struct("FloatPool")
            .field("prec", &self.prec)
            .field("floats", &floats)
            .finish()
    }
}

impl Default for FloatPool {
    /// Constructs a float interner using [`Precision::default()`].
    fn default() -> Self {
        Self::new(Precision::default())
    }
}

impl FloatPool {
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

    /// Replaces all floats in `value` with interned ones that are approximately
    /// equal, returning a mutated copy of `value`.
    ///
    /// If any floats in `value` are have not already been interned, they are
    /// added to the pool and unmodified.
    #[must_use = "intern() returns a mutated copy"]
    pub fn intern<V: ApproxHash>(&mut self, mut value: V) -> V {
        self.intern_in_place(&mut value);
        value
    }
    /// Replaces all floats in `value` with interned ones that are approximately
    /// equal.
    ///
    /// If any floats in `value` are have not already been interned, they are
    /// added to the pool and unmodified.
    pub fn intern_in_place<V: ApproxHash>(&mut self, value: &mut V) {
        value.intern_floats(&mut |x| *x = self.insert(*x).0);
    }

    /// Replaces all floats in `value` with interned ones that are approximately
    /// equal, returning a mutated copy of `value`. Returns `None` if any floats
    /// in `value` are not already in the pool.
    #[must_use = "try_intern() returns a mutated copy"]
    pub fn try_intern<V: ApproxHash>(&self, mut value: V) -> Option<V> {
        let mut failed = false;
        value.intern_floats(&mut |x| {
            if !failed {
                match self.get(*x) {
                    Some(saved) => *x = saved,
                    None => failed = true,
                }
            }
        });
        (!failed).then_some(value)
    }

    /// Searches for an existing hash value for a float that is approximately
    /// equal to `x`, and returns it and its bucket if found. Returns `None` if
    /// there is no existing value that is close to `x`.
    fn get(&self, x: f64) -> Option<f64> {
        self.floats.get(&self.prec.bucket(x)).copied()
    }

    /// Searches for an existing bucket value for a float that is approximately
    /// equal to `x`, and returns the existing float and its bucket if found. If
    /// none is found, inserts it and returns itself and its bucket.
    fn insert(&mut self, x: f64) -> (f64, u64) {
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

    /// Returns the number of occupied buckets in the pool.
    pub fn bucket_count(&self) -> usize {
        self.floats.len()
    }

    /// Iterates over all floats in the pool, in an undefined order.
    pub fn iter(&self) -> Iter<'_> {
        Iter(FloatIterInner {
            prec: self.prec,
            inner: self.floats.iter().map(|(&k, &v)| (k, v)),
        })
    }
}

impl IntoIterator for FloatPool {
    type Item = f64;

    type IntoIter = IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter(FloatIterInner {
            prec: self.prec,
            inner: self.floats.into_iter(),
        })
    }
}

impl<'a> IntoIterator for &'a FloatPool {
    type Item = f64;

    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[derive(Debug)]
struct FloatIterInner<I> {
    prec: Precision,
    inner: I,
}

impl<I: Iterator<Item = (u64, f64)>> FloatIterInner<I> {
    fn next(&mut self) -> Option<f64> {
        self.inner
            .find(|&(k, v)| self.prec.bucket(v) == k)
            .map(|(_k, v)| v)
    }
}

/// Owning iterator over floats in a [`FloatPool`].
#[derive(Debug)]
pub struct IntoIter(FloatIterInner<hash_map::IntoIter<u64, f64>>);

impl Iterator for IntoIter {
    type Item = f64;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

impl FusedIterator for IntoIter {}

type CopiedHashMapIter<'a> =
    std::iter::Map<hash_map::Iter<'a, u64, f64>, fn((&'a u64, &'a f64)) -> (u64, f64)>;

/// Iterator over floats in a [`FloatPool`].
#[derive(Debug)]
pub struct Iter<'a>(FloatIterInner<CopiedHashMapIter<'a>>);

impl Iterator for Iter<'_> {
    type Item = f64;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

impl FusedIterator for Iter<'_> {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_float_interning() {
        let mut interner = FloatPool::new(Precision::absolute(3)); // bucket size = 0.125
        assert_eq!(1.0, interner.intern(1.0));
        assert_eq!(1.0, interner.intern(1.1));
        assert_eq!(2.1, interner.intern(2.1));
        assert_eq!(2.1, interner.intern(1.9));
        assert_eq!(0.73, interner.intern(0.73));
        assert_eq!(0.73, interner.intern(0.8));
        assert_eq!(0.49, interner.intern(0.49));
    }

    #[test]
    fn test_struct_float_interning() {
        let mut interner = FloatPool::new(Precision::absolute(3)); // bucket size = 0.125
        assert_eq!([0.0, 0.0, 0.5], interner.intern([0.1, 0.0, 0.5]));
        assert_eq!([0.5, 0.8, 0.8], interner.intern([0.6, 0.8, 0.75]));
    }
}
