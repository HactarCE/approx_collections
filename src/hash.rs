//! Traits for hashing floats using [`FloatInterner`] to ensure that
//! approximately-equal floats always hash to the same value.

use std::hash::{BuildHasher, Hash, Hasher};

use crate::intern::FloatInterner;

pub(crate) struct InterningApproxHasher<S: BuildHasher, I> {
    hasher: S::Hasher,
    intern: I,
    failed: bool,
}
impl<S: BuildHasher, I> InterningApproxHasher<S, I> {
    pub fn new(hash_builder: &S, intern: I) -> Self {
        Self {
            hasher: hash_builder.build_hasher(),
            intern,
            failed: false,
        }
    }
}

impl<S: BuildHasher, I> Hasher for InterningApproxHasher<S, I> {
    fn finish(&self) -> u64 {
        unreachable!("call try_finish() instead");
    }

    fn write(&mut self, bytes: &[u8]) {
        if !self.failed {
            self.hasher.write(bytes);
        }
    }
}

/// Hasher that can hash floating-point numbers (via approximate interning) in
/// addition to arbitrary streams of bytes.
///
/// Unlike [`Hasher`], hashing with approximate equality may fail. This may
/// happen when trying to look up a value in a data structure that does not
/// contain a similar float.
pub trait ApproxHasher: Hasher {
    /// Error type returned if a float is not found.
    type Error;

    /// Interns and then writes a 64-bit float.
    fn write_f64(&mut self, x: f64);
    /// Interns and then writes a 32-bit float. This is automatically
    /// implemented by first converting to a 64-bit float.
    fn write_f32(&mut self, x: f32) {
        self.write_f64(x as f64);
    }
    /// Finishes hashing, or returns [`Self::Error`] if interner is read-only
    /// and a similar float was not found.
    fn try_finish(&self) -> Result<u64, Self::Error>;
}

impl<S: BuildHasher> ApproxHasher for InterningApproxHasher<S, &'_ mut FloatInterner> {
    type Error = std::convert::Infallible;

    fn write_f64(&mut self, x: f64) {
        let (_, bucket) = self.intern.insert(x);
        bucket.hash(&mut self.hasher);
    }
    fn try_finish(&self) -> Result<u64, Self::Error> {
        Ok(self.hasher.finish())
    }
}

impl<S: BuildHasher> ApproxHasher for InterningApproxHasher<S, &'_ FloatInterner> {
    type Error = ();

    fn write_f64(&mut self, x: f64) {
        match self.intern.get(x) {
            Some((_, bucket)) => bucket.hash(&mut self.hasher),
            None => self.failed = true,
        }
    }
    fn try_finish(&self) -> Result<u64, Self::Error> {
        if self.failed {
            Err(())
        } else {
            Ok(self.hasher.finish())
        }
    }
}

/// Trait for values that can be hashed using a combination of approximate
/// floating-point hashing (via interning) and conventional byte hashing.
pub trait ApproxHash {
    /// Feeds this value into the given [`ApproxHasher`].
    ///
    /// [`ApproxHasher`]s always also implement [`Hash`], so types without
    /// floating-point numbers can be conventionally hashed.
    fn approx_hash<H: ApproxHasher>(&self, state: &mut H);
}
impl ApproxHash for f64 {
    fn approx_hash<H: ApproxHasher>(&self, state: &mut H) {
        state.write_f64(*self);
    }
}
impl ApproxHash for f32 {
    fn approx_hash<H: ApproxHasher>(&self, state: &mut H) {
        state.write_f32(*self);
    }
}
impl<T: ApproxHash> ApproxHash for [T] {
    fn approx_hash<H: ApproxHasher>(&self, state: &mut H) {
        self.len().hash(state);
        for x in self {
            x.approx_hash(state);
        }
    }
}
impl<T: ApproxHash, const N: usize> ApproxHash for [T; N] {
    fn approx_hash<H: ApproxHasher>(&self, state: &mut H) {
        for x in self {
            x.approx_hash(state);
        }
    }
}
