//! Common traits related to approximate equality.

use std::cmp::Ordering;

use crate::Precision;
pub use crate::hash::{ApproxHash, ApproxHasher};

/// Trait for types that can be approximately compared for equality with each
/// other.
pub trait ApproxEq: std::fmt::Debug {
    /// Returns whether `self` and `other` are approximately equal according to
    /// the precision.
    fn approx_eq(&self, other: &Self, prec: Precision) -> bool;
}
impl ApproxEq for f64 {
    fn approx_eq(&self, other: &Self, prec: Precision) -> bool {
        prec.f64_eq(*self, *other)
    }
}
impl ApproxEq for f32 {
    fn approx_eq(&self, other: &Self, prec: Precision) -> bool {
        prec.f32_eq(*self, *other)
    }
}
impl<T: ApproxEq> ApproxEq for [T] {
    fn approx_eq(&self, other: &Self, prec: Precision) -> bool {
        self.len() == other.len() && std::iter::zip(self, other).all(|(a, b)| a.approx_eq(b, prec))
    }
}
impl<T: ApproxEq, const N: usize> ApproxEq for [T; N] {
    fn approx_eq(&self, other: &Self, prec: Precision) -> bool {
        std::iter::zip(self, other).all(|(a, b)| a.approx_eq(b, prec))
    }
}
impl<T: ApproxEq> ApproxEq for &T {
    fn approx_eq(&self, other: &Self, prec: Precision) -> bool {
        T::approx_eq(self, other, prec)
    }
}

/// Trait for types that can be approximately compared to some zero value.
pub trait ApproxEqZero {
    /// Returns whether `self` is approximately zero according to the precision.
    ///
    /// This should have the same behavior as [`ApproxEq::approx_eq()`] with
    /// zero as one of the arguments, but may be more optimized.
    fn approx_eq_zero(&self, prec: Precision) -> bool;
}
impl ApproxEqZero for f64 {
    fn approx_eq_zero(&self, prec: Precision) -> bool {
        prec.f64_eq_zero(*self)
    }
}
impl ApproxEqZero for f32 {
    fn approx_eq_zero(&self, prec: Precision) -> bool {
        prec.f64_eq_zero(*self as f64)
    }
}
impl<T: ApproxEqZero> ApproxEqZero for [T] {
    fn approx_eq_zero(&self, prec: Precision) -> bool {
        self.iter().all(|x| x.approx_eq_zero(prec))
    }
}
impl<T: ApproxEqZero, const N: usize> ApproxEqZero for [T; N] {
    fn approx_eq_zero(&self, prec: Precision) -> bool {
        self.iter().all(|x| x.approx_eq_zero(prec))
    }
}
impl<T: ApproxEqZero> ApproxEqZero for &T {
    fn approx_eq_zero(&self, prec: Precision) -> bool {
        T::approx_eq_zero(self, prec)
    }
}

/// Trait for types that can be approximately ordered with each other.
///
/// This ordering should be total.
pub trait ApproxOrd: ApproxEq {
    /// Returns the ordering relation between `self` and `other` according to
    /// the precision.
    fn approx_cmp(&self, other: &Self, prec: Precision) -> Ordering;
}
impl ApproxOrd for f64 {
    fn approx_cmp(&self, other: &Self, prec: Precision) -> Ordering {
        match self.approx_eq(other, prec) {
            true => Ordering::Equal,
            false => self.total_cmp(other),
        }
    }
}
impl ApproxOrd for f32 {
    fn approx_cmp(&self, other: &Self, prec: Precision) -> Ordering {
        match self.approx_eq(other, prec) {
            true => Ordering::Equal,
            false => self.total_cmp(other),
        }
    }
}
impl<T: ApproxOrd> ApproxOrd for [T] {
    fn approx_cmp(&self, other: &Self, prec: Precision) -> Ordering {
        std::iter::zip(self, other)
            .map(|(a, b)| a.approx_cmp(b, prec))
            .find(|&ord| ord != Ordering::Equal)
            .unwrap_or_else(|| self.len().cmp(&other.len()))
    }
}
impl<T: ApproxOrd, const N: usize> ApproxOrd for [T; N] {
    fn approx_cmp(&self, other: &Self, prec: Precision) -> Ordering {
        std::iter::zip(self, other)
            .map(|(a, b)| a.approx_cmp(b, prec))
            .find(|&ord| ord != Ordering::Equal)
            .unwrap_or(Ordering::Equal)
    }
}
impl<T: ApproxOrd> ApproxOrd for &T {
    fn approx_cmp(&self, other: &Self, prec: Precision) -> Ordering {
        T::approx_cmp(self, other, prec)
    }
}

/// Trait for values that contain `f32` or `f64`.
///
/// This is used for interning all floats in a structure, and may be used for
/// implementing [`ApproxEq`], [`ApproxEqZero`], and [`ApproxOrd`].
pub trait VisitFloats {
    /// Calls `f` on all float values in `self`.
    fn visit_floats(&self, f: impl FnMut(&f64));
    /// Calls `f` on mutable references to all float values in `self`.
    fn visit_floats_mut(&mut self, f: impl FnMut(&mut f64));
}
impl VisitFloats for f64 {
    fn visit_floats(&self, mut f: impl FnMut(&f64)) {
        f(self)
    }

    fn visit_floats_mut(&mut self, mut f: impl FnMut(&mut f64)) {
        f(self)
    }
}
impl VisitFloats for f32 {
    fn visit_floats(&self, mut f: impl FnMut(&f64)) {
        let x = *self as f64;
        f(&x);
    }

    fn visit_floats_mut(&mut self, mut f: impl FnMut(&mut f64)) {
        let mut x = *self as f64;
        f(&mut x);
        *self = x as f32;
    }
}
impl<T: VisitFloats> VisitFloats for [T] {
    fn visit_floats(&self, mut f: impl FnMut(&f64)) {
        self.iter().for_each(|x| x.visit_floats(&mut f));
    }

    fn visit_floats_mut(&mut self, mut f: impl FnMut(&mut f64)) {
        self.iter_mut().for_each(|x| x.visit_floats_mut(&mut f));
    }
}
impl<T: VisitFloats, const N: usize> VisitFloats for [T; N] {
    fn visit_floats(&self, mut f: impl FnMut(&f64)) {
        self.iter().for_each(|x| x.visit_floats(&mut f));
    }

    fn visit_floats_mut(&mut self, mut f: impl FnMut(&mut f64)) {
        self.iter_mut().for_each(|x| x.visit_floats_mut(&mut f));
    }
}
