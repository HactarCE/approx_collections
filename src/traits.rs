//! Common traits related to approximate equality.

use std::{
    cmp::Ordering,
    hash::{Hash, Hasher},
};

use crate::Precision;

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
        <[T]>::approx_eq(self, other, prec)
    }
}
impl<T: ApproxEq> ApproxEq for Vec<T> {
    fn approx_eq(&self, other: &Self, prec: Precision) -> bool {
        <[T]>::approx_eq(self, other, prec)
    }
}
impl<T: ApproxEq> ApproxEq for Box<T> {
    fn approx_eq(&self, other: &Self, prec: Precision) -> bool {
        T::approx_eq(self, other, prec)
    }
}
impl<T: ApproxEq + ?Sized> ApproxEq for &T {
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
        <[T]>::approx_eq_zero(self, prec)
    }
}
impl<T: ApproxEqZero> ApproxEqZero for Vec<T> {
    fn approx_eq_zero(&self, prec: Precision) -> bool {
        <[T]>::approx_eq_zero(self, prec)
    }
}
impl<T: ApproxEqZero> ApproxEqZero for Box<T> {
    fn approx_eq_zero(&self, prec: Precision) -> bool {
        T::approx_eq_zero(self, prec)
    }
}
impl<T: ApproxEqZero + ?Sized> ApproxEqZero for &T {
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
        <[T]>::approx_cmp(self, other, prec)
    }
}
impl<T: ApproxOrd> ApproxOrd for Vec<T> {
    fn approx_cmp(&self, other: &Self, prec: Precision) -> Ordering {
        <[T]>::approx_cmp(self, other, prec)
    }
}
impl<T: ApproxOrd> ApproxOrd for Box<T> {
    fn approx_cmp(&self, other: &Self, prec: Precision) -> Ordering {
        T::approx_cmp(self, other, prec)
    }
}
impl<T: ApproxOrd + ?Sized> ApproxOrd for &T {
    fn approx_cmp(&self, other: &Self, prec: Precision) -> Ordering {
        T::approx_cmp(self, other, prec)
    }
}

pub trait ApproxCmpZero: ApproxEqZero {
    fn approx_cmp_zero(&self, prec: Precision) -> Ordering;
}
impl ApproxCmpZero for f32 {
    fn approx_cmp_zero(&self, prec: Precision) -> Ordering {
        (*self as f64).approx_cmp_zero(prec)
    }
}
impl ApproxCmpZero for f64 {
    fn approx_cmp_zero(&self, prec: Precision) -> Ordering {
        if self.approx_eq_zero(prec) {
            Ordering::Equal
        } else if self.is_sign_positive() {
            Ordering::Greater
        } else {
            Ordering::Less
        }
    }
}
impl<T: ApproxCmpZero> ApproxCmpZero for Box<T> {
    fn approx_cmp_zero(&self, prec: Precision) -> Ordering {
        T::approx_cmp_zero(self, prec)
    }
}
impl<T: ApproxCmpZero> ApproxCmpZero for &T {
    fn approx_cmp_zero(&self, prec: Precision) -> Ordering {
        T::approx_cmp_zero(self, prec)
    }
}

/// Trait for types that can be stored in a [`crate::ApproxHashMap`].
pub trait ApproxHash {
    /// Interns every float in the object by calling `f`.
    fn intern_floats<F: FnMut(&mut f64)>(&mut self, f: &mut F);

    /// Returns whether `self` and `other` are exactly equal, assuming both have
    /// already been interned using `intern_floats()`.
    fn interned_eq(&self, other: &Self) -> bool;

    /// Hashes the object, assuming it has already been interned using
    /// `intern_floats()`.
    fn interned_hash<H: Hasher>(&self, state: &mut H);
}
impl ApproxHash for f64 {
    fn intern_floats<F: FnMut(&mut f64)>(&mut self, f: &mut F) {
        f(self)
    }

    fn interned_eq(&self, other: &Self) -> bool {
        self.to_bits() == other.to_bits()
    }

    fn interned_hash<H: Hasher>(&self, state: &mut H) {
        self.to_bits().hash(state);
    }
}
impl ApproxHash for f32 {
    fn intern_floats<F: FnMut(&mut f64)>(&mut self, f: &mut F) {
        let mut x = *self as f64;
        f(&mut x);
        *self = x as f32;
    }

    fn interned_eq(&self, other: &Self) -> bool {
        self.to_bits() == other.to_bits()
    }

    fn interned_hash<H: Hasher>(&self, state: &mut H) {
        self.to_bits().hash(state);
    }
}
impl<T: ApproxHash> ApproxHash for [T] {
    fn intern_floats<F: FnMut(&mut f64)>(&mut self, f: &mut F) {
        self.into_iter().for_each(|x| x.intern_floats(f));
    }

    fn interned_eq(&self, other: &Self) -> bool {
        self.len() == other.len() && std::iter::zip(self, other).all(|(a, b)| a.interned_eq(b))
    }

    fn interned_hash<H: Hasher>(&self, state: &mut H) {
        self.len().hash(state);
        self.iter().for_each(|x| x.interned_hash(state));
    }
}
impl<T: ApproxHash, const N: usize> ApproxHash for [T; N] {
    fn intern_floats<F: FnMut(&mut f64)>(&mut self, f: &mut F) {
        <[T]>::intern_floats(self, f);
    }

    fn interned_eq(&self, other: &Self) -> bool {
        <[T]>::interned_eq(self, other)
    }

    fn interned_hash<H: Hasher>(&self, state: &mut H) {
        <[T]>::interned_hash(self, state);
    }
}
impl<T: ApproxHash> ApproxHash for Vec<T> {
    fn intern_floats<F: FnMut(&mut f64)>(&mut self, f: &mut F) {
        <[T]>::intern_floats(self, f);
    }

    fn interned_eq(&self, other: &Self) -> bool {
        <[T]>::interned_eq(self, other)
    }

    fn interned_hash<H: Hasher>(&self, state: &mut H) {
        <[T]>::interned_hash(self, state);
    }
}
impl<T: ApproxHash> ApproxHash for Box<T> {
    fn intern_floats<F: FnMut(&mut f64)>(&mut self, f: &mut F) {
        T::intern_floats(self, f);
    }

    fn interned_eq(&self, other: &Self) -> bool {
        T::interned_eq(self, other)
    }

    fn interned_hash<H: Hasher>(&self, state: &mut H) {
        T::interned_hash(self, state);
    }
}
impl<T: ApproxHash> ApproxHash for &mut T {
    fn intern_floats<F: FnMut(&mut f64)>(&mut self, f: &mut F) {
        T::intern_floats(self, f);
    }

    fn interned_eq(&self, other: &Self) -> bool {
        T::interned_eq(self, other)
    }

    fn interned_hash<H: Hasher>(&self, state: &mut H) {
        T::interned_hash(self, state);
    }
}
