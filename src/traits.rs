//! Common traits related to approximate equality.

use std::{
    cmp::Ordering,
    hash::{Hash, Hasher},
};

use crate::Precision;

macro_rules! impl_for_tuples {
    ($impl_macro:ident) => {
        $impl_macro!(T0; 0);
        $impl_macro!(T0, T1; 0, 1);
        $impl_macro!(T0, T1, T2; 0, 1, 2);
        $impl_macro!(T0, T1, T2, T3; 0, 1, 2, 3);
        $impl_macro!(T0, T1, T2, T3, T4; 0, 1, 2, 3, 4);
        $impl_macro!(T0, T1, T2, T3, T4, T5; 0, 1, 2, 3, 4, 5);
        $impl_macro!(T0, T1, T2, T3, T4, T5, T6; 0, 1, 2, 3, 4, 5, 6);
        $impl_macro!(T0, T1, T2, T3, T4, T5, T6, T7; 0, 1, 2, 3, 4, 5, 6, 7);
        $impl_macro!(T0, T1, T2, T3, T4, T5, T6, T7, T8; 0, 1, 2, 3, 4, 5, 6, 7, 8);
        $impl_macro!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9);
    };
}

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
impl<T: ApproxEq> ApproxEq for Option<T> {
    fn approx_eq(&self, other: &Self, prec: Precision) -> bool {
        match (self, other) {
            (None, None) => true,
            (None, Some(_)) | (Some(_), None) => false,
            (Some(a), Some(b)) => a.approx_eq(b, prec),
        }
    }
}
macro_rules! impl_approx_eq_for_tuple {
    ($($generic_param:ident),+; $($index:tt),+) => {
        impl<$($generic_param: ApproxEq,)+> ApproxEq for ($($generic_param,)+) {
            fn approx_eq(&self, other: &Self, prec: Precision) -> bool {
                $(self.$index.approx_eq(&other.$index, prec))&&+
            }
        }
    };
}
impl_for_tuples!(impl_approx_eq_for_tuple);

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
macro_rules! impl_approx_eq_zero_for_tuple {
    ($($generic_param:ident),+; $($index:tt),+) => {
        impl<$($generic_param: ApproxEqZero,)+> ApproxEqZero for ($($generic_param,)+) {
            fn approx_eq_zero(&self, prec: Precision) -> bool {
                $(self.$index.approx_eq_zero(prec))&&+
            }
        }
    };
}
impl_for_tuples!(impl_approx_eq_zero_for_tuple);

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
impl<T: ApproxOrd> ApproxOrd for Option<T> {
    fn approx_cmp(&self, other: &Self, prec: Precision) -> Ordering {
        match (self, other) {
            (None, None) => Ordering::Equal,
            (None, Some(_)) => Ordering::Less,
            (Some(_), None) => Ordering::Greater,
            (Some(a), Some(b)) => a.approx_cmp(b, prec),
        }
    }
}
macro_rules! impl_approx_ord_for_tuple {
    ($($generic_param:ident),+; $($index:tt),+) => {
        impl<$($generic_param: ApproxOrd,)+> ApproxOrd for ($($generic_param,)+) {
            fn approx_cmp(&self, other: &Self, prec: Precision) -> Ordering {
                $(
                    match self.$index.approx_cmp(&other.$index, prec) {
                        Ordering::Equal => (),
                        nonequal => return nonequal,
                    }
                )+
                Ordering::Equal
            }
        }
    };
}
impl_for_tuples!(impl_approx_ord_for_tuple);

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
macro_rules! impl_approx_cmp_zero_for_tuple {
    ($($generic_param:ident),+; $($index:tt),+) => {
        impl<$($generic_param: ApproxCmpZero,)+> ApproxCmpZero for ($($generic_param,)+) {
            fn approx_cmp_zero(&self, prec: Precision) -> Ordering {
                $(
                    match self.$index.approx_cmp_zero(prec) {
                        Ordering::Equal => (),
                        nonequal => return nonequal,
                    }
                )+
                Ordering::Equal
            }
        }
    };
}
impl_for_tuples!(impl_approx_cmp_zero_for_tuple);

///Trait for types that can be interned (component-wise) in a [`crate::FloatPool`].
pub trait ApproxInternable {
    /// Interns every float in the object by calling `f`.
    fn intern_floats<F: FnMut(&mut f64)>(&mut self, f: &mut F);
}

impl ApproxInternable for f64 {
    fn intern_floats<F: FnMut(&mut f64)>(&mut self, f: &mut F) {
        f(self)
    }
}

impl ApproxInternable for f32 {
    fn intern_floats<F: FnMut(&mut f64)>(&mut self, f: &mut F) {
        let mut x = *self as f64;
        f(&mut x);
        *self = x as f32;
    }
}

impl<T: ApproxInternable> ApproxInternable for [T] {
    fn intern_floats<F: FnMut(&mut f64)>(&mut self, f: &mut F) {
        self.into_iter().for_each(|x| x.intern_floats(f));
    }
}

impl<T: ApproxInternable, const N: usize> ApproxInternable for [T; N] {
    fn intern_floats<F: FnMut(&mut f64)>(&mut self, f: &mut F) {
        <[T]>::intern_floats(self, f);
    }
}

impl<T: ApproxInternable> ApproxInternable for Vec<T> {
    fn intern_floats<F: FnMut(&mut f64)>(&mut self, f: &mut F) {
        <[T]>::intern_floats(self, f);
    }
}
impl<T: ApproxInternable> ApproxInternable for Box<T> {
    fn intern_floats<F: FnMut(&mut f64)>(&mut self, f: &mut F) {
        T::intern_floats(self, f);
    }
}

impl<T: ApproxInternable> ApproxInternable for &mut T {
    fn intern_floats<F: FnMut(&mut f64)>(&mut self, f: &mut F) {
        T::intern_floats(self, f);
    }
}

impl<T: ApproxInternable> ApproxInternable for Option<T> {
    fn intern_floats<F: FnMut(&mut f64)>(&mut self, f: &mut F) {
        if let Some(inner) = self {
            inner.intern_floats(f);
        }
    }
}
/// Trait for types that can be stored in a [`crate::ApproxHashMap`].
pub trait ApproxHash: ApproxInternable {
    /// Returns whether `self` and `other` are exactly equal, assuming both have
    /// already been interned using `intern_floats()`.
    fn interned_eq(&self, other: &Self) -> bool;

    /// Hashes the object, assuming it has already been interned using
    /// `intern_floats()`.
    fn interned_hash<H: Hasher>(&self, state: &mut H);
}
impl ApproxHash for f64 {
    fn interned_eq(&self, other: &Self) -> bool {
        self.to_bits() == other.to_bits()
    }

    fn interned_hash<H: Hasher>(&self, state: &mut H) {
        self.to_bits().hash(state);
    }
}
impl ApproxHash for f32 {
    fn interned_eq(&self, other: &Self) -> bool {
        self.to_bits() == other.to_bits()
    }

    fn interned_hash<H: Hasher>(&self, state: &mut H) {
        self.to_bits().hash(state);
    }
}
impl<T: ApproxHash> ApproxHash for [T] {
    fn interned_eq(&self, other: &Self) -> bool {
        self.len() == other.len() && std::iter::zip(self, other).all(|(a, b)| a.interned_eq(b))
    }

    fn interned_hash<H: Hasher>(&self, state: &mut H) {
        self.len().hash(state);
        self.iter().for_each(|x| x.interned_hash(state));
    }
}
impl<T: ApproxHash, const N: usize> ApproxHash for [T; N] {
    fn interned_eq(&self, other: &Self) -> bool {
        <[T]>::interned_eq(self, other)
    }

    fn interned_hash<H: Hasher>(&self, state: &mut H) {
        <[T]>::interned_hash(self, state);
    }
}
impl<T: ApproxHash> ApproxHash for Vec<T> {
    fn interned_eq(&self, other: &Self) -> bool {
        <[T]>::interned_eq(self, other)
    }

    fn interned_hash<H: Hasher>(&self, state: &mut H) {
        <[T]>::interned_hash(self, state);
    }
}
impl<T: ApproxHash> ApproxHash for Box<T> {
    fn interned_eq(&self, other: &Self) -> bool {
        T::interned_eq(self, other)
    }

    fn interned_hash<H: Hasher>(&self, state: &mut H) {
        T::interned_hash(self, state);
    }
}
impl<T: ApproxHash> ApproxHash for &mut T {
    fn interned_eq(&self, other: &Self) -> bool {
        T::interned_eq(self, other)
    }

    fn interned_hash<H: Hasher>(&self, state: &mut H) {
        T::interned_hash(self, state);
    }
}
impl<T: ApproxHash> ApproxHash for Option<T> {
    fn interned_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (None, None) => true,
            (None, Some(_)) | (Some(_), None) => false,
            (Some(a), Some(b)) => a.interned_eq(b),
        }
    }

    fn interned_hash<H: Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        if let Some(inner) = self {
            inner.interned_hash(state);
        }
    }
}
macro_rules! impl_approx_internable_for_tuple {
    ($($generic_param:ident),+; $($index:tt),+) => {
        impl<$($generic_param: ApproxInternable,)+> ApproxInternable for ($($generic_param,)+) {
            fn intern_floats<F: FnMut(&mut f64)>(&mut self, f: &mut F) {
                $(self.$index.intern_floats(f);)+
            }
        }
    };
}

macro_rules! impl_approx_hash_for_tuple {
    ($($generic_param:ident),+; $($index:tt),+) => {
        impl<$($generic_param: ApproxHash,)+> ApproxHash for ($($generic_param,)+) {
            fn interned_eq(&self, other: &Self) -> bool {
                $(self.$index.interned_eq(&other.$index))&&+
            }

            fn interned_hash<H: Hasher>(&self, state: &mut H) {
                $(self.$index.interned_hash(state);)+
            }
        }
    };
}
impl_for_tuples!(impl_approx_internable_for_tuple);
impl_for_tuples!(impl_approx_hash_for_tuple);
