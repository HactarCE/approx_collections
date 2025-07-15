//! Precision level for comparing floats.

use std::cmp::Ordering;

use crate::{ApproxEq, ApproxEqZero, ApproxOrd};

/// Sign bit
const SIGN_MASK: u64 = 0x8000_0000_0000_0000;
/// Exponent mask
const EXPONENT_MASK: u64 = 0x7ff0_0000_0000_0000;
/// Number of bits in the representation of the mantissa
const MANTISSA_BITS: u32 = f64::MANTISSA_DIGITS - 1;

/// Maximum value for `absolute` precision. This means the minimum possible
/// absolute bucket size is [`f64::MIN_POSITIVE`].
pub const MAX_ABSOLUTE: i32 = 1 - f64::MIN_EXP;
/// Minimum value for `absolute` precision. This means the minimum possible
/// absolute bucket size is [`f64::MAX`]; i.e., all floats are in the same
/// bucket.
pub const MIN_ABSOLUTE: i32 = -f64::MAX_EXP;
/// Maximum value for `relative` precision. This means the minimum possible
/// relative bucket size is [`f64::EPSILON`]; i.e., each float is in its own
/// bucket (except where limited by `absolute`).
pub const MAX_RELATIVE: u32 = MANTISSA_BITS;

/// Almost-total order on floats using relative comparison, sorting floats into
/// buckets.
///
/// Each float spans three buckets so that for any value _n_ there is a value
/// _ε_ such that all values within _n±ε_ are equal to _n_ and all values
/// outside _n±2ε_ are not equal to _n_. _ε_ varies (relatively) smoothly over
/// all values according to the parameters of this struct.
///
/// This has the following properties, given any values _a_ and _b_:
///
/// - Reflexivity: _a = a_
/// - Weak transitivity:
///     - if _a ≤ b_ and _b < c_ then _a < c_
///     - if _a < b_ and _b ≤ c_ then _a < c_
/// - Antisymmetry: if _a ≤ b_ and _b ≤ a_ then _a = b_
/// - Strong connectivity: _a ≤ b_ or _b ≤ a_
///
/// This is the same as a [total order] **except** that the transitivity
/// requirement is weaker. A total order requires that if _a ≤ b_ and _b ≤ c_
/// then _a ≤ c_, but this property is **not** necessarily true.
///
/// [total order]: https://en.wikipedia.org/wiki/Total_order
///
/// # What parmeters do I use?
///
/// `Precision::default()` is a good place to start. It's equivalent to
/// `Precision::new_simple(26)`, which uses approximately half the precision of
/// a 64-bit float and ensures all comparisons are accurate to within
/// ~1/20,000,000. (This is a gross oversimplification.)
///
/// # How do I tune the parameters?
///
/// - If you're getting errors where numbers **should be equivalent but are
///   considered distinct**, then use [`Precision::new_simple()`] with a
///   **smaller** number
/// - If you're getting errors where numbers **should be distinct but are
///   considered equivalent**, then use [`Precision::new_simple()`] with a
///   **larger** number
///
/// If there is a wide range of values that works, I recommend selecting a
/// number in the middle of that range.
///
/// You can change `absolute` to tune the behavior for small numbers and
/// `relative` to tune the behavior for large numbers.
/// [`Precision::new_simple()`] uses the same value for both.
///
/// If you are curious about the details, continue reading.
///
/// # What are `absolute` and `relative`?
///
/// `absolute` and `relative` are both upper bounds on precision; numbers are
/// truncated according to whichever them demands less precision.
///
/// - `absolute` determines behavior for small numbers
/// - `relative` determines behavior for large numbers
///
/// - If either parameter is **more negative**, there will be **fewer larger**
///   buckets
/// - If either parameter is **more positive**, there will be **more smaller**
///   buckets
///
/// ## `absolute`
///
/// `absolute` determines you how many base-2 digits are allowed in the
/// fractional part (i.e., after the [radix point]).
///
/// [radix point]: https://en.wikipedia.org/wiki/Decimal_separator#Radix_point
///
/// - To truncate to integers, use `absolute = 0`
/// - To truncate to multiples of 1/32, use `absolute = 5`
/// - To truncate to multiples of 32, use `absolute = -5`
///
/// As an optimization, all values `absolute > 1023` are equivalent to `absolute
/// = 1023` so that subnormals are always in the same bucket as `0.0`.
///
/// All values of `absolute < -1023` are equivalent to `absolute = -1023`.
///
/// ## `relative`
///
/// `relative` determines you how many total base-2 digits of precision are used
/// to determine the bucket for a float, not including the leading `1` (since
/// all nonzero binary numbers start with a `1`).
///
/// - To compare based only on the exponent, use `relative = 0`
/// - To compare using `f16` precision, use `relative = 10`
/// - To compare using `f32` precision, use `relative = 23`
/// - To compare using `f64` precision, use `relative = 52`
///
/// `f64` only has 52 bits of precision, so all values `relative > 52` are
/// equivalent to `relative = 52`.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Precision {
    // #[cfg_attr(
    //     test,
    //     proptest(strategy = "1..=(MAX_ABSOLUTE - MIN_ABSOLUTE + 1) as u32")
    // )]
    min_exponent: u32,
    // #[cfg_attr(test, proptest(strategy = "0..=MAX_RELATIVE"))]
    mantissa_bits: u32,
}

impl Default for Precision {
    fn default() -> Self {
        Self::new_simple(26)
    }
}

impl Precision {
    /// Default `Precision` which uses about half the precision of an `f64`,
    /// which is still more than an `f32`.
    pub const DEFAULT: Self = Self::new_simple(26);

    /// Constructs a `Precision` using the same value for `absolute` and
    /// `relative`.
    ///
    /// See [`Precision`] for details about what `absolute` and `relative` do.
    pub const fn new_simple(parameter: u32) -> Self {
        // `try_from()` is not `const fn`
        let absolute = if parameter > i32::MAX as u32 {
            i32::MAX
        } else {
            parameter as i32
        };

        let relative = parameter;

        Self::new(absolute, relative)
    }

    /// Constructs a `Precision` where all buckets have the same absolute size.
    pub const fn absolute(absolute: i32) -> Self {
        Self::new(absolute, MAX_RELATIVE)
    }

    /// Constructs a `Precision` where all buckets have the same relative size
    /// proportional to the next-smallest power of 2.
    pub const fn relative(relative: u32) -> Self {
        Self::new(MAX_ABSOLUTE, relative)
    }

    /// Constructs a `Precision` with a value for `absolute` and a value for
    /// `relative`.
    ///
    /// See [`Precision`] for details about what `absolute` and `relative` do.
    pub const fn new(absolute: i32, relative: u32) -> Self {
        let min_exponent = match absolute {
            ..MIN_ABSOLUTE => (MAX_ABSOLUTE - MIN_ABSOLUTE) as u32 + 1,
            MAX_ABSOLUTE.. => 1,
            _ => MAX_ABSOLUTE.saturating_sub(absolute) as u32 + 1,
        };

        Self {
            min_exponent,
            mantissa_bits: relative,
        }
    }

    /// Compares two floating-point numbers for equality.
    pub(crate) fn f32_eq(self, a: f32, b: f32) -> bool {
        self.f64_eq(a as f64, b as f64)
    }
    /// Compares two floating-point numbers for equality.
    pub(crate) fn f64_eq(self, a: f64, b: f64) -> bool {
        if a == b {
            return true;
        }

        let a_exp = f64_exponent(a);
        let b_exp = f64_exponent(b);
        if a_exp < self.min_exponent && b_exp < self.min_exponent {
            return true; // equal to zero
        }
        if (a_exp > self.min_exponent || b_exp > self.min_exponent) && a_exp.abs_diff(b_exp) > 1 {
            return false;
        }

        let a_bucket = self.bucket(a);
        let b_bucket = self.bucket(b);
        if a_bucket == b_bucket {
            return true;
        }
        let (a_lo, a_mid, a_hi) = self.nearby_buckets(a);
        a_mid == b_bucket || a_lo == Some(b_bucket) || a_hi == Some(b_bucket)
    }
    pub(crate) fn f64_eq_zero(self, n: f64) -> bool {
        let exp = f64_exponent(n);
        exp < self.min_exponent
            || (exp == self.min_exponent && self.buckets_near_zero().contains(&self.bucket(n)))
    }

    /// Returns the bitmask to determine the bucket for `f`.
    fn bucket_mask(self, f: f64) -> u64 {
        match f.classify() {
            // +INF, -INF, and each NaN gets its own bucket
            std::num::FpCategory::Nan | std::num::FpCategory::Infinite => u64::MAX,

            // zero and subnormal all share one bucket
            std::num::FpCategory::Zero | std::num::FpCategory::Subnormal => 0,

            std::num::FpCategory::Normal => {
                let exponent = f64_exponent(f);
                let Some(spare_mantissa_bits) = exponent.checked_sub(self.min_exponent) else {
                    return 0; // close to zero
                };

                let mantissa_bits_to_keep = MANTISSA_BITS
                    .min(spare_mantissa_bits)
                    .min(self.mantissa_bits);
                let mantissa_bits_to_drop = MANTISSA_BITS - mantissa_bits_to_keep;
                u64::MAX << mantissa_bits_to_drop
            }
        }
    }

    pub(crate) fn bucket(self, f: f64) -> u64 {
        f.to_bits() & self.bucket_mask(f)
    }

    /// Returns the bucket below `f`, the bucket containing `f`, and the bucket
    /// above `f`.
    pub(crate) fn nearby_buckets(self, f: f64) -> (Option<u64>, u64, Option<u64>) {
        let bucket_mask = self.bucket_mask(f);
        let bucket_containing = f.to_bits() & bucket_mask;
        if f.is_nan() {
            (None, bucket_containing, None)
        } else if f.is_infinite() {
            if f.is_sign_positive() {
                (Some(self.bucket(f64::MAX)), bucket_containing, None)
            } else {
                (None, bucket_containing, Some(self.bucket(f64::MIN)))
            }
        } else if bucket_mask == 0 {
            let [lo, mid, hi] = self.buckets_near_zero();
            (Some(lo), mid, Some(hi))
        } else {
            let closest_to_zero = f64::from_bits(bucket_containing);
            let farthest_from_zero = f64::from_bits(bucket_containing | !bucket_mask);
            let [lowest_in_bucket, highest_in_bucket] = if f.is_sign_positive() {
                [closest_to_zero, farthest_from_zero]
            } else {
                [farthest_from_zero, closest_to_zero]
            };
            (
                Some(self.bucket(lowest_in_bucket.next_down())),
                bucket_containing,
                Some(self.bucket(highest_in_bucket.next_up())),
            )
        }
    }

    fn buckets_near_zero(self) -> [u64; 3] {
        let bucket_above = (self.min_exponent as u64) << MANTISSA_BITS;
        let bucket_below = SIGN_MASK | bucket_above;
        [bucket_below, 0, bucket_above]
    }

    /// Compares `a` and `b` using `T::approx_eq()`.
    pub fn eq<T: ApproxEq>(self, a: T, b: T) -> bool {
        a.approx_eq(&b, self)
    }
    /// Compares `a` and `b` using `T::approx_cmp()`.
    pub fn cmp<T: ApproxOrd>(self, a: T, b: T) -> Ordering {
        a.approx_cmp(&b, self)
    }
    /// Compares `a` and `b` using `T::approx_cmp()` and returns whether `a < b`.
    pub fn lt<T: ApproxOrd>(self, a: T, b: T) -> bool {
        self.cmp(a, b) == Ordering::Less
    }
    /// Compares `a` and `b` using `T::approx_cmp()` and returns whether `a > b`.
    pub fn gt<T: ApproxOrd>(self, a: T, b: T) -> bool {
        self.cmp(a, b) == Ordering::Less
    }
    /// Compares `a` and `b` using `T::approx_cmp()` and returns whether `a <= b`.
    pub fn lt_eq<T: ApproxOrd>(self, a: T, b: T) -> bool {
        !self.gt(a, b)
    }
    /// Compares `a` and `b` using `T::approx_cmp()` and returns whether `a >= b`.
    pub fn gt_eq<T: ApproxOrd>(self, a: T, b: T) -> bool {
        !self.lt(a, b)
    }

    /// Returns whether `a` is approximately equal to zero.
    pub fn eq_zero<T: ApproxEqZero>(self, a: T) -> bool {
        a.approx_eq_zero(self)
    }
}

fn f64_exponent(f: f64) -> u32 {
    ((f.to_bits() & EXPONENT_MASK) >> MANTISSA_BITS) as u32
}

#[cfg(test)]
mod tests {
    use super::*;

    use proptest::prelude::*;

    #[cfg(test)]
    impl Arbitrary for Precision {
        type Parameters = ();

        fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
            (MIN_ABSOLUTE..=MAX_ABSOLUTE, 0..=MAX_RELATIVE)
                .prop_map(|(abs, rel)| Precision::new(abs, rel))
                .boxed()
        }

        type Strategy = BoxedStrategy<Self>;
    }

    #[proptest_macro::property_test]
    fn proptest_bucketing_idempotent(f: f64, absolute: i32, relative: u32) {
        let prec = Precision::new(absolute, relative);

        let b = prec.bucket(f);
        assert_eq!(b, prec.bucket(f64::from_bits(b)));
    }

    #[proptest_macro::property_test]
    fn proptest_nearby_buckets(f: f64, absolute: i32, relative: u32) {
        let prec = Precision::new(absolute, relative);

        let (lo, mid, hi) = prec.nearby_buckets(f);
        assert_ne!(lo, Some(mid));
        assert_ne!(hi, Some(mid));
        if f.is_nan() {
            assert_eq!(lo, None);
            assert_eq!(hi, None);
        } else if f.is_infinite() {
            assert!(Option::xor(lo, hi).is_some());
        } else {
            assert!(lo.is_some());
            assert!(hi.is_some());
        }
        if let Some(lo) = lo {
            let (_, should_be_lo, should_be_mid) = prec.nearby_buckets(f64::from_bits(lo));
            assert_eq!(should_be_lo, lo);
            assert_eq!(should_be_mid, Some(mid));

            let between_lo_and_mid =
                prec.bucket(f64::midpoint(f64::from_bits(lo), f64::from_bits(mid)));
            assert!(between_lo_and_mid == lo || between_lo_and_mid == mid);
        }
        if let Some(hi) = hi {
            let (should_be_mid, should_be_hi, _) = prec.nearby_buckets(f64::from_bits(hi));
            assert_eq!(should_be_hi, hi);
            assert_eq!(should_be_mid, Some(mid));

            let between_hi_and_mid =
                prec.bucket(f64::midpoint(f64::from_bits(hi), f64::from_bits(mid)));
            assert!(between_hi_and_mid == hi || between_hi_and_mid == mid);
        }
    }

    #[proptest_macro::property_test]
    fn proptest_buckets(f: f64, absolute: i32, relative: u32) {
        let prec = Precision::new(absolute, relative);

        if f.is_infinite() {
            let inf = match f.is_sign_positive() {
                true => f64::INFINITY,
                false => f64::NEG_INFINITY,
            };
            assert_eq!(prec.bucket(f), inf.to_bits());
        } else if f.is_nan() {
            assert_eq!(prec.bucket(f), f.to_bits());
        } else {
            let absolute_bucket_log = -(absolute.clamp(MIN_ABSOLUTE, MAX_ABSOLUTE) as f64);
            let relative_bucket_log =
                f.abs().log2().floor() - relative.clamp(0, MAX_RELATIVE) as f64;

            let bucket_size = f64::max(absolute_bucket_log, relative_bucket_log).exp2();

            let mut expected_bucket = (f / bucket_size).trunc() * bucket_size;

            if bucket_size == 0.0 || bucket_size.is_infinite() || expected_bucket == 0.0 {
                expected_bucket = 0.0
            }

            assert_eq!(prec.bucket(f), expected_bucket.to_bits());
        }
    }

    #[test]
    fn test_round_to_integer() {
        let prec = Precision::new(0, MAX_RELATIVE); // integer precision
        assert_eq!(prec.bucket(5.99), 5.0_f64.to_bits());
        assert_eq!(prec.bucket(-5.99), (-5.0_f64).to_bits());
        assert_eq!(prec.bucket(999.99), 999.0_f64.to_bits());
        assert_eq!(prec.bucket(-999.99), (-999.0_f64).to_bits());
        let second_largest_f64_integer = 9007199254740992.0;
        assert_eq!(
            prec.bucket(second_largest_f64_integer),
            second_largest_f64_integer.to_bits(),
        );
    }

    #[proptest_macro::property_test]
    fn proptest_every_float_gets_its_own_bucket_proptest(f: f64) {
        let prec = Precision::new(MAX_ABSOLUTE, MAX_RELATIVE);
        // Exponents ≤ MANTISSA_BITS are allowed to get rounded a bit
        if f.is_subnormal() {
            assert_eq!(prec.bucket(f), 0);
        } else if f64_exponent(f) > MANTISSA_BITS {
            assert_eq!(prec.bucket(f), f.to_bits())
        }
    }

    #[proptest_macro::property_test]
    fn proptest_sign_symmetry(f: f64, prec: Precision) {
        let bucket = prec.bucket(f);
        if bucket == 0 {
            assert_eq!(bucket, prec.bucket(-f));
        } else {
            assert_eq!(bucket ^ SIGN_MASK, prec.bucket(-f));
            assert_eq!((bucket & SIGN_MASK != 0), f.is_sign_negative());
        }
    }

    #[test]
    fn test_min_absolute_limit() {
        let prec = Precision::new(MIN_ABSOLUTE + 1, MAX_RELATIVE);
        assert_ne!(prec.bucket(f64::MAX), 0);
        assert_ne!(prec.bucket(-f64::MAX), 0);

        let prec = Precision::new(MIN_ABSOLUTE, MAX_RELATIVE);
        assert_eq!(prec.bucket(f64::MAX), 0);
        assert_eq!(prec.bucket(-f64::MAX), 0);

        let prec = Precision::new(MIN_ABSOLUTE - 1, MAX_RELATIVE);
        assert_eq!(prec.bucket(f64::MAX), 0);
        assert_eq!(prec.bucket(-f64::MAX), 0);
    }

    #[test]
    fn test_max_absolute_limit() {
        let f = f64::MIN_POSITIVE;

        let prec = Precision::new(MAX_ABSOLUTE, MAX_RELATIVE);
        assert_ne!(0, prec.bucket(f));
        assert_eq!(prec.bucket(f), prec.bucket(f * 1.5));
        assert_ne!(prec.bucket(f), prec.bucket(f * 2.0));
        assert_eq!(prec.buckets_near_zero(), [(-f).to_bits(), 0, f.to_bits()]);

        let prec = Precision::new(MAX_ABSOLUTE - 1, MAX_RELATIVE);
        assert_eq!(0, prec.bucket(f));
        assert_eq!(prec.bucket(f), prec.bucket(f * 1.5));
        assert_ne!(prec.bucket(f), prec.bucket(f * 2.0));
        assert_eq!(
            prec.buckets_near_zero(),
            [(f * -2.0).to_bits(), 0, (f * 2.0).to_bits()],
        );
    }
    #[proptest_macro::property_test]
    fn proptest_test_max_absolute_limit(f: f64, relative: u32) {
        let prec1 = Precision::new(MAX_ABSOLUTE, relative);
        let prec2 = Precision::new(MAX_ABSOLUTE + 1, relative);
        assert_eq!(prec1.bucket(f), prec2.bucket(f));
    }

    #[test]
    fn test_max_relative_limit() {
        let prec1 = Precision::new(MAX_ABSOLUTE, MAX_RELATIVE - 1);
        let prec2 = Precision::new(MAX_ABSOLUTE, MAX_RELATIVE);
        let f = 1.0_f64.next_down();
        assert_ne!(prec1.bucket(f), prec2.bucket(f));
    }
    #[proptest_macro::property_test]
    fn proptest_max_relative_limit(f: f64, absolute: i32) {
        let prec1 = Precision::new(absolute, MAX_RELATIVE);
        let prec2 = Precision::new(absolute, MAX_RELATIVE + 1);
        assert_eq!(prec1.bucket(f), prec2.bucket(f));
    }

    #[proptest_macro::property_test]
    fn proptest_symmetric_eq(a: f64, b: f64, prec: Precision) {
        assert_eq!(prec.f64_eq(a, b), prec.f64_eq(b, a))
    }

    #[proptest_macro::property_test]
    fn proptest_eq_optimizations(a: f64, b: f64, prec: Precision) {
        let b_bucket = prec.bucket(b);
        let (a_lo, a_mid, a_hi) = prec.nearby_buckets(a);
        let expected_eq = a_mid == b_bucket || a_lo == Some(b_bucket) || a_hi == Some(b_bucket);

        assert_eq!(prec.f64_eq(a, b), expected_eq);
    }

    #[proptest_macro::property_test]
    fn proptest_eq_zero(f: f64, prec: Precision) {
        assert_eq!(prec.f64_eq_zero(f), prec.f64_eq(0.0, f));
    }
}
