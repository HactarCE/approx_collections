//! Data structures using approximate floating-point comparisons.
//!
//! [`Precision`] is the basic struct used by everything in this crate.
//!
//! [`FloatPool`] is used for interning floats to reduce accumulated numerical
//! error and allow direct comparison and hashing via [`ApproxHash`].
//!
//! [`ApproxHashMap`] is used for looking up approximate values.
//!
//! For implementing approximate comparison on your own types, see [`ApproxEq`],
//! [`ApproxEqZero`], and [`ApproxOrd`].
//!
//! # Example
//!
//! ```
//! # use approx_collections::*;
//! const APPROX: Precision = Precision::DEFAULT;
//!
//! assert_ne!(0.1 + 0.2, 0.3_f64);
//! assert!(APPROX.eq(0.1 + 0.2, 0.3_f64));
//! ```
//!
//! # Implementation
//!
//! See [`Precision`] for details about how floats are compared.
//!
//! # Features
//!
//! The `rustc-hash` feature is enabled by default, and uses a faster hashing
//! algorithm for the hash map inside [`FloatPool`].
//!
//! The `derive` feature is enabled by default, and provides derive macros for
//! [`ApproxEq`] and [`ApproxEqZero`].

pub mod hash_map;
pub mod pool;
pub mod precision;
pub mod traits;

#[cfg(feature = "derive")]
pub use approx_collections_derive::{ApproxEq, ApproxEqZero};
pub use hash_map::ApproxHashMap;
pub use pool::FloatPool;
pub use precision::Precision;
pub use traits::*;
