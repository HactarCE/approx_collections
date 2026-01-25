# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [3.2.0]

### Added

- `FloatPool::bucket_count()`
- `FloatPool::iter()`
- `impl IntoIterator for FloatPool`
- `impl IntoIterator for &FloatPool`
- `impl IntoIterator for AppoxHashMap`
- `impl IntoIterator for &AppoxHashMap`
- `impl IntoIterator for &mut AppoxHashMap`
- Structs for `ApproxHashMap` iteration methods
- Macros for `#[derive(ApproxEq, ApproxEqZero)]` with feature `derive`

## [3.1.0]

### Added

- `impl {ApproxEq, ApproxOrd, ApproxHash} for Option<T>`
- `impl {ApproxEq, ApproxEqZero, ApproxOrd, ApproxCmpZero, ApproxHash} for (T0, T1, ...)` (tuples up to length 10)

## [3.0.0]

Values must now be interned to be stored in an `ApproxHashMap`. This aligns better with intended use cases in geometric puzzle simulation.

### Added

- `Precision::ne()`
- `Precision::ne_zero()`
- `Precision::cmp_zero()`
- `ApproxHashMap::intern()`
- `ApproxHashMap::intern_in_place()`
- `ApproxHashMap::try_intern()`
- `ApproxHashMap::insert_with_mut_key()`
- `ApproxHashMap::get_mut_with_mut_key()`
- `ApproxHashMap::entry_with_mut_key()`
- `FloatPool::try_intern()`
- `impl {ApproxEqZero, ApproxOrd, ApproxCmpZero, ApproxHash} for Vec<T>`
- `impl {ApproxEqZero, ApproxOrd, ApproxCmpZero, ApproxHash} for Box<T>`
- `?Sized` bound on `impl {ApproxEqZero, ApproxOrd, ApproxCmpZero} for &T`
- `impl ApproxHash for &mut T`

### Changed

- Renamed `ApproxSign` to `ApproxCmpZero`
  - Renamed `approx_sign()` to `approx_cmp_zero()` and changed it to return `std::cmp::Ordering` instead of `Sign`
- All methods on `ApproxHashMap` now take `K` instead of `&K`
- Overhauled `ApproxHash`
  - Removed `approx_hash()`
  - Added `intern_floats()`, `interned_eq()`, and `interned_hash()`
- Renamed `FloatInterner` to `FloatPool`
- Renamed `FloatInterner::canonicalize()` to `FloatPool::intern()`
- Renamed `FloatInterner::canonicalize_in_place()` to `FloatPool::intern_in_place()`
- Renamed `ApproxHashMap::interner()` to `ApproxHashMap::float_pool()`

### Removed

- `Sign` enum
- `ApproxHashMap::interner_mut()`
- `ApproxHash` trait
- `ApproxHasher` trait
- `ForEachFloat` trait

### Fixed

- `Precision::gt()` is no longer equivalent to `Precision::lt()`

## [2.0.0]

### Added

- `Precision::is_pos()`
- `Precision::is_neg()`
- Missing `+ ?Sized` bounds on `&T` impls.

### Changed

- Renamed `VisitFloats` to `ForEachFloat`
  - Removed `visit_floats()`
  - Renamed `visit_floats_mut()` to `for_each_float()`

### Removed

- `impl {PartialEq, Eq, Hash} for Precision` because it may cause confusion with `eq()` and `ne()` methods

## [1.1.0]

### Added

- `prelude` module
- `ApproxSign` trait

## [1.0.0]

### Added

- `Precision`
- `ApproxEq`, `ApproxEqZero`, `ApproxOrd`, `ApproxHash`, and `ApproxHasher` traits
- `FloatInterner` and `ApproxHashMap` data structures
- Entry API for `ApproxHashMap`

[3.2.0]: https://github.com/HactarCE/approx_collections/compare/v3.1.0...v3.2.0
[3.1.0]: https://github.com/HactarCE/approx_collections/compare/v3.0.0...v3.1.0
[3.0.0]: https://github.com/HactarCE/approx_collections/compare/v2.0.0...v3.0.0
[2.0.0]: https://github.com/HactarCE/approx_collections/compare/v1.1.0...v2.0.0
[1.1.0]: https://github.com/HactarCE/approx_collections/compare/v1.0.0...v1.1.0
[1.0.0]: https://github.com/HactarCE/approx_collections/releases/tag/v1.0.0
