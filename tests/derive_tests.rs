#![allow(dead_code)]
#![allow(unused)]

// A lot of the structs/enums in here are not used in any test, but rather are
// included to test the proc macro to make sure the code it generates doesn't
// throw any errors. Thus I allow dead code.

use approx_collections::{ApproxEq, ApproxEqZero, ApproxInternable, FloatPool, Precision};

fn main() {}

#[derive(Debug, ApproxEq, ApproxEqZero)]
pub struct Coordinate {
    x: f64,
    y: f64,
}

#[derive(Debug, ApproxEq)]
struct Coordinate2(f64, f64);

#[derive(Debug, ApproxEq, ApproxEqZero)]
struct Wrapper<'a, 'b, T, const N: usize>
where
    T: ApproxEq + ApproxEqZero,
    'a: 'b,
{
    data: &'a [T; N],
    data2: &'b T,
}

#[derive(Debug, ApproxEq, ApproxEqZero)]
struct Wrapper2<'a, 'b: 'a, T: ApproxEq + ApproxEqZero, const N: usize> {
    data: &'a [T; N],
    data2: &'b T,
}
#[derive(ApproxInternable)]
struct WrapperIntern<'a, 'b: 'a, T: ApproxInternable, const N: usize> {
    data: &'a mut [T; N],
    data2: &'b mut T,
}

#[derive(Debug, ApproxEq)]
enum ComplicatedEnum<'a, 'b, T, const N: usize>
where
    T: ApproxEq + ApproxEqZero,
    'a: 'b,
{
    Data(&'a [T; N]),
    Data2(&'b T),
}

#[derive(Debug, ApproxEq)]
struct Empty {}

struct NoDebug {}

#[derive(Debug, ApproxEq)]
enum Foo {
    Bar1 { data: f32 },
    Bar2(f32),
    Bar3,
}

#[derive(Debug, ApproxEq)]
struct Test3<const N: usize> {
    data: [f64; N],
}

#[derive(Debug, ApproxEq)]
enum Test2<'a, 'b, T, const N: usize>
where
    T: ApproxEq,
    'a: 'b,
{
    One,
    Two { t: &'a [T; N] },
    Three(T, &'b T),
}

#[derive(Debug, ApproxEq)]
enum Test {
    One(f64, f64),
    Two { x: f64, y: f64 },
}
#[derive(ApproxInternable)]
struct InternTest {
    x: f64,
    #[approx_internable_non_float]
    y: u64,
}

#[derive(ApproxInternable)]
struct UnnamedInternTest(f64, #[approx_internable_non_float] u64);

#[derive(ApproxInternable)]
enum InternTestEnum {
    First,
    Second(f32, #[approx_internable_non_float] usize),
    Third {
        x: f32,
        #[approx_internable_non_float]
        _y: usize,
    },
}

#[derive(ApproxInternable)]
struct Foo2 {
    bar1: f64,
    #[approx_internable_non_float]
    bar2: u64,
}

#[derive(ApproxInternable)]
struct Foo3(f64, #[approx_internable_non_float] u64);

#[derive(ApproxInternable)]
enum Foo4 {
    Bar1,
    Bar2(#[approx_internable_non_float] u64, f64),
    Bar3 {
        x: f64,
        #[approx_internable_non_float]
        y: u64,
    },
}

///examples for both ApproxEq and ApproxEqZero, exactly as in the docs for the proc macros.
#[test]
fn doctest_examples() {
    assert!(ApproxEq::approx_eq(
        &Foo::Bar1 { data: 5.0 },
        &Foo::Bar1 { data: 5.0 },
        Precision::DEFAULT
    ));
    assert!(ApproxEq::approx_eq(
        &Foo::Bar2(5.0),
        &Foo::Bar2(5.0),
        Precision::DEFAULT
    ));
    assert!(ApproxEq::approx_eq(
        &Foo::Bar3,
        &Foo::Bar3,
        Precision::DEFAULT
    ));
    assert!(!ApproxEq::approx_eq(
        &Foo::Bar1 { data: 5.0 },
        &Foo::Bar2(5.0),
        Precision::DEFAULT
    ));
    let c1 = Coordinate2(5.0, 4.0);
    let c2 = Coordinate2(4.0, 5.0);
    assert!(ApproxEq::approx_eq(&c1, &c1, Precision::DEFAULT));
    assert!(!ApproxEq::approx_eq(&c1, &c2, Precision::DEFAULT));
    let c1 = Coordinate { x: 5.0, y: 4.0 };
    let c2 = Coordinate { x: 4.0, y: 5.0 };
    assert!(ApproxEq::approx_eq(&c1, &c1, Precision::DEFAULT));
    assert!(!ApproxEq::approx_eq(&c1, &c2, Precision::DEFAULT));
    let c1 = Coordinate { x: 0.0, y: 4.0 };
    let c2 = Coordinate { x: 0.0, y: 0.0 };
    assert!(!ApproxEqZero::approx_eq_zero(&c1, Precision::DEFAULT));
    assert!(ApproxEqZero::approx_eq_zero(&c2, Precision::DEFAULT));
}

#[test]
fn test_enum() {
    let e1 = Test::One(3.0, 4.0);
    let e2 = Test::One(4.0, 3.0);
    let e3 = Test::Two { x: 3.0, y: 4.0 };
    let prec = Precision::new_simple(20);
    assert!(!e1.approx_eq(&e2, prec));
    assert!(e1.approx_eq(&e1, prec));
    assert!(!e1.approx_eq(&e3, prec));
    assert!(e3.approx_eq(&e3, prec));
}

#[test]
fn test_complicated() {
    let arr = [1.0, 2.0, 3.0];
    let arr2 = [1.0, 2.001, 3.0];
    let arr3 = [0.0, 0.001, 0.0];
    let w1 = Wrapper2 {
        data: &arr,
        data2: &arr[1],
    };
    let w2 = Wrapper2 {
        data: &arr2,
        data2: &arr2[1],
    };
    let w3 = Wrapper2 {
        data: &arr3,
        data2: &arr3[1],
    };
    let precise = Precision::DEFAULT;
    let rough = Precision::new_simple(2);
    assert!(!w1.approx_eq(&w2, precise));
    assert!(w1.approx_eq(&w2, rough));
    assert!(!w3.approx_eq_zero(precise));
    assert!(w3.approx_eq_zero(rough));
}

#[test]
///test the interning. the 13 at the end comes from the initial bucket at 0.0, followed by 3 buckets per interned float (4 interned floats, since 'three' doesn't contain a float).
fn test_intern() {
    let one = Foo2 {
        bar1: 16.0,
        bar2: 5,
    };
    let two = Foo3(20.0, 10);
    let three = Foo4::Bar1;
    let four = Foo4::Bar2(55, 62.0);
    let five = Foo4::Bar3 { x: 222.0, y: 22 };
    let mut pool = FloatPool::default();
    let _ = pool.intern(one);
    let _ = pool.intern(two);
    let _ = pool.intern(three);
    let _ = pool.intern(four);
    let _ = pool.intern(five);
    assert_eq!(pool.bucket_count(), 13)
}
