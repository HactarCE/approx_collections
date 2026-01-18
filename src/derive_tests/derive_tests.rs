use crate::{ApproxEqZero, traits::ApproxEq};
use approx_eq_derive::{ApproxEq, ApproxEqZero};

use crate::Precision;

#[derive(Debug, ApproxEq)]
pub struct Coord {
    x: f64,
    y: f64,
}

#[derive(Debug, ApproxEq)]
struct Coord2(f64, f64);

#[derive(Debug, ApproxEq, ApproxEqZero)]
struct Wrapper<'a, T: ApproxEq + ApproxEqZero> {
    data: &'a T,
}

#[derive(Debug, ApproxEq)]
enum Empty {}
#[derive(Debug, ApproxEq)]
struct Empty2 {}

struct NoDebug {}

// #[derive(Debug, ApproxEq)]
// struct Test6 {
//     f1: f64,
//     f2: NoDebug,
// }

#[derive(Debug, ApproxEq)]
struct Test3<const N: usize> {
    data: [f64; N],
}

// #[derive(Debug, ApproxEq)]
// union UnionTest {
//     one: f64,
//     two: f64,
// }

// #[derive(Debug, ApproxEq, Copy)]
// struct Hello {
//     x: f64,
//     y: String,
// }

#[derive(Debug, ApproxEq)]
enum Test2<'a, 'b, T>
where
    T: ApproxEq,
    'a: 'b,
{
    One,
    Two { t: &'a T },
    Three(T, &'b T),
}

#[derive(Debug, ApproxEq)]
enum Test {
    One(f64, f64),
    Two { x: f64, y: f64 },
}

fn coord(x: f64, y: f64) -> Coord {
    Coord { x, y }
}

#[test]
fn test_coords() {
    let c1 = coord(1.0, 1.0);
    let c2 = coord(2.0, 1.0);
    let prec = Precision::new_simple(20);
    assert!(c1.approx_eq(&c1, prec));
    assert!(!c1.approx_eq(&c2, prec));
}

#[test]
fn test_coords2() {
    let c1 = Coord2(1.0, 1.0);
    let c2 = Coord2(2.0, 1.0);
    let prec = Precision::new_simple(20);
    assert!(c1.approx_eq(&c1, prec));
    assert!(!c1.approx_eq(&c2, prec));
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
