use std::{cmp::Ordering, collections::BTreeMap};

use num_traits::{Signed, Zero};

pub type Nat = num_bigint::BigUint;
pub type Int = num_bigint::BigInt;

pub trait ToNat {
    fn to_nat(&self) -> Nat;
}

pub trait FromNat {
    fn from_nat(n: &Nat) -> Self;
}

impl ToNat for [u8] {
    fn to_nat(&self) -> Nat {
        let mut n = Nat::ZERO;
        for i in (0..self.len()).rev() {
            n.set_bit(i as u64 * 8, true);
        }
        n += Nat::from_bytes_le(self);
        n
    }
}

impl FromNat for Vec<u8> {
    fn from_nat(n: &Nat) -> Self {
        let mut len = n.bits().div_ceil(8);
        let mut offset = Nat::ZERO;
        for i in (0..len).rev() {
            offset.set_bit(i * 8, true);
        }
        if offset > *n {
            offset.set_bit((len - 1) * 8, false);
            len -= 1;
        }

        let mut bytes = (n - offset).to_bytes_le();
        bytes.resize(len as usize, 0);
        bytes
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Point {
    pub x: Int,
    pub y: Int,
}

impl Point {
    pub fn new(x: Int, y: Int) -> Self {
        Self { x, y }
    }
}

impl ToNat for Point {
    fn to_nat(&self) -> Nat {
        if self.x.is_zero() && self.y.is_zero() {
            return Nat::ZERO;
        }

        let (x_abs, y_abs) = (self.x.abs(), self.y.abs());
        let (k, vertical) = if x_abs > y_abs {
            (&x_abs, true)
        } else {
            (&y_abs, false)
        };
        let t: Int = k << 1;
        // m=(t-1)^2

        let n = if vertical {
            if self.x.is_positive() {
                // Right: m+y+k-1
                (t - 1u32).pow(2) + &self.y + k - 1u32
            } else {
                // Left: m+2t+k-1-y
                &t * &t + k - &self.y
            }
        } else if self.y.is_positive() {
            // Top: m+t-1+k-x
            &t * &t - t + k - &self.x
        } else {
            // Bottom: m+3t-1+x+k
            &t * &t + t + &self.x + k
        };
        n.into_parts().1
    }
}

impl FromNat for Point {
    fn from_nat(n: &Nat) -> Self {
        if n.is_zero() {
            return Self::new(Int::ZERO, Int::ZERO);
        }

        let k = (n.sqrt() + 1u32) >> 1;
        let t = &k << 1;
        let mut m = &t * &t + 1u32; // m=(t-1)^2+2t

        let k = Int::from(k);
        if *n < m {
            m -= t;
            if *n < m {
                // Right
                Self::new(k.clone(), k + 1u32 - Int::from(m - n))
            } else {
                // Top
                Self::new(&k - 1 - Int::from(n - m), k)
            }
        } else {
            m += t;
            if *n < m {
                // Left
                Self::new(-k.clone(), -k - 1u32 + Int::from(m - n))
            } else {
                // Bottom
                Self::new(-&k + 1 + Int::from(n - m), -k)
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Direction {
    Right,
    Up,
    Left,
    Down,
}

impl Direction {
    fn is_vertical(self) -> bool {
        matches!(self, Self::Up | Self::Down)
    }

    fn next(self) -> Self {
        match self {
            Self::Right => Self::Up,
            Self::Up => Self::Left,
            Self::Left => Self::Down,
            Self::Down => Self::Right,
        }
    }

    fn unit_vec(self) -> (i32, i32) {
        match self {
            Self::Right => (1, 0),
            Self::Up => (0, 1),
            Self::Left => (-1, 0),
            Self::Down => (0, -1),
        }
    }
}

pub struct Spiral {
    steps: u32,
    dir: Direction,
    rem_steps: u32,
    x: i32,
    y: i32,
}

impl Spiral {
    pub fn new() -> Self {
        Self {
            steps: 1,
            dir: Direction::Right,
            rem_steps: 1,
            x: 0,
            y: 0,
        }
    }
}

impl Iterator for Spiral {
    type Item = (i32, i32);

    fn next(&mut self) -> Option<(i32, i32)> {
        let res = (self.x, self.y);

        if self.rem_steps == 0 {
            if self.dir.is_vertical() {
                self.steps += 1;
            }
            self.dir = self.dir.next();
            self.rem_steps = self.steps;
        }

        let (dx, dy) = self.dir.unit_vec();
        self.x += dx;
        self.y += dy;
        self.rem_steps -= 1;

        Some(res)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Stone {
    Black = 1,
    White = 2,
}

#[derive(Debug, Clone)]
struct IndexedPoint {
    i: Nat,
    p: Point,
}

impl IndexedPoint {
    fn new(p: Point) -> Self {
        Self { i: p.to_nat(), p }
    }
}

impl PartialEq for IndexedPoint {
    fn eq(&self, other: &Self) -> bool {
        self.i == other.i
    }
}

impl Eq for IndexedPoint {}

impl PartialOrd for IndexedPoint {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for IndexedPoint {
    fn cmp(&self, other: &Self) -> Ordering {
        self.i.cmp(&other.i)
    }
}

#[derive(Debug, Clone)]
pub struct Shape {
    stones: BTreeMap<IndexedPoint, Stone>,
}

impl Shape {
    pub fn new() -> Self {
        Self {
            stones: BTreeMap::new(),
        }
    }

    pub fn set(&mut self, p: Point, stone: Stone) {
        self.stones.insert(IndexedPoint::new(p), stone);
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Point, Stone)> {
        self.stones.iter().map(|(ip, s)| (&ip.p, *s))
    }
}

impl ToNat for Shape {
    fn to_nat(&self) -> Nat {
        let Some(last) = self.stones.last_key_value() else {
            return Nat::ZERO;
        };
        let len = usize::try_from(&last.0.i)
            .ok()
            .and_then(|i| i.checked_add(1))
            .expect("too far away");
        let mut digits = vec![0u8; len];

        for (ip, &s) in &self.stones {
            let i = usize::try_from(&ip.i).unwrap();
            digits[i] = s as u8;
        }
        Nat::from_radix_le(&digits, 3).unwrap()
    }
}

impl FromNat for Shape {
    fn from_nat(n: &Nat) -> Self {
        let mut res = Shape::new();
        let digits = n.to_radix_le(3);
        for ((x, y), digit) in Spiral::new().zip(digits) {
            if digit == 0 {
                continue;
            }
            let p = Point::new(x.into(), y.into());
            let stone = if digit == 1 {
                Stone::Black
            } else {
                Stone::White
            };
            res.set(p, stone);
        }
        res
    }
}

#[cfg(test)]
mod tests {
    use crate::{FromNat, Nat, Point, Shape, Spiral, ToNat};

    #[test]
    fn point_from_to_nat() {
        for i in 0..100000u32 {
            let n = Nat::from(i);
            assert_eq!(Point::from_nat(&n).to_nat(), n);
        }
    }

    #[test]
    fn bytes_from_to_nat() {
        for i in 0..100000u32 {
            let n = Nat::from(i);
            assert_eq!(Vec::<u8>::from_nat(&n).to_nat(), n);
        }
    }

    #[test]
    fn spiral() {
        for ((x, y), i) in Spiral::new().zip(0..100000u32) {
            let p = Point::new(x.into(), y.into());
            let n = Nat::from(i);
            assert_eq!(p.to_nat(), n);
        }
    }

    #[test]
    fn shape_from_to_nat() {
        for i in 0..100000u32 {
            let n = Nat::from(i);
            assert_eq!(Shape::from_nat(&n).to_nat(), n);
        }
    }
}
