///|
using @core {type Bits}

///|
/// A **little n-cube**: an axis-aligned affine embedding of the unit cube
/// into itself, `x ↦ (lo + side·x) / den`, with `side > 0` and the image
/// inside `[0,1]^n`.
///
/// Coordinates are exact integers over a per-cube denominator, so
/// composition is exact integer arithmetic — no floating point, no
/// rounding, and every predicate below is decidable.  Composing two cubes
/// multiplies their denominators, which is the only source of growth.
#derive(Debug, Eq)
pub struct LittleCube {
  lo : Array[Int32]
  side : Array[Int32]
  den : Int32
}

///|
pub fn LittleCube::new(
  lo : Array[Int32],
  side : Array[Int32],
  den : Int32,
) -> LittleCube {
  LittleCube::{ lo, side, den, }
}

///|
pub fn LittleCube::dim(self : LittleCube) -> Int32 {
  self.lo.length()
}

///|
/// The unit cube, the identity operation of the operad.
pub fn unit_cube(n : Int32) -> LittleCube {
  LittleCube::{ lo: Array::make(n, 0), side: Array::make(n, 1), den: 1, }
}

///|
/// Well-formedness: positive side lengths and image inside the unit cube.
pub fn LittleCube::valid(self : LittleCube) -> Bool {
  let n = self.dim()
  if self.side.length() != n || self.den <= 0 {
    return false
  }
  for i in 0..<n {
    if self.lo[i] < 0 ||
      self.side[i] <= 0 ||
      self.lo[i] + self.side[i] > self.den {
      return false
    }
  }
  true
}

///|
/// Two little cubes have disjoint interiors iff they are separated along
/// *some* axis.  Exact integer comparison.
pub fn LittleCube::disjoint(self : LittleCube, other : LittleCube) -> Bool {
  if self.dim() != other.dim() {
    return false
  }
  // rescale to a common denominator
  let d1 = self.den
  let d2 = other.den
  for i in 0..<self.dim() {
    let a0 = self.lo[i] * d2
    let a1 = (self.lo[i] + self.side[i]) * d2
    let b0 = other.lo[i] * d1
    let b1 = (other.lo[i] + other.side[i]) * d1
    if a1 <= b0 || b1 <= a0 {
      return true
    }
  }
  false
}

///|
/// Insert `inner` into `self`: the affine composite `self ∘ inner`.
/// Denominators multiply, everything stays exact.
pub fn LittleCube::compose(self : LittleCube, inner : LittleCube) -> LittleCube {
  let n = self.dim()
  let lo : Array[Int32] = []
  let side : Array[Int32] = []
  for i in 0..<n {
    lo.push(self.lo[i] * inner.den + self.side[i] * inner.lo[i])
    side.push(self.side[i] * inner.side[i])
  }
  LittleCube::{ lo, side, den: self.den * inner.den, }
}

///|
/// The image of a corner: `x ∈ {0,1}^n` mapped through the embedding,
/// as an exact rational over `den`.  Used to check containment.
pub fn LittleCube::corner(self : LittleCube, x : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<self.dim() {
    out.push(self.lo[i] + self.side[i] * x[i])
  }
  out
}

///|
/// Does `self` contain `other` (as a subset of the unit cube)?
pub fn LittleCube::contains(self : LittleCube, other : LittleCube) -> Bool {
  if self.dim() != other.dim() {
    return false
  }
  let d1 = self.den
  let d2 = other.den
  for i in 0..<self.dim() {
    if other.lo[i] * d1 < self.lo[i] * d2 {
      return false
    }
    if (other.lo[i] + other.side[i]) * d1 > (self.lo[i] + self.side[i]) * d2 {
      return false
    }
  }
  true
}

///|
/// Do two cubes describe the same region, ignoring the representation of
/// the rational coordinates?  Composition multiplies denominators without
/// cancelling, so this — not structural equality — is geometric sameness.
pub fn LittleCube::same_region(self : LittleCube, other : LittleCube) -> Bool {
  if self.dim() != other.dim() {
    return false
  }
  for i in 0..<self.dim() {
    if self.lo[i] * other.den != other.lo[i] * self.den {
      return false
    }
    if self.side[i] * other.den != other.side[i] * self.den {
      return false
    }
  }
  true
}

///|
/// An element of the little cubes operad `C_n(k)`: `k` little `n`-cubes
/// with pairwise disjoint interiors.  The arity is the number of cubes.
#derive(Debug, Eq)
pub struct Config {
  dim : Int32
  cubes : Array[LittleCube]
}

///|
pub fn Config::new(dim : Int32, cubes : Array[LittleCube]) -> Config {
  Config::{ dim, cubes, }
}

///|
pub fn Config::arity(self : Config) -> Int32 {
  self.cubes.length()
}

///|
/// The operad unit: one cube, the whole unit cube.
pub fn operad_unit(n : Int32) -> Config {
  Config::new(n, [unit_cube(n)])
}

///|
/// A configuration is a point of `C_n(k)` iff every cube is valid and they
/// are pairwise disjoint.  This is the *decidable* membership test.
pub fn Config::valid(self : Config) -> Bool {
  for c in self.cubes {
    if c.dim() != self.dim || !c.valid() {
      return false
    }
  }
  for i in 0..<self.arity() {
    for j in (i + 1)..<self.arity() {
      if !self.cubes[i].disjoint(self.cubes[j]) {
        return false
      }
    }
  }
  true
}

///|
/// **Operadic composition** `γ(c; d_1, …, d_k)`: insert `d_i` into the
/// `i`-th cube of `c`.  The arities add up: the result has arity
/// `Σ arity(d_i)`.
pub fn Config::compose(self : Config, parts : Array[Config]) -> Config? {
  if parts.length() != self.arity() {
    return None
  }
  let out : Array[LittleCube] = []
  for i in 0..<self.arity() {
    if parts[i].dim != self.dim {
      return None
    }
    for c in parts[i].cubes {
      out.push(self.cubes[i].compose(c))
    }
  }
  Some(Config::new(self.dim, out))
}

///|
/// The symmetric group action: permute the inputs.  `sigma[i]` is the
/// index of the cube that becomes the `i`-th one.
pub fn Config::permute(self : Config, sigma : Array[Int32]) -> Config? {
  if sigma.length() != self.arity() {
    return None
  }
  let seen = Bits::new(self.arity())
  let out : Array[LittleCube] = []
  for i in 0..<self.arity() {
    let j = sigma[i]
    if j < 0 || j >= self.arity() || seen.get(j) {
      return None
    }
    seen.set(j)
    out.push(self.cubes[j])
  }
  Some(Config::new(self.dim, out))
}

///|
/// **Dunn additivity**, the board product: an `m`-cube configuration and
/// an `n`-cube configuration give an `(m+n)`-cube configuration whose
/// cubes are the products of the factors.  This is the map
/// `C_m(j) × C_n(k) → C_{m+n}(jk)` underlying `E_m ⊗ E_n  E_{m+n}`.
pub fn board_product(a : Config, b : Config) -> Config {
  let out : Array[LittleCube] = []
  for x in a.cubes {
    for y in b.cubes {
      let lo : Array[Int32] = []
      let side : Array[Int32] = []
      // rescale each factor to the common denominator x.den * y.den
      for v in x.lo {
        lo.push(v * y.den)
      }
      for v in y.lo {
        lo.push(v * x.den)
      }
      for v in x.side {
        side.push(v * y.den)
      }
      for v in y.side {
        side.push(v * x.den)
      }
      out.push(LittleCube::{ lo, side, den: x.den * y.den, })
    }
  }
  Config::new(a.dim + b.dim, out)
}

///|
/// A standard binary operation in `C_n(2)`: two half-cubes side by side
/// along axis 0.  For `n = 1` these are the two intervals of a
/// concatenation; for `n ≥ 2` there is room to move them around.
pub fn binary_op(n : Int32) -> Config {
  let a = LittleCube::{
    lo: Array::make(n, 0),
    side: Array::make(n, 2),
    den: 4,
  }
  let b_lo = Array::make(n, 0)
  b_lo[0] = 2
  let b = LittleCube::{ lo: b_lo, side: Array::make(n, 2), den: 4, }
  Config::new(n, [a, b])
}

///|
/// A standard ternary operation: three slabs along axis 0.
pub fn ternary_op(n : Int32) -> Config {
  let out : Array[LittleCube] = []
  for i in 0..<3 {
    let lo = Array::make(n, 0)
    lo[0] = 2 * i
    out.push(LittleCube::{ lo, side: Array::make(n, 2), den: 6, })
  }
  Config::new(n, out)
}
