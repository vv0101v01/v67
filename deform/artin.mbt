///|
/// The Artin local ring `R_n = F_p[t] / (t^n)`, the `n`-th stage of the
/// canonical tower
///
/// ```text
/// ... -> R_3 -> R_2 -> R_1 = F_p
/// ```
///
/// An element is a coefficient vector of length `n`.  `R_2` is the ring of
/// dual numbers, whose points are exactly the first-order deformations.
/// Every formal deformation problem is a functor on these rings, and the
/// tower maps are truncation of coefficients.
#derive(Debug, Eq)
pub struct Artin {
  p : Int32
  n : Int32
}

///|
pub fn Artin::new(p : Int32, n : Int32) -> Artin {
  Artin::{ p, n, }
}

///|
pub fn Artin::zero(self : Artin) -> Array[Int32] {
  Array::make(self.n, 0)
}

///|
pub fn Artin::one(self : Artin) -> Array[Int32] {
  let a = Array::make(self.n, 0)
  a[0] = 1
  a
}

///|
/// The uniformiser `t`, i.e. the class of the deformation parameter.
pub fn Artin::uniformiser(self : Artin) -> Array[Int32] {
  let a = Array::make(self.n, 0)
  if self.n > 1 {
    a[1] = 1
  }
  a
}

///|
pub fn Artin::from_int(self : Artin, k : Int32) -> Array[Int32] {
  let a = Array::make(self.n, 0)
  a[0] = fp_norm(k, self.p)
  a
}

///|
pub fn Artin::add(
  self : Artin,
  a : Array[Int32],
  b : Array[Int32],
) -> Array[Int32] {
  let out = Array::make(self.n, 0)
  for i in 0..<self.n {
    out[i] = fp_add(a[i], b[i], self.p)
  }
  out
}

///|
pub fn Artin::neg(self : Artin, a : Array[Int32]) -> Array[Int32] {
  let out = Array::make(self.n, 0)
  for i in 0..<self.n {
    out[i] = fp_norm(-a[i], self.p)
  }
  out
}

///|
/// Truncated convolution: `(a*b)_k = sum_{i+j=k} a_i b_j`, dropping `k >= n`.
/// Cost `O(n^2)`.
pub fn Artin::mul(
  self : Artin,
  a : Array[Int32],
  b : Array[Int32],
) -> Array[Int32] {
  let out = Array::make(self.n, 0)
  for i in 0..<self.n {
    if a[i] != 0 {
      for j in 0..<(self.n - i) {
        out[i + j] = fp_add(out[i + j], fp_mul(a[i], b[j], self.p), self.p)
      }
    }
  }
  out
}

///|
/// A truncated power series is a unit iff its constant term is nonzero
/// (the ring is local with maximal ideal `(t)`).  The inverse is computed
/// by the recursion `b_0 = a_0^{-1}`, `b_k = -a_0^{-1} sum_{i=1}^k a_i b_{k-i}`.
pub fn Artin::inv(self : Artin, a : Array[Int32]) -> Array[Int32]? {
  if a[0] == 0 {
    return None
  }
  let inv0 = fp_inv(a[0], self.p)
  let b = Array::make(self.n, 0)
  b[0] = inv0
  for k in 1..<self.n {
    let mut s = 0
    for i in 1..<=k {
      s = fp_add(s, fp_mul(a[i], b[k - i], self.p), self.p)
    }
    b[k] = fp_norm(-fp_mul(inv0, s, self.p), self.p)
  }
  Some(b)
}

///|
pub fn Artin::is_unit(_self : Artin, a : Array[Int32]) -> Bool {
  a[0] != 0
}

///|
/// The tower map `R_{n+1} -> R_n`: forget the top coefficient.  This is the
/// structure map of the inverse system whose limit is `F_p[[t]]`.
pub fn Artin::truncate(
  _self : Artin,
  a : Array[Int32],
  to_n : Int32,
) -> Array[Int32] {
  let out = Array::make(to_n, 0)
  for i in 0..<to_n {
    out[i] = if i < a.length() { a[i] } else { 0 }
  }
  out
}

///|
/// Lift an element of `R_n` to `R_{n+1}` by appending a zero top coefficient.
/// Any other lift differs by a multiple of `t^n`, which is exactly the
/// affine space of choices that the obstruction theory acts on.
pub fn Artin::lift_zero(
  _self : Artin,
  a : Array[Int32],
  to_n : Int32,
) -> Array[Int32] {
  let out = Array::make(to_n, 0)
  for i in 0..<a.length() {
    if i < to_n {
      out[i] = a[i]
    }
  }
  out
}

///|
/// The residue field `R_1 = F_p`: reduction modulo the maximal ideal.
pub fn Artin::residue(_self : Artin, a : Array[Int32]) -> Int32 {
  a[0]
}

///|
/// The `t`-adic valuation, capped at `n` (where it means zero).
pub fn Artin::valuation(self : Artin, a : Array[Int32]) -> Int32 {
  for i in 0..<self.n {
    if a[i] != 0 {
      return i
    }
  }
  self.n
}

///|
/// A square-zero extension `0 -> I -> R_{n+1} -> R_n -> 0` with
/// `I = (t^n) ≅ F_p`.  The kernel is one-dimensional and killed by the
/// maximal ideal, which is precisely the hypothesis under which
/// obstruction classes live in a single cohomology group.
#derive(Debug, Eq)
pub struct SmallExtension {
  base : Artin
  total : Artin
  kernel_dim : Int32
}

///|
pub fn small_extension(p : Int32, n : Int32) -> SmallExtension {
  SmallExtension::{
    base: Artin::new(p, n),
    total: Artin::new(p, n + 1),
    kernel_dim: 1,
  }
}

///|
/// Check the defining property: the kernel of truncation is spanned by
/// `t^n` and is square-zero.
pub fn SmallExtension::check(self : SmallExtension) -> Bool {
  let t_n = Array::make(self.total.n, 0)
  t_n[self.base.n] = 1
  // square-zero
  let sq = self.total.mul(t_n, t_n)
  let mut zero = true
  for x in sq {
    if x != 0 {
      zero = false
    }
  }
  // killed by the maximal ideal: t * t^n = 0
  let prod = self.total.mul(self.total.uniformiser(), t_n)
  let mut killed = true
  for x in prod {
    if x != 0 {
      killed = false
    }
  }
  zero && killed
}
