///|
/// Monomials of `F_p[x_0 .. x_{n-1}]` up to total degree `deg_bound`,
/// indexed in graded-lexicographic order.  Everything below is *graded*:
/// a computation truncated at degree `D` is exact in every degree `<= D`,
/// because all the differentials are degree-preserving.
#derive(Debug, Eq)
pub struct Monomials {
  nvars : Int32
  deg_bound : Int32
  exps : Array[Array[Int32]]
  degs : Array[Int32]
}

///|
pub fn Monomials::new(nvars : Int32, deg_bound : Int32) -> Monomials {
  let exps : Array[Array[Int32]] = []
  let degs : Array[Int32] = []
  let cur = Array::make(nvars, 0)
  fn go(v : Int32, used : Int32) -> Unit {
    if v == nvars {
      let e : Array[Int32] = []
      for x in cur {
        e.push(x)
      }
      exps.push(e)
      degs.push(used)
    } else {
      for k in 0..<=(deg_bound - used) {
        cur[v] = k
        go(v + 1, used + k)
      }
      cur[v] = 0
    }
  }

  go(0, 0)
  Monomials::{ nvars, deg_bound, exps, degs, }
}

///|
pub fn Monomials::size(self : Monomials) -> Int32 {
  self.exps.length()
}

///|
pub fn Monomials::index_of(self : Monomials, e : Array[Int32]) -> Int32 {
  for i in 0..<self.exps.length() {
    if self.exps[i] == e {
      return i
    }
  }
  -1
}

///|
pub fn Monomials::degree(self : Monomials, i : Int32) -> Int32 {
  self.degs[i]
}

///|
/// Does the monomial `a` divide `b`?
pub fn monomial_divides(a : Array[Int32], b : Array[Int32]) -> Bool {
  for i in 0..<a.length() {
    if a[i] > b[i] {
      return false
    }
  }
  true
}

///|
/// A monomial ideal, given by monomial generators.  The quotient `R/I` has
/// a basis of *standard monomials*: those divisible by no generator.  This
/// is what makes every module below an explicit finite vector space.
#derive(Debug, Eq)
pub struct MonomialIdeal {
  gens : Array[Array[Int32]]
}

///|
pub fn monomial_ideal(gens : Array[Array[Int32]]) -> MonomialIdeal {
  MonomialIdeal::{ gens, }
}

///|
pub fn MonomialIdeal::contains(self : MonomialIdeal, m : Array[Int32]) -> Bool {
  for g in self.gens {
    if monomial_divides(g, m) {
      return true
    }
  }
  false
}

///|
/// Standard monomials of `R/I` up to the degree bound: a basis of the
/// graded quotient.
pub fn MonomialIdeal::standard(
  self : MonomialIdeal,
  ms : Monomials,
) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<ms.size() {
    if !self.contains(ms.exps[i]) {
      out.push(i)
    }
  }
  out
}

///|
/// Multiply monomial `i` by the monomial `g`, returning its index in the
/// truncated basis, or `-1` if the product exceeds the degree bound.
pub fn Monomials::shift(self : Monomials, i : Int32, g : Array[Int32]) -> Int32 {
  let e : Array[Int32] = []
  let mut total = 0
  for k in 0..<self.nvars {
    let x = self.exps[i][k] + g[k]
    e.push(x)
    total = total + x
  }
  if total > self.deg_bound {
    -1
  } else {
    self.index_of(e)
  }
}

///|
/// The graded quotient `R/I` as an explicit based vector space, with the
/// multiplication-by-a-monomial structure maps.
#derive(Debug, Eq)
pub struct Quotient {
  ms : Monomials
  ideal : MonomialIdeal
  basis : Array[Int32]
  p : Int32
}

///|
pub fn quotient(ms : Monomials, ideal : MonomialIdeal, p : Int32) -> Quotient {
  Quotient::{ ms, ideal, basis: ideal.standard(ms), p, }
}

///|
pub fn Quotient::dim(self : Quotient) -> Int32 {
  self.basis.length()
}

///|
/// Position of a monomial index in the quotient basis, or -1 if it is zero
/// in the quotient.
pub fn Quotient::position(self : Quotient, mono : Int32) -> Int32 {
  for k in 0..<self.basis.length() {
    if self.basis[k] == mono {
      return k
    }
  }
  -1
}

///|
/// The matrix of "multiply by the monomial `g`" on `R/I`, truncated at the
/// degree bound.  Columns that leave the bound are zero, which is exactly
/// the truncation error — and it only affects degrees above the bound.
pub fn Quotient::mul_matrix(
  self : Quotient,
  g : Array[Int32],
) -> Array[Array[Int32]] {
  let n = self.dim()
  let mat = fp_mat_zero(n, n)
  for col in 0..<n {
    let target = self.ms.shift(self.basis[col], g)
    if target >= 0 {
      let row = self.position(target)
      if row >= 0 {
        mat[row][col] = 1
      }
    }
  }
  mat
}

///|
/// Hilbert function of the quotient: the number of standard monomials in
/// each degree.  For a derived intersection this is the graded Euler
/// characteristic input.
pub fn Quotient::hilbert(self : Quotient) -> Array[Int32] {
  let out = Array::make(self.ms.deg_bound + 1, 0)
  for b in self.basis {
    out[self.ms.degree(b)] = out[self.ms.degree(b)] + 1
  }
  out
}
