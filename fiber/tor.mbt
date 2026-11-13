///|
/// Componentwise maximum: the lcm of two monomials.
pub fn monomial_lcm(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<a.length() {
    out.push(if a[i] > b[i] { a[i] } else { b[i] })
  }
  out
}

///|
/// Componentwise difference `a - b`, valid when `b` divides `a`.
pub fn monomial_quotient(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<a.length() {
    out.push(a[i] - b[i])
  }
  out
}

///|
pub fn monomial_degree(a : Array[Int32]) -> Int32 {
  let mut s = 0
  for x in a {
    s = s + x
  }
  s
}

///|
/// All subsets of `{0 .. r-1}` of size `k`, in lexicographic order.
fn subsets_of_size(r : Int32, k : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  let cur : Array[Int32] = []
  fn go(start : Int32, left : Int32) -> Unit {
    if left == 0 {
      let s : Array[Int32] = []
      for x in cur {
        s.push(x)
      }
      out.push(s)
    } else {
      for i in start..<(r - left + 1) {
        cur.push(i)
        go(i + 1, left - 1)
        ignore(cur.pop())
      }
    }
  }

  go(0, k)
  out
}

///|
/// The Taylor resolution of a monomial ideal `I = (m_1, .., m_r)`.
///
/// In homological degree `k` there is one free generator `e_S` for each
/// `k`-subset `S`, of multidegree `lcm(m_i : i in S)`, and
///
/// ```text
/// d(e_S) = sum_{j} (-1)^j (lcm(S) / lcm(S \ i_j)) e_{S \ i_j}.
/// ```
///
/// Unlike the Koszul complex this is a free resolution for *every* monomial
/// ideal, regular sequence or not — which is exactly what a derived
/// computation needs, since derived intersections are interesting precisely
/// when transversality fails.
#derive(Debug)
pub struct Taylor {
  gens : Array[Array[Int32]]
  lcms : Array[Array[Array[Int32]]]
}

///|
pub fn taylor(gens : Array[Array[Int32]]) -> Taylor {
  let r = gens.length()
  let lcms : Array[Array[Array[Int32]]] = []
  for k in 0..<=r {
    let level : Array[Array[Int32]] = []
    for s in subsets_of_size(r, k) {
      let mut acc = Array::make(gens[0].length(), 0)
      for i in s {
        acc = monomial_lcm(acc, gens[i])
      }
      level.push(acc)
    }
    lcms.push(level)
  }
  Taylor::{ gens, lcms, }
}

///|
pub fn Taylor::top(self : Taylor) -> Int32 {
  self.gens.length()
}

///|
/// Number of free generators in homological degree `k`: `binom(r, k)`.
pub fn Taylor::rank_at(self : Taylor, k : Int32) -> Int32 {
  if k < 0 || k >= self.lcms.length() {
    0
  } else {
    self.lcms[k].length()
  }
}

///|
/// A graded basis element of the Taylor complex tensored with `R/J`:
/// homological degree, subset index, and the standard monomial of `R/J`.
#derive(Debug, Eq)
pub struct TorBasis {
  subset : Int32
  mono : Int32
  degree : Int32
}

///|
/// The complex `Taylor(I) tensor_R R/J`, truncated at total degree `D`.
/// Because every differential preserves the total degree, the truncation
/// is a subcomplex and its homology is *exact* in all degrees `<= D`.
#derive(Debug)
pub struct TorComplex {
  levels : Array[Array[TorBasis]]
  diffs : Array[Array[Array[Int32]]]
  deg_bound : Int32
  p : Int32
}

///|
/// Build `Taylor(I) tensor R/J`.  `q` is the graded quotient `R/J`.
pub fn tor_complex(t : Taylor, q : Quotient) -> TorComplex {
  let p = q.p
  let bound = q.ms.deg_bound
  let levels : Array[Array[TorBasis]] = []
  for k in 0..<=t.top() {
    let level : Array[TorBasis] = []
    for si in 0..<t.rank_at(k) {
      let shift = monomial_degree(t.lcms[k][si])
      for bi in 0..<q.dim() {
        let d = shift + q.ms.degree(q.basis[bi])
        if d <= bound {
          level.push(TorBasis::{ subset: si, mono: bi, degree: d, })
        }
      }
    }
    levels.push(level)
  }
  let diffs : Array[Array[Array[Int32]]] = []
  // diffs[k] : level k -> level k-1 ; diffs[0] is the empty map
  diffs.push(fp_mat_zero(0, levels[0].length()))
  for k in 1..<=t.top() {
    let src = levels[k]
    let dst = levels[k - 1]
    let mat = fp_mat_zero(dst.length(), src.length())
    let subsets = subsets_of_size(t.top(), k)
    let smaller = subsets_of_size(t.top(), k - 1)
    for col in 0..<src.length() {
      let entry = src[col]
      let s = subsets[entry.subset]
      let s_lcm = t.lcms[k][entry.subset]
      for j in 0..<s.length() {
        // S without its j-th element
        let rest : Array[Int32] = []
        for x in 0..<s.length() {
          if x != j {
            rest.push(s[x])
          }
        }
        let mut target_subset = -1
        for si in 0..<smaller.length() {
          if smaller[si] == rest {
            target_subset = si
          }
        }
        if target_subset < 0 {
          continue
        }
        let rest_lcm = t.lcms[k - 1][target_subset]
        let factor = monomial_quotient(s_lcm, rest_lcm)
        // multiply the R/J basis monomial by `factor`
        let prod = q.ms.shift(q.basis[entry.mono], factor)
        if prod < 0 {
          continue
        }
        let target_mono = q.position(prod)
        if target_mono < 0 {
          continue
        }
        // find the row
        for row in 0..<dst.length() {
          if dst[row].subset == target_subset && dst[row].mono == target_mono {
            let sign = if j % 2 == 0 { 1 } else { p - 1 }
            mat[row][col] = fp_norm(mat[row][col] + sign, p)
          }
        }
      }
    }
    diffs.push(mat)
  }
  TorComplex::{ levels, diffs, deg_bound: bound, p, }
}

///|
pub fn TorComplex::level_dim(self : TorComplex, k : Int32) -> Int32 {
  if k < 0 || k >= self.levels.length() {
    0
  } else {
    self.levels[k].length()
  }
}

///|
/// `dim Tor_k^R(R/I, R/J)` in total degrees `<= deg_bound`.
pub fn TorComplex::tor_dim(self : TorComplex, k : Int32) -> Int32 {
  if k < 0 || k >= self.levels.length() {
    return 0
  }
  let n = self.levels[k].length()
  // dim ker d_k - dim(im d_{k+1} intersect ker d_k)
  let ker = fp_kernel_cols(self.diffs[k], n, self.p)
  let next = if k + 1 < self.diffs.length() {
    self.diffs[k + 1]
  } else {
    fp_mat_zero(n, 0)
  }
  let im = @core.fp_image(next, self.p)
  let combined : Array[Array[Int32]] = []
  for r in ker {
    combined.push(r)
  }
  for r in im {
    combined.push(r)
  }
  let inter = im.length() + ker.length() - fp_rank(combined, self.p)
  ker.length() - inter
}

///|
/// All Tor dimensions, from `Tor_0` up to the number of generators.
pub fn TorComplex::tor_dims(self : TorComplex) -> Array[Int32] {
  let out : Array[Int32] = []
  for k in 0..<self.levels.length() {
    out.push(self.tor_dim(k))
  }
  out
}

///|
/// Graded Tor dimensions: `tor_graded(k)[d] = dim Tor_k` in degree `d`.
pub fn TorComplex::tor_graded(self : TorComplex, k : Int32) -> Array[Int32] {
  let out = Array::make(self.deg_bound + 1, 0)
  if k < 0 || k >= self.levels.length() {
    return out
  }
  // homology restricted to each degree: the differential preserves degree,
  // so we may split the matrices by degree and compute independently
  for d in 0..<=self.deg_bound {
    let src_cols : Array[Int32] = []
    for i in 0..<self.levels[k].length() {
      if self.levels[k][i].degree == d {
        src_cols.push(i)
      }
    }
    let next_rows : Array[Int32] = []
    if k + 1 < self.levels.length() {
      for i in 0..<self.levels[k + 1].length() {
        if self.levels[k + 1][i].degree == d {
          next_rows.push(i)
        }
      }
    }
    let dst_rows : Array[Int32] = []
    if k - 1 >= 0 {
      for i in 0..<self.levels[k - 1].length() {
        if self.levels[k - 1][i].degree == d {
          dst_rows.push(i)
        }
      }
    }
    let dk = fp_mat_zero(dst_rows.length(), src_cols.length())
    for a in 0..<dst_rows.length() {
      for b in 0..<src_cols.length() {
        dk[a][b] = self.diffs[k][dst_rows[a]][src_cols[b]]
      }
    }
    let dn = fp_mat_zero(src_cols.length(), next_rows.length())
    for a in 0..<src_cols.length() {
      for b in 0..<next_rows.length() {
        dn[a][b] = self.diffs[k + 1][src_cols[a]][next_rows[b]]
      }
    }
    let ker = fp_kernel_cols(dk, src_cols.length(), self.p)
    let im = @core.fp_image(dn, self.p)
    let combined : Array[Array[Int32]] = []
    for r in ker {
      combined.push(r)
    }
    for r in im {
      combined.push(r)
    }
    let inter = im.length() + ker.length() - fp_rank(combined, self.p)
    out[d] = ker.length() - inter
  }
  out
}

///|
/// `d^2 = 0` on the tensored Taylor complex — the check that the whole
/// derived construction is a complex at all.
pub fn TorComplex::check_d2(self : TorComplex) -> Bool {
  for k in 1..<(self.diffs.length() - 1) {
    let prod = fp_matmul(self.diffs[k], self.diffs[k + 1], self.p)
    for row in prod {
      for x in row {
        if x != 0 {
          return false
        }
      }
    }
  }
  true
}

///|
/// Serre's intersection multiplicity
/// `chi(R/I, R/J) = sum_k (-1)^k dim Tor_k^R(R/I, R/J)`.
/// For a proper (finite-length) intersection this is the correct
/// intersection number; the naive `dim R/(I+J)` is only its first term.
pub fn TorComplex::serre_multiplicity(self : TorComplex) -> Int32 {
  let mut s = 0
  for k in 0..<self.levels.length() {
    let d = self.tor_dim(k)
    s = s + (if k % 2 == 0 { d } else { -d })
  }
  s
}

///|
/// The classical (underived) fiber product `R/(I+J)`, for comparison.
pub fn classical_fiber_dim(
  i : MonomialIdeal,
  j : MonomialIdeal,
  ms : Monomials,
) -> Int32 {
  let gens : Array[Array[Int32]] = []
  for g in i.gens {
    gens.push(g)
  }
  for g in j.gens {
    gens.push(g)
  }
  monomial_ideal(gens).standard(ms).length()
}

///|
/// The derived fiber product of `R/I` and `R/J` over `R`: the full Tor
/// algebra, not just its `Tor_0`.  `Tor_0` recovers the classical fiber
/// product; the higher `Tor_k` are the derived structure sheaf, and they
/// vanish exactly when the intersection is transverse.
#derive(Debug)
pub struct DerivedFiber {
  tor : Array[Int32]
  classical : Int32
  serre : Int32
  transverse : Bool
  d2_ok : Bool
}

///|
pub fn derived_fiber(
  i : MonomialIdeal,
  j : MonomialIdeal,
  ms : Monomials,
  p : Int32,
) -> DerivedFiber {
  let t = taylor(i.gens)
  let q = quotient(ms, j, p)
  let cx = tor_complex(t, q)
  let tor = cx.tor_dims()
  let mut transverse = true
  for k in 1..<tor.length() {
    if tor[k] != 0 {
      transverse = false
    }
  }
  DerivedFiber::{
    tor,
    classical: classical_fiber_dim(i, j, ms),
    serre: cx.serre_multiplicity(),
    transverse,
    d2_ok: cx.check_d2(),
  }
}
