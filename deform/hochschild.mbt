///|
/// A finite-dimensional associative algebra `A` over `F_p` with a fixed
/// basis `e_0 .. e_{d-1}`, given by structure constants
/// `c[i][j][k]` meaning `e_i * e_j = sum_k c[i][j][k] e_k`.
///
/// This is the input to a deformation problem: Gerstenhaber's theory says
/// first-order deformations of the multiplication are classified by the
/// Hochschild cohomology `HH^2(A,A)`, and obstructions live in `HH^3`.
#derive(Debug, Eq)
pub struct Alg {
  dim : Int32
  p : Int32
  c : Array[Array[Array[Int32]]]
}

///|
pub fn Alg::new(dim : Int32, p : Int32, c : Array[Array[Array[Int32]]]) -> Alg {
  Alg::{ dim, p, c, }
}

///|
/// Structure constants of the product of two basis elements.
pub fn Alg::mul_basis(self : Alg, i : Int32, j : Int32) -> Array[Int32] {
  self.c[i][j]
}

///|
/// Associativity: `(e_i e_j) e_k = e_i (e_j e_k)` for all triples.
/// Cost `O(d^4)` — the defining identity of the whole deformation theory.
pub fn Alg::is_associative(self : Alg) -> Bool {
  let d = self.dim
  let p = self.p
  for i in 0..<d {
    for j in 0..<d {
      for k in 0..<d {
        // (e_i e_j) e_k
        let lhs = Array::make(d, 0)
        for m in 0..<d {
          let a = self.c[i][j][m]
          if a != 0 {
            for t in 0..<d {
              lhs[t] = fp_add(lhs[t], fp_mul(a, self.c[m][k][t], p), p)
            }
          }
        }
        // e_i (e_j e_k)
        let rhs = Array::make(d, 0)
        for m in 0..<d {
          let a = self.c[j][k][m]
          if a != 0 {
            for t in 0..<d {
              rhs[t] = fp_add(rhs[t], fp_mul(a, self.c[i][m][t], p), p)
            }
          }
        }
        if lhs != rhs {
          return false
        }
      }
    }
  }
  true
}

///|
/// Is the algebra commutative?
pub fn Alg::is_commutative(self : Alg) -> Bool {
  for i in 0..<self.dim {
    for j in 0..<self.dim {
      if self.c[i][j] != self.c[j][i] {
        return false
      }
    }
  }
  true
}

///|
/// `F_p` itself, the terminal one-dimensional algebra.
pub fn alg_field(p : Int32) -> Alg {
  Alg::{ dim: 1, p, c: [[[1]]], }
}

///|
/// The dual numbers `F_p[x]/(x^2)`, the standard non-rigid example:
/// it has genuine first-order deformations.
pub fn alg_dual_numbers(p : Int32) -> Alg {
  let c : Array[Array[Array[Int32]]] = [[[1, 0], [0, 1]], [[0, 1], [0, 0]]]
  Alg::{ dim: 2, p, c, }
}

///|
/// The product algebra `F_p x F_p`, which is separable and therefore rigid:
/// `HH^n = 0` for all `n >= 1`.
pub fn alg_product(p : Int32) -> Alg {
  let c : Array[Array[Array[Int32]]] = [[[1, 0], [0, 0]], [[0, 0], [0, 0]]]
  // e1 * e1 = e1
  c[1][1] = [0, 1]
  Alg::{ dim: 2, p, c, }
}

///|
/// The truncated polynomial algebra `F_p[x]/(x^m)`.
pub fn alg_truncated(p : Int32, m : Int32) -> Alg {
  let c : Array[Array[Array[Int32]]] = []
  for i in 0..<m {
    let row : Array[Array[Int32]] = []
    for j in 0..<m {
      let v = Array::make(m, 0)
      if i + j < m {
        v[i + j] = 1
      }
      row.push(v)
    }
    c.push(row)
  }
  Alg::{ dim: m, p, c, }
}

///|
/// Index of a basis tuple in base `d`, most significant digit first.
fn tuple_index(t : Array[Int32], d : Int32) -> Int32 {
  let mut acc = 0
  for x in t {
    acc = acc * d + x
  }
  acc
}

///|
fn index_tuple(idx : Int32, len : Int32, d : Int32) -> Array[Int32] {
  let out = Array::make(len, 0)
  let mut cur = idx
  for k in 0..<len {
    out[len - 1 - k] = cur % d
    cur = cur / d
  }
  out
}

///|
/// Dimension of the Hochschild cochain space `C^n = Hom(A^{tensor n}, A)`,
/// namely `d^{n+1}`.
pub fn Alg::cochain_dim(self : Alg, n : Int32) -> Int32 {
  @core.ipow(self.dim, n + 1)
}

///|
/// The Hochschild differential `delta : C^n -> C^{n+1}` as a matrix,
///
/// ```text
/// (df)(a_0..a_n) = a_0 f(a_1..a_n)
///                + sum_i (-1)^{i+1} f(a_0..a_i a_{i+1}..a_n)
///                + (-1)^{n+1} f(a_0..a_{n-1}) a_n .
/// ```
///
/// Rows are indexed by `(input tuple, output basis)`.  Associativity of `A`
/// is exactly the statement `delta^2 = 0`, which the tests verify.
pub fn Alg::hochschild_diff(self : Alg, n : Int32) -> Array[Array[Int32]] {
  let d = self.dim
  let p = self.p
  let src_dim = @core.ipow(d, n + 1)
  let dst_dim = @core.ipow(d, n + 2)
  let mat = fp_mat_zero(dst_dim, src_dim)
  let ninputs = @core.ipow(d, n)
  for src in 0..<src_dim {
    let t = index_tuple(src / d, n, d)
    let k = src % d
    for uidx in 0..<@core.ipow(d, n + 1) {
      let u = index_tuple(uidx, n + 1, d)
      let val = Array::make(d, 0)
      // term 1: a_0 * f(a_1..a_n)
      let mut match1 = true
      for i in 0..<n {
        if u[i + 1] != t[i] {
          match1 = false
        }
      }
      if match1 {
        for m in 0..<d {
          val[m] = fp_add(val[m], self.c[u[0]][k][m], p)
        }
      }
      // middle terms: multiply a_i a_{i+1} inside f
      for i in 0..<n {
        let sign = if i % 2 == 0 { p - 1 } else { 1 }
        let rest : Array[Int32] = []
        for j in 0..<=n {
          if j < i {
            rest.push(u[j])
          } else if j > i + 1 {
            rest.push(u[j])
          }
        }
        // rest has length n-1; insert each basis element m at position i
        for m in 0..<d {
          let cand : Array[Int32] = []
          for j in 0..<i {
            cand.push(rest[j])
          }
          cand.push(m)
          for j in i..<rest.length() {
            cand.push(rest[j])
          }
          let mut same = true
          for j in 0..<n {
            if cand[j] != t[j] {
              same = false
            }
          }
          if same {
            let coeff = fp_mul(sign, self.c[u[i]][u[i + 1]][m], p)
            if coeff != 0 {
              val[k] = fp_add(val[k], coeff, p)
            }
          }
        }
      }
      // last term: (-1)^{n+1} f(a_0..a_{n-1}) * a_n
      let mut match2 = true
      for i in 0..<n {
        if u[i] != t[i] {
          match2 = false
        }
      }
      if match2 {
        let sign = if (n + 1) % 2 == 0 { 1 } else { p - 1 }
        for m in 0..<d {
          val[m] = fp_add(val[m], fp_mul(sign, self.c[k][u[n]][m], p), p)
        }
      }
      for m in 0..<d {
        if val[m] != 0 {
          let row = uidx * d + m
          mat[row][src] = fp_norm(mat[row][src] + val[m], p)
        }
      }
    }
  }
  let _ = ninputs
  mat
}

///|
/// `dim HH^n(A,A) = dim ker delta^n - dim im delta^{n-1}`.
/// `HH^0` is the centre, `HH^1` outer derivations, `HH^2` first-order
/// deformations, `HH^3` the obstruction space.
pub fn Alg::hh_dim(self : Alg, n : Int32) -> Int32 {
  let dn = self.hochschild_diff(n)
  if n == 0 {
    fp_kernel(dn, self.p).length()
  } else {
    let prev = self.hochschild_diff(n - 1)
    fp_homology_dim(prev, dn, self.p)
  }
}

///|
/// Verify `delta^{n+1} delta^n = 0`, which holds iff `A` is associative.
pub fn Alg::check_d2(self : Alg, n : Int32) -> Bool {
  let d1 = self.hochschild_diff(n)
  let d2 = self.hochschild_diff(n + 1)
  let prod = fp_matmul(d2, d1, self.p)
  for row in prod {
    for x in row {
      if x != 0 {
        return false
      }
    }
  }
  true
}

///|
/// The Gerstenhaber obstruction of a first-order deformation `mu_1`:
///
/// ```text
/// ob(a,b,c) = mu_1(mu_1(a,b), c) - mu_1(a, mu_1(b,c)).
/// ```
///
/// This is a Hochschild 3-cocycle.  The deformation extends to second
/// order exactly when `ob` is a coboundary, i.e. lies in the image of
/// `delta^2`.  That membership test is a linear system, hence decidable.
pub fn Alg::gerstenhaber_obstruction(
  self : Alg,
  mu1 : Array[Array[Array[Int32]]],
) -> Array[Int32] {
  let d = self.dim
  let p = self.p
  // mu1[i][j] is the value vector of mu_1(e_i, e_j)
  let out = Array::make(d * d * d * d, 0)
  for i in 0..<d {
    for j in 0..<d {
      for k in 0..<d {
        let val = Array::make(d, 0)
        // mu_1(mu_1(e_i,e_j), e_k)
        for m in 0..<d {
          let a = mu1[i][j][m]
          if a != 0 {
            for t in 0..<d {
              val[t] = fp_add(val[t], fp_mul(a, mu1[m][k][t], p), p)
            }
          }
        }
        // - mu_1(e_i, mu_1(e_j,e_k))
        for m in 0..<d {
          let a = mu1[j][k][m]
          if a != 0 {
            for t in 0..<d {
              val[t] = fp_sub(val[t], fp_mul(a, mu1[i][m][t], p), p)
            }
          }
        }
        let base = tuple_index([i, j, k], d) * d
        for t in 0..<d {
          out[base + t] = val[t]
        }
      }
    }
  }
  out
}

///|
/// Does the first-order deformation `mu1` extend to order 2?
/// Decided by solving `delta^2(x) = ob(mu1)` over `F_p`.
pub fn Alg::extends_to_order2(
  self : Alg,
  mu1 : Array[Array[Array[Int32]]],
) -> Bool {
  let ob = self.gerstenhaber_obstruction(mu1)
  let d2 = self.hochschild_diff(2)
  match fp_solve(d2, ob, self.p) {
    Some(_) => true
    None => false
  }
}

///|
/// A basis of the space of first-order deformations `Z^2 = ker delta^2`,
/// each returned as a `d x d` table of value vectors.
pub fn Alg::first_order_space(self : Alg) -> Array[Array[Array[Array[Int32]]]] {
  let d = self.dim
  let ker = fp_kernel(self.hochschild_diff(2), self.p)
  let out : Array[Array[Array[Array[Int32]]]] = []
  for vec in ker {
    let tab : Array[Array[Array[Int32]]] = []
    for i in 0..<d {
      let row : Array[Array[Int32]] = []
      for j in 0..<d {
        let val = Array::make(d, 0)
        let base = (i * d + j) * d
        for t in 0..<d {
          val[t] = vec[base + t]
        }
        row.push(val)
      }
      tab.push(row)
    }
    out.push(tab)
  }
  out
}
