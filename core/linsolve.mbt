///|
/// Reduced row echelon form over `F_p`, in place on a copy.
/// Returns `(rref, pivot_columns, rank)`.  Everything downstream — kernels,
/// images, solvability, homology — is read off this one routine.
pub fn fp_rref(
  rows : Array[Array[Int32]],
  p : Int32,
) -> (Array[Array[Int32]], Array[Int32], Int32) {
  let m = rows.length()
  let n = if m == 0 { 0 } else { rows[0].length() }
  let a : Array[Array[Int32]] = []
  for i in 0..<m {
    let row : Array[Int32] = []
    for j in 0..<n {
      row.push(fp_norm(rows[i][j], p))
    }
    a.push(row)
  }
  let pivots : Array[Int32] = []
  let mut r = 0
  for c in 0..<n {
    if r >= m {
      break
    }
    let mut piv = -1
    for i in r..<m {
      if a[i][c] != 0 && piv < 0 {
        piv = i
      }
    }
    if piv < 0 {
      continue
    }
    let tmp = a[r]
    a[r] = a[piv]
    a[piv] = tmp
    let inv = fp_inv(a[r][c], p)
    for j in 0..<n {
      a[r][j] = fp_mul(a[r][j], inv, p)
    }
    for i in 0..<m {
      if i != r && a[i][c] != 0 {
        let f = a[i][c]
        for j in 0..<n {
          a[i][j] = fp_sub(a[i][j], fp_mul(f, a[r][j], p), p)
        }
      }
    }
    pivots.push(c)
    r = r + 1
  }
  (a, pivots, r)
}

///|
/// A basis of the kernel `{x : A x = 0}`, one vector per free column.
/// Cost `O(m n^2)` field operations, the usual Gauss–Jordan bound.
pub fn fp_kernel(rows : Array[Array[Int32]], p : Int32) -> Array[Array[Int32]] {
  let n = if rows.length() == 0 { 0 } else { rows[0].length() }
  fp_kernel_cols(rows, n, p)
}

///|
/// Kernel of a map `F_p^n -> F_p^m` given by its matrix, with the source
/// dimension `n` supplied explicitly.  This matters for the zero map out of
/// a nonzero space: a matrix with no rows still has an `n`-dimensional
/// kernel, and getting that wrong silently kills `Tor_0` and `H^0`.
pub fn fp_kernel_cols(
  rows : Array[Array[Int32]],
  n : Int32,
  p : Int32,
) -> Array[Array[Int32]] {
  let m = rows.length()
  let (a, pivots, r) = fp_rref(rows, p)
  let is_pivot = Array::make(n, false)
  for c in pivots {
    is_pivot[c] = true
  }
  let basis : Array[Array[Int32]] = []
  for free in 0..<n {
    if is_pivot[free] {
      continue
    }
    let vec = Array::make(n, 0)
    vec[free] = 1
    for k in 0..<r {
      vec[pivots[k]] = fp_norm(-a[k][free], p)
    }
    basis.push(vec)
  }
  let _ = m
  basis
}

///|
/// Solve `A x = b`.  Returns one particular solution, or `None` when the
/// system is inconsistent.  The full solution set is that vector plus the
/// kernel of `A`, which is what makes lifting problems decidable.
pub fn fp_solve(
  rows : Array[Array[Int32]],
  b : Array[Int32],
  p : Int32,
) -> Array[Int32]? {
  let m = rows.length()
  let n = if m == 0 { 0 } else { rows[0].length() }
  let aug : Array[Array[Int32]] = []
  for i in 0..<m {
    let row : Array[Int32] = []
    for j in 0..<n {
      row.push(rows[i][j])
    }
    row.push(b[i])
    aug.push(row)
  }
  let (a, pivots, r) = fp_rref(aug, p)
  // inconsistent iff some pivot sits in the augmented column
  for c in pivots {
    if c == n {
      return None
    }
  }
  let x = Array::make(n, 0)
  for k in 0..<r {
    x[pivots[k]] = a[k][n]
  }
  Some(x)
}

///|
pub fn fp_is_consistent(
  rows : Array[Array[Int32]],
  b : Array[Int32],
  p : Int32,
) -> Bool {
  match fp_solve(rows, b, p) {
    Some(_) => true
    None => false
  }
}

///|
/// A basis of the column space (image) of `A`, as vectors in `F_p^m`.
pub fn fp_image(rows : Array[Array[Int32]], p : Int32) -> Array[Array[Int32]] {
  let m = rows.length()
  let n = if m == 0 { 0 } else { rows[0].length() }
  // transpose, take rref, transpose back
  let t : Array[Array[Int32]] = []
  for j in 0..<n {
    let row : Array[Int32] = []
    for i in 0..<m {
      row.push(rows[i][j])
    }
    t.push(row)
  }
  let (a, _, r) = fp_rref(t, p)
  let out : Array[Array[Int32]] = []
  for k in 0..<r {
    out.push(a[k])
  }
  out
}

///|
/// Is `b` in the span of the rows of `A`?  (Row-space membership.)
pub fn fp_in_row_span(
  rows : Array[Array[Int32]],
  b : Array[Int32],
  p : Int32,
) -> Bool {
  let r0 = fp_rank(rows, p)
  let ext : Array[Array[Int32]] = []
  for r in rows {
    ext.push(r)
  }
  ext.push(b)
  fp_rank(ext, p) == r0
}

///|
/// Dimension of the quotient `ker(B) / im(A)` for composable maps
/// `A : U -> V`, `B : V -> W` with `B A = 0`.  This is the homology of
/// `U -A-> V -B-> W` at `V`, the single quantity every derived computation
/// below reduces to.
pub fn fp_homology_dim(
  a : Array[Array[Int32]],
  b : Array[Array[Int32]],
  p : Int32,
) -> Int32 {
  let rank_a = fp_rank(a, p)
  let ker_b = fp_kernel(b, p)
  // dim(ker B ∩ im A) = rank A + dim ker B - dim(ker B + im A)
  let combined : Array[Array[Int32]] = []
  for r in ker_b {
    combined.push(r)
  }
  for r in fp_image(a, p) {
    combined.push(r)
  }
  let sum_dim = fp_rank(combined, p)
  let inter = rank_a + ker_b.length() - sum_dim
  ker_b.length() - inter
}

///|
/// Dense matrix product over `F_p`.
pub fn fp_matmul(
  a : Array[Array[Int32]],
  b : Array[Array[Int32]],
  p : Int32,
) -> Array[Array[Int32]] {
  let m = a.length()
  let k = if m == 0 { 0 } else { a[0].length() }
  let n = if b.length() == 0 { 0 } else { b[0].length() }
  let out : Array[Array[Int32]] = []
  for i in 0..<m {
    let row = Array::make(n, 0)
    for t in 0..<k {
      let av = a[i][t]
      if av != 0 {
        for j in 0..<n {
          row[j] = fp_norm(row[j] + av * b[t][j], p)
        }
      }
    }
    out.push(row)
  }
  out
}

///|
/// Dense matrix sum over `F_p`.
pub fn fp_matadd(
  a : Array[Array[Int32]],
  b : Array[Array[Int32]],
  p : Int32,
) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for i in 0..<a.length() {
    let row : Array[Int32] = []
    for j in 0..<a[i].length() {
      row.push(fp_add(a[i][j], b[i][j], p))
    }
    out.push(row)
  }
  out
}

///|
pub fn fp_mat_zero(m : Int32, n : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for _ in 0..<m {
    out.push(Array::make(n, 0))
  }
  out
}

///|
pub fn fp_mat_eq(a : Array[Array[Int32]], b : Array[Array[Int32]]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i in 0..<a.length() {
    if a[i].length() != b[i].length() {
      return false
    }
    for j in 0..<a[i].length() {
      if a[i][j] != b[i][j] {
        return false
      }
    }
  }
  true
}
