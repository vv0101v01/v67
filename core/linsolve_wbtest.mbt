///|
test "rref, kernel and image over F_5" {
  let p = 5
  let a = [[1, 2, 3], [2, 4, 6], [1, 1, 1]]
  let (r, pivots, rank) = fp_rref(a, p)
  assert_eq(rank, 2)
  assert_eq(pivots, [0, 1])
  assert_eq(r[2], [0, 0, 0])
  let ker = fp_kernel(a, p)
  assert_eq(ker.length(), 1)
  // A * k = 0 for every kernel basis vector
  for k in ker {
    for row in a {
      let mut s = 0
      for j in 0..<3 {
        s = fp_add(s, fp_mul(row[j], k[j], p), p)
      }
      assert_eq(s, 0)
    }
  }
  assert_eq(fp_image(a, p).length(), 2)
}

///|
test "solving linear systems: consistent, inconsistent, affine solution set" {
  let p = 7
  let a = [[1, 1], [2, 2]]
  match fp_solve(a, [3, 6], p) {
    None => fail("should be consistent")
    Some(x) => {
      assert_eq(fp_add(x[0], x[1], p), 3)
      // general solution = particular + kernel
      let ker = fp_kernel(a, p)
      assert_eq(ker.length(), 1)
      for k in ker {
        let y = [fp_add(x[0], k[0], p), fp_add(x[1], k[1], p)]
        assert_eq(fp_add(y[0], y[1], p), 3)
      }
    }
  }
  // 2*(x+y)=6 is required; b=[3,5] is inconsistent
  assert_true(fp_solve(a, [3, 5], p) is None)
  assert_false(fp_is_consistent(a, [3, 5], p))
}

///|
test "homology dimension: ker B / im A" {
  let p = 5
  // U -A-> V -B-> W with A = [[1],[0]], B = [[0,1]] : BA = 0
  let a = [[1], [0]]
  let b = [[0, 1]]
  assert_eq(fp_matmul(b, a, p), [[0]])
  // ker B = span(e1) = im A, so homology is 0
  assert_eq(fp_homology_dim(a, b, p), 0)
  // now A = 0 : homology = ker B has dimension 1
  assert_eq(fp_homology_dim([[0], [0]], b, p), 1)
  // B = 0 : ker B = V (dim 2), im A dim 1, homology 1
  assert_eq(fp_homology_dim(a, [[0, 0]], p), 1)
}

///|
test "row span membership and matrix arithmetic" {
  let p = 5
  let rows = [[1, 2], [3, 1]]
  assert_true(fp_in_row_span(rows, [4, 3], p))
  assert_true(fp_in_row_span([[1, 2]], [2, 4], p))
  assert_false(fp_in_row_span([[1, 2]], [2, 3], p))
  let a = [[1, 2], [3, 4]]
  let b = [[2, 0], [1, 3]]
  assert_eq(fp_matmul(a, b, p), [[4, 1], [0, 2]])
  assert_eq(fp_matadd(a, b, p), [[3, 2], [4, 2]])
  assert_true(fp_mat_eq(fp_mat_zero(2, 2), [[0, 0], [0, 0]]))
}
