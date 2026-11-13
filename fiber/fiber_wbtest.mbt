///|
test "standard monomials and Hilbert function of R/(x^2, xy)" {
  let ms = Monomials::new(2, 4)
  // monomials in x,y up to degree 4: 15 of them
  assert_eq(ms.size(), 15)
  let i = monomial_ideal([[2, 0], [1, 1]])
  let q = quotient(ms, i, 5)
  // standard monomials: 1, x, y, y^2, y^3, y^4
  assert_eq(q.dim(), 6)
  assert_eq(q.hilbert(), [1, 2, 1, 1, 1])
  // multiplication by y sends y^k to y^{k+1}
  let my = q.mul_matrix([0, 1])
  let mut rank = 0
  for row in my {
    for x in row {
      if x != 0 {
        rank = rank + 1
      }
    }
  }
  assert_eq(rank, 4)
}

///|
test "transverse intersection: two coordinate axes meet in a point, no higher Tor" {
  let ms = Monomials::new(2, 6)
  // I = (x), J = (y) in F_5[x,y] : the axes meet transversally at the origin
  let i = monomial_ideal([[1, 0]])
  let j = monomial_ideal([[0, 1]])
  let df = derived_fiber(i, j, ms, 5)
  assert_true(df.d2_ok)
  // Tor_0 = R/(x,y) = F_5, dimension 1
  assert_eq(df.tor[0], 1)
  // transversality: all higher Tor vanish
  assert_true(df.transverse)
  assert_eq(df.tor[1], 0)
  assert_eq(df.classical, 1)
  assert_eq(df.serre, 1)
}

///|
test "non-transverse self-intersection: the diagonal meets itself, Tor_1 appears" {
  let ms = Monomials::new(2, 6)
  // I = J = (x) : the "self-intersection" of a divisor.  Classically the
  // fiber is the whole line R/(x); derivedly there is an extra Tor_1,
  // which is the conormal direction -- the derived structure.
  let i = monomial_ideal([[1, 0]])
  let df = derived_fiber(i, i, ms, 5)
  assert_true(df.d2_ok)
  assert_false(df.transverse)
  // Tor_0 = R/(x) has basis 1,y,..,y^6 (7 elements, degrees 0..6).
  // Tor_1 = R/(x) shifted by deg(x)=1, so in degrees <= 6 it has 6.
  assert_eq(df.tor[0], 7)
  assert_eq(df.tor[1], 6)
  assert_eq(df.tor[1], df.tor[0] - 1)
  // The intersection is not proper (excess dimension), so the *total*
  // Serre sum is truncation-dependent.  The invariant statement is the
  // graded Euler characteristic: it vanishes in every positive degree,
  // which is the algebraic signature of excess intersection.
  let cx = tor_complex(taylor(i.gens), quotient(ms, i, 5))
  let g0 = cx.tor_graded(0)
  let g1 = cx.tor_graded(1)
  assert_eq(g0[0] - g1[0], 1)
  for d in 1..<=4 {
    assert_eq(g0[d] - g1[d], 0)
  }
  // the classical count misses the derived direction entirely
  assert_eq(df.classical, 7)
}

///|
test "fat point intersection: multiplicity 2 is seen by Tor_0, and Serre corrects tangency" {
  let ms = Monomials::new(2, 6)
  // I = (y), J = (y - x^2) is not monomial; use the monomial model of a
  // tangency: I = (x^2), J = (x) gives R/(x) with Tor_1 = R/(x) again.
  let i = monomial_ideal([[2, 0]])
  let j = monomial_ideal([[1, 0]])
  let df = derived_fiber(i, j, ms, 5)
  assert_true(df.d2_ok)
  assert_false(df.transverse)
  assert_eq(df.tor[0], 7)
  // Tor_1 is shifted by deg(x^2) = 2, so degrees 2..6 : 5 elements
  assert_eq(df.tor[1], 5)
  assert_eq(df.serre, 2)
  // two distinct axes with multiplicity: (x^2) vs (y^2) is transverse
  // in the sense that the generators form a regular sequence
  let a = monomial_ideal([[2, 0]])
  let b = monomial_ideal([[0, 2]])
  let df2 = derived_fiber(a, b, ms, 5)
  assert_true(df2.d2_ok)
  assert_true(df2.transverse)
  // Tor_0 = R/(x^2,y^2) has basis 1,x,y,xy : dimension 4 = 2*2
  assert_eq(df2.tor[0], 4)
  assert_eq(df2.serre, 4)
  assert_eq(df2.classical, 4)
}

///|
test "Koszul case: a regular sequence gives Tor only up to its length" {
  let ms = Monomials::new(3, 5)
  // I = (x,y,z) is a regular sequence of length 3 in F_5[x,y,z];
  // tensoring with R/(x,y,z) = F_5 gives the exterior algebra:
  // Tor_k = binom(3,k), i.e. [1,3,3,1].
  let i = monomial_ideal([[1, 0, 0], [0, 1, 0], [0, 0, 1]])
  let df = derived_fiber(i, i, ms, 5)
  assert_true(df.d2_ok)
  assert_eq(df.tor, [1, 3, 3, 1])
  assert_false(df.transverse)
  // alternating sum of binomials is 0
  assert_eq(df.serre, 0)
}

///|
test "graded Tor: the derived structure is concentrated in the right degrees" {
  let ms = Monomials::new(2, 4)
  let i = monomial_ideal([[1, 0]])
  let q = quotient(ms, i, 5)
  let cx = tor_complex(taylor(i.gens), q)
  assert_true(cx.check_d2())
  // Tor_0 = R/(x) has one element in each degree 0..4
  assert_eq(cx.tor_graded(0), [1, 1, 1, 1, 1])
  // Tor_1 = R/(x) shifted by deg(x) = 1 : nothing in degree 0
  assert_eq(cx.tor_graded(1), [0, 1, 1, 1, 1])
  // graded dimensions sum to the total
  let mut s = 0
  for x in cx.tor_graded(1) {
    s = s + x
  }
  assert_eq(s, cx.tor_dim(1))
}

///|
test "derived fiber product is symmetric in the two factors" {
  let ms = Monomials::new(2, 5)
  let cases = [
    (monomial_ideal([[1, 0]]), monomial_ideal([[0, 1]])),
    (monomial_ideal([[2, 0]]), monomial_ideal([[0, 2]])),
    (monomial_ideal([[1, 1]]), monomial_ideal([[1, 0]])),
    (monomial_ideal([[2, 0], [1, 1]]), monomial_ideal([[0, 2]])),
  ]
  for (i, j) in cases {
    let a = derived_fiber(i, j, ms, 5)
    let b = derived_fiber(j, i, ms, 5)
    assert_true(a.d2_ok)
    assert_true(b.d2_ok)
    // Tor is symmetric: Tor^R_k(M,N) = Tor^R_k(N,M).  The two Taylor
    // resolutions have different lengths, so pad with zeros first.
    assert_eq(pad_zeros(a.tor, 6), pad_zeros(b.tor, 6))
    assert_eq(a.serre, b.serre)
    assert_eq(a.transverse, b.transverse)
  }
}

///|
fn pad_zeros(xs : Array[Int32], n : Int32) -> Array[Int32] {
  let out = Array::make(n, 0)
  for i in 0..<xs.length() {
    if i < n {
      out[i] = xs[i]
    }
  }
  out
}
