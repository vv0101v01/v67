///|
test "little cubes: validity, disjointness and exact composition" {
  let u = unit_cube(2)
  assert_true(u.valid())
  assert_true(u.contains(u))
  // two half-cubes along axis 0 are disjoint and both inside the unit square
  let bin = binary_op(2)
  assert_true(bin.valid())
  assert_eq(bin.arity(), 2)
  assert_true(u.contains(bin.cubes[0]))
  assert_true(u.contains(bin.cubes[1]))
  assert_true(bin.cubes[0].disjoint(bin.cubes[1]))
  // overlapping cubes are rejected
  let a = LittleCube::new([0, 0], [3, 3], 4)
  let b = LittleCube::new([1, 1], [3, 3], 4)
  assert_false(a.disjoint(b))
  assert_false(Config::new(2, [a, b]).valid())
  // a cube sticking out of the unit square is invalid
  assert_false(LittleCube::new([2, 0], [3, 1], 4).valid())
  // composition is exact: inserting a half-cube into a half-cube gives a
  // quarter-cube, with the denominator multiplying
  let half = LittleCube::new([0], [1], 2)
  let q = half.compose(half)
  assert_eq(q.den, 4)
  assert_eq(q.side, [1])
  assert_eq(q.lo, [0])
  assert_true(half.contains(q))
  // and the shifted half composed with a shifted half lands at 3/4
  let half_hi = LittleCube::new([1], [1], 2)
  let q3 = half_hi.compose(half_hi)
  assert_eq(q3.lo, [3])
  assert_eq(q3.den, 4)
}

///|
test "operad axioms: associativity, unit, and both equivariances" {
  for n in 1..<4 {
    let c = ternary_op(n)
    let b = binary_op(n)
    let u = operad_unit(n)
    assert_true(c.valid())
    assert_true(b.valid())
    assert_true(u.valid())
    // unit laws
    assert_true(check_unit(c))
    assert_true(check_unit(b))
    assert_true(check_unit(u))
    // associativity with a mixture of arities: 3 = 2 + 0 + 1 is not
    // possible, so use ds of arities 2, 1, 2 giving total 5
    let ds = [b, u, b]
    let es = [b, u, u, b, u]
    assert_true(check_associativity(c, ds, es))
    // associativity of binary operations: the two bracketings of four inputs
    let ds2 = [b, b]
    let es2 = [b, u, u, b]
    assert_true(check_associativity(b, ds2, es2))
    // equivariance in the outer variable, over all permutations of 3 inputs
    let sigmas : Array[Array[Int32]] = [
      [0, 1, 2],
      [0, 2, 1],
      [1, 0, 2],
      [1, 2, 0],
      [2, 0, 1],
      [2, 1, 0],
    ]
    for s in sigmas {
      assert_true(check_equivariance_outer(c, ds, s))
    }
    // equivariance in the inner variables
    assert_true(check_equivariance_inner(c, ds, [[1, 0], [0], [1, 0]]))
    assert_true(check_equivariance_inner(c, ds, [[0, 1], [0], [0, 1]]))
    // composition preserves disjointness
    assert_true(compose_preserves_valid(c, ds))
    assert_true(compose_preserves_valid(b, [c, c]))
  }
}

///|
test "the two bracketings of a ternary product are different points of C_n(3)" {
  // In the operad, (x*y)*z and x*(y*z) are DIFFERENT points of C_n(3):
  // associativity holds only up to homotopy, which is exactly why E_1 is
  // not a monoid.  The exact integer model makes the difference visible.
  let b = binary_op(1)
  let u = operad_unit(1)
  let left = match b.compose([b, u]) {
    None => fail("compose")
    Some(x) => x
  }
  let right = match b.compose([u, b]) {
    None => fail("compose")
    Some(x) => x
  }
  assert_true(left.valid())
  assert_true(right.valid())
  assert_eq(left.arity(), 3)
  assert_eq(right.arity(), 3)
  assert_false(left == right)
  // but they become equal after composing with the associativity path's
  // endpoint data: both have the same three cubes up to reparametrisation
  // of the intervals, which is what a homotopy rescales.
  assert_true(left.cubes[0].same_region(LittleCube::new([0], [1], 4)))
  assert_true(right.cubes[2].same_region(LittleCube::new([3], [1], 4)))
  // and no reordering makes them the same configuration
  assert_false(left.cubes[2].same_region(right.cubes[2]))
}

///|
test "pi_0 of the little cubes spaces: k! in dimension 1, a point above" {
  // dimension 1: the order of the points on a line is invariant
  assert_eq(pi0_config(1, 4, 2), factorial(2))
  assert_eq(pi0_config(1, 4, 3), factorial(3))
  assert_eq(pi0_config(1, 5, 3), factorial(3))
  // dimension 2 and 3: there is room to move around, so the space is
  // connected -- this is the E_2 commutativity phenomenon
  assert_eq(pi0_config(2, 3, 2), 1)
  assert_eq(pi0_config(2, 3, 3), 1)
  assert_eq(pi0_config(3, 2, 2), 1)
  // the swap is impossible on a line and possible in the plane
  assert_false(can_swap(1, 5))
  assert_true(can_swap(2, 3))
  assert_true(can_swap(3, 2))
  // with a single token the space is always connected
  assert_eq(pi0_config(1, 4, 1), 1)
  assert_eq(pi0_config(2, 3, 1), 1)
}

///|
test "component sizes match the ordered configuration count" {
  // In dimension 1 each component is a chamber of the braid arrangement:
  // all k! chambers have the same number of grid placements.
  let sizes = config_components(1, 4, 3)
  assert_eq(sizes.length(), 6)
  let each = sizes[0]
  for s in sizes {
    assert_eq(s, each)
  }
  // total number of placements is 4*3*2
  assert_eq(each * 6, 24)
  // in dimension 2 there is one component containing everything: 9*8 = 72
  let plane = config_components(2, 3, 2)
  assert_eq(plane.length(), 1)
  assert_eq(plane[0], 72)
}

///|
test "Dunn additivity: the board product of E_m and E_n lands in E_{m+n}" {
  let a = binary_op(1)
  let b = binary_op(2)
  let prod = board_product(a, b)
  assert_eq(prod.dim, 3)
  assert_eq(prod.arity(), 4)
  assert_true(prod.valid())
  // volumes multiply: a fills length 1, b fills area 1/2, so the board
  // product fills volume 1/2.  All four cubes share the denominator 16.
  let den = prod.cubes[0].den
  assert_eq(den, 16)
  let mut vol = 0
  for c in prod.cubes {
    assert_eq(c.den, den)
    vol = vol + c.side[0] * c.side[1] * c.side[2]
  }
  assert_eq(vol * 2, den * den * den)
  // the board product of units is a unit
  let u1 = operad_unit(1)
  let u2 = operad_unit(2)
  let up = board_product(u1, u2)
  assert_eq(up.dim, 3)
  assert_eq(up.arity(), 1)
  assert_true(up.valid())
  assert_true(check_unit(up))
  // and the board product is compatible with composition in each factor:
  // (a ∘ a') × (b ∘ b') = (a × b) ∘ (a' × b') up to the block ordering
  let aa = match a.compose([a, u1]) {
    None => fail("a")
    Some(x) => x
  }
  let bb = match b.compose([b, u2]) {
    None => fail("b")
    Some(x) => x
  }
  let lhs = board_product(aa, bb)
  assert_true(lhs.valid())
  assert_eq(lhs.arity(), aa.arity() * bb.arity())
  // every cube of the product is contained in the corresponding product
  // of outer cubes
  let outer = board_product(a, b)
  for c in lhs.cubes {
    let mut inside = false
    for o in outer.cubes {
      if o.contains(c) {
        inside = true
      }
    }
    assert_true(inside)
  }
}

///|
fn lcg(s : Int32) -> Int32 {
  (s * 1103 + 12345) % 32768
}

///|
test "a random configuration is either valid or rejected, never ambiguous" {
  // a deterministic pseudo-random sweep over 2-cube configurations in the
  // unit square on a 6-grid: membership must agree with the bit-level
  // occupancy test
  let mut seed = 12345
  let mut valid_count = 0
  for _ in 0..<200 {
    let cubes : Array[LittleCube] = []
    for _ in 0..<2 {
      seed = lcg(seed)
      let x = seed % 5
      seed = lcg(seed)
      let y = seed / 7 % 5
      seed = lcg(seed)
      let w = 1 + seed / 13 % 2
      seed = lcg(seed)
      let h = 1 + seed / 17 % 2
      cubes.push(LittleCube::new([x, y], [w, h], 6))
    }
    let cfg = Config::new(2, cubes)
    let ok = cfg.valid()
    if ok {
      valid_count = valid_count + 1
      // independent check: rasterise both cubes on the 6x6 grid and
      // confirm the rasters do not overlap
      let mut clash = false
      for cx in 0..<6 {
        for cy in 0..<6 {
          let mut hits = 0
          for c in cubes {
            if cx >= c.lo[0] &&
              cx < c.lo[0] + c.side[0] &&
              cy >= c.lo[1] &&
              cy < c.lo[1] + c.side[1] {
              hits = hits + 1
            }
          }
          if hits > 1 {
            clash = true
          }
        }
      }
      assert_false(clash)
    }
  }
  assert_true(valid_count > 0)
}
