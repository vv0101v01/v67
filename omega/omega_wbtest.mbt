///|
test "free groupoid: reduced words compose associatively and invert" {
  let g = graph_wedge2()
  // (a b) ; (b⁻¹ a¹) = id
  let p = match g.path(0, [0, 1]) {
    Some(x) => x
    None => fail("path")
  }
  let q = match g.path(0, [-2, -1]) {
    Some(x) => x
    None => fail("path")
  }
  match p.then(q) {
    Some(r) => assert_eq(r.word, [])
    None => fail("compose")
  }
  // reduction is idempotent and normalising
  // 0 cancels -1, then 1 cancels -2, leaving the reduced word [1, 0]
  assert_eq(reduce_word([0, -1, 1, -2, 1, 0]), [1, 0])
  assert_eq(reduce_word([0, -1]), [])
  assert_eq(reduce_word([-1, 0]), [])
  // inverse really inverts, on both sides
  let inv = p.inverse()
  match p.then(inv) {
    Some(r) => assert_eq(r, Path1::id(0))
    None => fail("inv")
  }
  match inv.then(p) {
    Some(r) => assert_eq(r, Path1::id(0))
    None => fail("inv")
  }
  // associativity on a triple of composable words
  let a = match g.path(0, [0]) {
    Some(x) => x
    None => fail("a")
  }
  let b = match g.path(0, [1]) {
    Some(x) => x
    None => fail("b")
  }
  let c = match g.path(0, [-1]) {
    Some(x) => x
    None => fail("c")
  }
  let lhs = match (a.then(b), b.then(c)) {
    (Some(ab), Some(bc)) => (ab.then(c), a.then(bc))
    _ => fail("comp")
  }
  assert_eq(lhs.0, lhs.1)
}

///|
test "fundamental group rank: circle 1, figure eight 2, theta 2, tree 0" {
  assert_eq(graph_circle().pi1_rank(0), 1)
  assert_eq(graph_wedge2().pi1_rank(0), 2)
  assert_eq(graph_theta().pi1_rank(0), 2)
  let tree = Graph::new(4, [(0, 1), (1, 2), (2, 3)])
  assert_eq(tree.pi1_rank(0), 0)
  // Free group F_2 growth: 4 generators, then 3 choices at each step
  // (no immediate backtracking), so 4 + 12 + 36 + 108 = 160 reduced
  // words of length 1..4.  This is the standard growth series of F_2.
  let loops = graph_wedge2().loops(0, 4)
  assert_eq(loops.length(), 4 + 12 + 36 + 108)
  // the circle: only two reduced words per length (all forward / all back)
  let cl = graph_circle().loops(0, 4)
  assert_eq(cl.length(), 8)
}

///|
test "groupoid model: sets satisfy UIP, groups do not" {
  let set3 = discrete_groupoid(3)
  assert_true(set3.check())
  assert_true(set3.is_set())
  assert_eq(set3.path_type(0, 0), [set3.refl(0)])
  assert_eq(set3.path_type(0, 1), [])
  // a nontrivial group as a one-object groupoid violates UIP
  let z2 = group_as_groupoid([[0, 1], [1, 0]], 0)
  assert_true(z2.check())
  assert_false(z2.is_set())
  assert_eq(z2.path_type(0, 0).length(), 2)
  assert_true(z2.is_connected())
  assert_false(z2.is_contractible())
  // path inversion is an involution
  for p in z2.path_type(0, 0) {
    match z2.sym(p) {
      Some(q) =>
        match z2.sym(q) {
          Some(r) => assert_eq(r, p)
          None => fail("sym")
        }
      None => fail("sym")
    }
  }
}

///|
test "based path space is contractible, which is why J is sound" {
  // for a set, a group, and a connected groupoid with several objects
  let cases = [
    discrete_groupoid(3),
    group_as_groupoid([[0, 1], [1, 0]], 0),
    codiscrete_groupoid(3),
    group_as_groupoid(gp_cyclic(3).mul, 0),
  ]
  for g in cases {
    assert_true(g.check())
    for a in 0..<g.nobjs {
      let bps = g.based_path_space(a)
      // THE theorem: Σ(x:A), Id(a,x) is contractible
      assert_true(bps.is_contractible())
      assert_true(bps.check())
      // and J satisfies its computation rule at refl
      assert_true(g.check_j_beta(a, 42))
    }
  }
  // The codiscrete groupoid is contractible, hence equivalent to the
  // point, hence a set: all its hom-sets are singletons.  Contractible
  // does not mean "has many paths" -- it means the paths are all equal.
  assert_true(codiscrete_groupoid(4).is_contractible())
  assert_true(codiscrete_groupoid(4).is_set())
}

///|
test "weak 2-group: the pentagon axiom IS the 3-cocycle condition" {
  let g = gp_cyclic(2)
  assert_true(g.check())
  let strict = strict_two_group(g, 2)
  assert_true(strict.is_coherent())
  assert_true(strict.is_normalised())
  assert_eq(strict.pentagon_defects(), 0)
  assert_true(strict.is_strictifiable())
  // Over Z/2 coefficients alpha(1,1,1)=1 IS a cocycle (2*1 = 0 mod 2),
  // so to see the pentagon fail we change the coefficients to Z/3:
  // there 2*1 = 2 != 0, and the pentagon genuinely fails.
  let alpha3 : Array[Array[Array[Int32]]] = [[[0, 0], [0, 0]], [[0, 0], [0, 1]]]
  let w = WeakTwoGroup::new(g, 3, [[0, 1, 2], [0, 1, 2]], alpha3)
  assert_true(w.is_normalised())
  assert_true(w.pentagon_defects() > 0)
  assert_false(w.is_coherent())
  // over Z/2 the same shape is coherent
  let w2 = WeakTwoGroup::new(g, 2, [[0, 1], [0, 1]], alpha3)
  assert_true(w2.is_coherent())
}

///|
test "H^3(Z/2, Z/2) = Z/2: the nontrivial weak 2-group is not strictifiable" {
  let g = gp_cyclic(2)
  let (z3, b3, h3) = h3_order(g, 2)
  // one free slot (1,1,1), so Z^3 has 2 elements, B^3 has 1
  assert_eq(z3, 2)
  assert_eq(b3, 1)
  assert_eq(h3, 2)
  // the nontrivial class: alpha(1,1,1) = 1
  let action = [[0, 1], [0, 1]]
  let alpha : Array[Array[Array[Int32]]] = [[[0, 0], [0, 0]], [[0, 0], [0, 1]]]
  let w = WeakTwoGroup::new(g, 2, action, alpha)
  // it IS coherent (a genuine weak 2-group) ...
  assert_true(w.is_coherent())
  // ... but NOT strictifiable: no coboundary kills the associator
  assert_false(w.is_strictifiable())
  // while the trivial class is
  assert_true(strict_two_group(g, 2).is_strictifiable())
}

///|
test "regauging by a coboundary preserves coherence and the cohomology class" {
  let g = gp_cyclic(2)
  let action = [[0, 1], [0, 1]]
  let alpha : Array[Array[Array[Int32]]] = [[[0, 0], [0, 0]], [[0, 0], [0, 1]]]
  let w = WeakTwoGroup::new(g, 2, action, alpha)
  assert_true(w.is_coherent())
  for b in 0..<2 {
    let beta = [[0, 0], [0, b]]
    let w2 = w.regauge(beta)
    // coherence is preserved
    assert_true(w2.is_coherent())
    // and so is the (non)strictifiability, i.e. the class in H^3
    assert_eq(w.is_strictifiable(), w2.is_strictifiable())
  }
  // regauging the strict group by any cochain stays strictifiable
  let s = strict_two_group(g, 2)
  for b in 0..<2 {
    let s2 = s.regauge([[0, 0], [0, b]])
    assert_true(s2.is_coherent())
    assert_true(s2.is_strictifiable())
  }
}

///|
test "H^3(Z/3, Z/3) = Z/3 and H^3(Z/2, Z/3) is trivial" {
  // Z/3 with trivial action: H^3 = Z/3, three weak 2-groups
  let (z3, b3, h3) = h3_order(gp_cyclic(3), 3)
  assert_eq(h3, 3)
  assert_eq(z3, 3 * b3)
  // coprime orders: H^3(Z/2, Z/3) = 0, every weak structure strictifies
  let (z3b, b3b, h3b) = h3_order(gp_cyclic(2), 3)
  assert_eq(h3b, 1)
  assert_eq(z3b, b3b)
  // With G = Z/2 the only normalised slot is (1,1,1), and the pentagon
  // demands 2*a = 0 in Z/3, forcing a = 0.  So every coherent associator
  // is zero: H^3 vanishes, exactly as the coprime-order theorem predicts.
  let action = [[0, 1, 2], [0, 1, 2]]
  let cohs = three_cocycles(gp_cyclic(2), 3, action)
  assert_eq(cohs.length(), 1)
  let w = WeakTwoGroup::new(gp_cyclic(2), 3, action, cohs[0])
  assert_true(w.is_coherent())
  assert_true(w.is_strictifiable())
}

///|
test "strict omega-category laws: associativity, units, inverses, interchange" {
  // a group viewed as a 2-level globular set: one 0-cell, n 1-cells,
  // and only identity 2-cells.  Composition at level 0 is the group law.
  let g = gp_cyclic(3)
  let dims = [1, 3, 3]
  let src = [[], [0, 0, 0], [0, 1, 2]]
  let tgt = [[], [0, 0, 0], [0, 1, 2]]
  let shape = Globular::new(dims, src, tgt)
  assert_true(shape.check())
  assert_true(shape.is_truncated(2))
  assert_false(shape.is_truncated(1))
  let comp : Array[Array[Array[Int32]]] = [
    g.mul,
    [[0, -1, -1], [-1, 1, -1], [-1, -1, 2]],
  ]
  let ident = [[0], [0, 1, 2]]
  let omega = StrictOmega::new(shape, comp, ident)
  assert_true(omega.check_associative())
  assert_true(omega.check_units())
  assert_true(omega.check_inverses())
  assert_true(omega.check_interchange())
}
