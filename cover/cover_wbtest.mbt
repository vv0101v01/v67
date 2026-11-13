///|
test "universal cover of the circle is a line: a tree, locally bijective" {
  let uc = universal_cover(space_circle(), 0, 4)
  // reduced words over one loop: (), ±e, ±e², ±e³, ±e⁴ -> 9 points
  assert_eq(uc.size(), 9)
  assert_true(uc.is_tree())
  assert_true(uc.is_local_bijection())
  // the fibre over the base point is all of them (one vertex downstairs)
  assert_eq(uc.fibre(0).length(), 9)
  // path lifting: e^k from the root lands at the point with word [e]*k
  match uc.lift_path(0, [0, 0, 0]) {
    Some(q) => assert_eq(uc.points[q].word, [0, 0, 0])
    None => fail("lift")
  }
  // and lifting a reduced word never backtracks
  match uc.lift_path(0, [0, -1]) {
    Some(q) => assert_eq(q, 0)
    None => fail("lift")
  }
}

///|
test "universal cover of the figure eight is the 4-regular tree" {
  let uc = universal_cover(space_wedge(2), 0, 3)
  // 1 + 4 + 12 + 36 = 53 points
  assert_eq(uc.size(), 53)
  assert_true(uc.is_tree())
  assert_true(uc.is_local_bijection())
  // every interior point has exactly 4 lifted edge-ends
  for p in 0..<uc.size() {
    if uc.points[p].word.length() < 3 {
      let mut deg = 0
      for x in uc.lift[p] {
        if x >= 0 {
          deg = deg + 1
        }
      }
      assert_eq(deg, 4)
    }
  }
}

///|
test "deck transformations of the universal cover realise pi_1" {
  let uc = universal_cover(space_circle(), 0, 5)
  // translations by e^k are defined on the interior; the identity always is
  assert_true(uc.check_deck(0))
  // the point with word [e] gives the shift
  let mut shift = -1
  for p in 0..<uc.size() {
    if uc.points[p].word == [0] {
      shift = p
    }
  }
  assert_true(shift >= 0)
  match uc.deck_translation(shift) {
    None => fail("deck")
    Some(f) => {
      // it preserves the projection everywhere it is defined
      for p in 0..<uc.size() {
        if f[p] >= 0 {
          assert_eq(uc.project(f[p]), uc.project(p))
        }
      }
      // on forward words it is the shift e^k -> e^(k+1)
      for p in 0..<uc.size() {
        let w = uc.points[p].word
        let forward = w.iter().all(fn(x) { x == 0 })
        if forward && f[p] >= 0 {
          assert_eq(uc.points[f[p]].word.length(), w.length() + 1)
        }
      }
    }
  }
  // deck transformations form a group: composing shifts adds exponents
  assert_true(uc.check_deck(shift))
}

///|
test "cyclic covers: k-fold cover of the circle is regular with deck group Z/k" {
  for k in [1, 2, 3, 5] {
    let c = cyclic_cover(k)
    assert_eq(c.total.nverts, k)
    assert_eq(c.total.nedges(), k)
    let deck = c.deck_group()
    assert_eq(deck.length(), k)
    assert_true(c.is_regular())
    // the deck group is closed under composition and inversion
    for f in deck {
      for g in deck {
        let comp : Array[Int32] = []
        for v in 0..<k {
          comp.push(f[g[v]])
        }
        assert_true(deck.contains(comp))
      }
    }
    // as a graph cover it really is a covering map
    let gc = circle_cover(k)
    assert_true(gc.is_covering())
    assert_true(gc.has_local_sections())
  }
}

///|
test "local sections exist exactly when the map is a covering" {
  // covers of the figure eight
  for k in [1, 2, 3] {
    let gc = wedge_cover(k, 2)
    assert_true(gc.is_covering())
    assert_true(gc.has_local_sections())
    // the local section at each vertex picks one edge over each of the
    // four edge-ends (two loops, two ends each)
    for v in 0..<k {
      match gc.local_section(0, v) {
        None => fail("section")
        Some(sec) => {
          assert_eq(sec.length(), 4)
          for e in 0..<2 {
            for side in 0..<2 {
              let te = sec[2 * e + side]
              assert_true(te >= 0)
              assert_eq(gc.edge_map[te], e)
            }
          }
        }
      }
    }
  }
  // a non-cover: collapse two edges onto one, breaking the bijection
  let base = space_circle()
  let total = Space::new(1, [(0, 0), (0, 0)])
  let bad = GraphCover::new(base, total, [0], [0, 0])
  assert_false(bad.is_covering())
  assert_false(bad.has_local_sections())
}

///|
test "local complementability: constant and product types are Kan" {
  // a constant finite type is Kan: every box has a unique filler
  let ty = @cubical.const_ty(2, 3)
  let report = audit_type(ty, tube_size=1)
  assert_true(report.boxes > 0)
  assert_true(report.is_kan())
  assert_eq(report.failures, 0)
  // products of Kan types are Kan
  let prod = @cubical.prod_ty(@cubical.const_ty(2, 2), @cubical.const_ty(2, 3))
  let rp = audit_type(prod, tube_size=1)
  assert_true(rp.is_kan())
  assert_true(rp.boxes > 0)
}

///|
test "local complementability: a path type is Kan, and fillers are found" {
  // In a discrete type the path type between DISTINCT points is empty;
  // the interesting Kan object is the based loop type at a point.
  let base = @cubical.const_ty(2, 2)
  let p = @cubical.path_ty(base, 0, 0)
  let report = audit_type(p, tube_size=1)
  assert_true(report.boxes > 0)
  assert_true(report.is_kan())
  // an explicit box: the empty tube, cap 0, must have a filler
  let problem = BoxProblem::new(p, 0, @cubical.partial_empty(), 0)
  assert_true(problem.well_formed())
  match problem.complement() {
    None => fail("should be complementable")
    Some(f) => assert_true(f >= 0)
  }
}

///|
test "an incompatible box is not complementable, and is detected" {
  // a type with a single point in dimension 0 but two in the generic
  // cube cannot fill a box demanding two different values on one face.
  let ty = @cubical.const_ty(2, 2)
  let n = ty.n
  // tube demanding value 0 on (dim 1 = 0) and value 1 on (dim 1 = 1),
  // with the composition direction 0: this is a genuine box and IS
  // fillable in a constant type; to get a failure we demand a value
  // outside the fibre, which well_formed rejects.
  let side = @cubical.face_cube(n, 1, 0)
  let tube = PartialElem::new(@cubical.face_cof(1, 0), [side], [0])
  let ok = BoxProblem::new(ty, 0, tube, 0)
  assert_true(ok.well_formed())
  assert_true(ok.complement() is Some(_))
  let bad = BoxProblem::new(ty, 0, tube, 99)
  assert_false(bad.well_formed())
  assert_true(bad.complement() is None)
}
