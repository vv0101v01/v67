///|
/// Build every cofibration over `n` directions up to a given size, so the
/// structural procedure can be checked against the exhaustive oracle on
/// *all* of them, not on examples.
fn cof_universe(n : Int32) -> Array[Cof] {
  let base : Array[Cof] = [CTop, CBot]
  for i in 0..<n {
    base.push(face_cof(i, 0))
    base.push(face_cof(i, 1))
  }
  let all : Array[Cof] = []
  for a in base {
    all.push(a)
  }
  for a in base {
    for b in base {
      all.push(CAnd(a, b))
      all.push(COr(a, b))
    }
  }
  all
}

///|
test "faces: structural entailment agrees with the exhaustive oracle" {
  // 2 directions: 6 atoms, 78 formulas, 6084 ordered pairs, each decided
  // twice — once by 3^n enumeration, once structurally.
  let us = cof_universe(2)
  let mut pairs = 0
  for a in us {
    for b in us {
      assert_eq(cof_leq(a, b), cof_entails(a, b, 2))
      pairs = pairs + 1
    }
  }
  assert_eq(pairs, 6084)
}

///|
test "faces: agreement on three directions, with dimension terms" {
  let atoms : Array[Cof] = [
    CTop,
    CBot,
    face_cof(0, 0),
    face_cof(0, 1),
    face_cof(1, 0),
    face_cof(1, 1),
    face_cof(2, 0),
    face_cof(2, 1),
    CEq(DAnd(DVar(0), DVar(1)), 1),
    CEq(DOr(DVar(0), DVar(1)), 0),
    CEq(DNot(DVar(2)), 1),
    CEq(DAnd(DVar(0), DNot(DVar(1))), 0),
  ]
  let us : Array[Cof] = []
  for a in atoms {
    us.push(a)
  }
  for a in atoms {
    for b in atoms {
      us.push(CAnd(a, b))
      us.push(COr(a, b))
    }
  }
  for a in us {
    for b in us {
      assert_eq(cof_leq(a, b), cof_entails(a, b, 3))
    }
  }
}

///|
test "faces: the lattice is not Boolean — the boundary is not the whole" {
  let boundary = COr(face_cof(0, 0), face_cof(0, 1))
  assert_false(cof_is_true(boundary))
  assert_false(cof_is_false(boundary))
  assert_true(cof_leq(face_cof(0, 0), boundary))
  assert_true(cof_leq(boundary, boundary))
  // and a face below a disjunction is below one disjunct: join-primeness
  let f = CAnd(face_cof(0, 1), face_cof(1, 0))
  assert_true(cof_leq(f, boundary))
  assert_true(cof_leq(f, face_cof(0, 1)))
}

///|
test "faces: contradiction is bottom, and bottom entails everything" {
  let clash = CAnd(face_cof(0, 0), face_cof(0, 1))
  assert_true(cof_is_false(clash))
  assert_true(cof_leq(clash, CBot))
  assert_true(cof_leq(CBot, face_cof(7, 1)))
  assert_true(cof_leq(CBot, CBot))
}

///|
test "faces: De Morgan expansion of dimension terms" {
  // (i ∧ j = 0) is the union of two faces, not one
  let a = CEq(DAnd(DVar(0), DVar(1)), 0)
  let b = COr(face_cof(0, 0), face_cof(1, 0))
  assert_true(cof_same(a, b))
  // (i ∨ j = 1) likewise
  assert_true(
    cof_same(CEq(DOr(DVar(0), DVar(1)), 1), COr(face_cof(0, 1), face_cof(1, 1))),
  )
  // negation swaps the endpoint
  assert_true(cof_same(CEq(DNot(DVar(3)), 1), face_cof(3, 0)))
  // constants
  assert_true(cof_is_true(CEq(DZero, 0)))
  assert_true(cof_is_false(CEq(DZero, 1)))
}

///|
test "faces: entailment is unbounded in the dimension supply" {
  // Direction 10_000 does not exist as far as the 3^n oracle is concerned:
  // deciding anything about it would need 3^10001 subcubes.  Structurally
  // it is a two-literal check.
  let hi = face_cof(10000, 1)
  let lo = face_cof(9999, 0)
  assert_true(cof_leq(CAnd(hi, lo), hi))
  assert_false(cof_leq(hi, lo))
  assert_true(cof_is_false(CAnd(hi, face_cof(10000, 0))))
  assert_true(cof_leq(hi, COr(hi, lo)))
  assert_false(cof_is_true(COr(hi, face_cof(10000, 0))))
  // a large conjunction still decides instantly
  let mut big = CTop
  for i in 0..<200 {
    big = CAnd(big, face_cof(5000 + i, i % 2))
  }
  assert_true(cof_leq(big, face_cof(5100, 0)))
  assert_false(cof_leq(big, face_cof(5100, 1)))
  assert_false(cof_is_false(big))
}
