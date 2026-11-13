///|
test "api: mul_basis is the structure constant tensor" {
  let a = alg_dual_numbers(5)
  assert_true(a.is_associative())
  // e0 is the unit, so e0 * e1 = e1
  let prod = a.mul_basis(0, 1)
  assert_eq(prod[1], 1)
  // and the square of the nilpotent generator vanishes
  let sq = a.mul_basis(1, 1)
  for c in sq {
    assert_eq(c, 0)
  }
}

///|
test "api: cochain_dim is d^(n+1)" {
  let a = alg_dual_numbers(3)
  for n in 0..<4 {
    assert_eq(a.cochain_dim(n), @core.ipow(a.dim, n + 1))
  }
}

///|
test "api: the residue of an Artin ring element is its constant term" {
  let r = Artin::new(5, 3)
  let a = [2, 1, 4]
  assert_eq(r.residue(a), 2)
  assert_eq(r.valuation(a), 0)
  let b = [0, 3, 1]
  assert_eq(r.residue(b), 0)
  assert_eq(r.valuation(b), 1)
}
