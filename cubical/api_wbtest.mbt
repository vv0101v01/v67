///|
test "api: apply_inv undoes apply" {
  let e = Iso::new(3, 3, [1, 2, 0], [2, 0, 1])
  for k in 0..<3 {
    assert_eq(e.apply_inv(e.apply(k)), k)
    assert_eq(e.apply(e.apply_inv(k)), k)
  }
  let id = Iso::id(4)
  for k in 0..<4 {
    assert_eq(id.apply_inv(k), k)
  }
}

///|
test "api: ty_iso_id is the identity isomorphism of a type" {
  let t = const_ty(2, 3)
  let e = ty_iso_id(t)
  assert_true(check_ty_iso(t, t, e))
}

///|
test "api: general dimension substitution extends the endpoint case" {
  let t = DAnd(DVar(0), DOr(DVar(1), DOne))
  // substituting the generic point is the identity
  assert_true(dim_eq(dim_subst(t, 0, DVar(0)), t))
  // substituting 1 collapses the conjunction
  assert_true(dim_eq(dim_subst(t, 0, DOne), DOr(DVar(1), DOne)))
  assert_true(dim_eq(dim_subst(t, 1, DZero), DVar(0)))
}
