///|
test "api: normalize_closed evaluates a closed term to a literal" {
  // (λx:Bool. x) true  ⟶  true
  let t = App(Lam(Bool, Var(0)), BoolLit(true))
  assert_eq(normalize_closed(t), BoolLit(true))
  // 2 + 3 ⟶ 5
  assert_eq(normalize_closed(Add(NatLit(2), NatLit(3))), NatLit(5))
  // if true then 1 else 2 ⟶ 1
  assert_eq(
    normalize_closed(If(BoolLit(true), NatLit(1), NatLit(2))),
    NatLit(1),
  )
}
