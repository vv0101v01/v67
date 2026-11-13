///|
test "api: is_normal and all_reducts agree" {
  // the single rule f(f(x)) → x
  let r = rule(app("f", [app("f", [v(0)])]), v(0))
  let rules = [r]
  let t = app("f", [app("f", [constant("a")])])
  assert_true(!is_normal(t, rules))
  assert_eq(all_reducts(t, rules).length(), 1)
  let n = constant("a")
  assert_true(is_normal(n, rules))
  assert_eq(all_reducts(n, rules).length(), 0)
}
