///|
test "api: level_dim is the size of the Taylor level" {
  let ms = Monomials::new(2, 4)
  let i = monomial_ideal([[1, 0]])
  let j = monomial_ideal([[0, 1]])
  let t = taylor(i.gens)
  let q = quotient(ms, j, 2)
  let cx = tor_complex(t, q)
  for k in 0..<cx.levels.length() {
    assert_eq(cx.level_dim(k), cx.levels[k].length())
  }
  assert_eq(cx.level_dim(-1), 0)
  assert_eq(cx.level_dim(cx.levels.length()), 0)
}
