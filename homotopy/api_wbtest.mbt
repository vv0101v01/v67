///|
test "api: a simplex fills its inner horns, a bare circle does not" {
  assert_true(fills_inner_horns_2(simplex3()))
  assert_true(!fills_inner_horns_2(circle()))
}

///|
test "api: the cyclic monoid of order 3 is unital and associative" {
  let mul : Array[Array[Int32]] = []
  for a in 0..<3 {
    let row : Array[Int32] = []
    for b in 0..<3 {
      row.push((a + b) % 3)
    }
    mul.push(row)
  }
  let m = Monoid::new(mul, 0)
  assert_true(m.is_unital())
  assert_true(m.is_associative())
  // a wrong unit is detected
  let bad = Monoid::new(mul, 1)
  assert_true(!bad.is_unital())
}
