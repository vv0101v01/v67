///|
test "api: transport along a morphism is the fibre bijection" {
  // the discrete family over Z/3 with the shift action
  let fam : Array[Array[Int32]] = []
  for p in 0..<3 {
    let row : Array[Int32] = []
    for x in 0..<3 {
      row.push((x + p) % 3)
    }
    fam.push(row)
  }
  assert_eq(transport_along(fam, 0, 2), 2)
  assert_eq(transport_along(fam, 1, 2), 0)
  // functoriality: transport along a composite is the composite
  for p in 0..<3 {
    for q in 0..<3 {
      for x in 0..<3 {
        assert_eq(
          transport_along(fam, (p + q) % 3, x),
          transport_along(fam, p, transport_along(fam, q, x)),
        )
      }
    }
  }
}
