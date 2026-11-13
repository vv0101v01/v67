///|
test "api: to_dim is a retraction of of_dim on generators" {
  for i in 0..<3 {
    let d = @cubical.DVar(i)
    let back = DMA::of_dim(d).to_dim()
    assert_eq(@cubical.dim_eq(back, d), true)
  }
}

///|
test "api: cube_map builds the map it is given" {
  let cs : Array[@cubical.Dim] = [@cubical.DVar(1), @cubical.DZero]
  let m = cube_map(2, 2, cs)
  let id = cube_id(2)
  assert_eq(m.src, id.src)
  assert_eq(m.dst, id.dst)
}
