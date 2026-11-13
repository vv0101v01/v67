///|
test "api: the corners of a little cube are its bounding box" {
  let c = LittleCube::new([1, 2], [2, 3], 8)
  assert_eq(c.corner([0, 0]), [1, 2])
  assert_eq(c.corner([1, 1]), [3, 5])
  assert_eq(c.corner([1, 0]), [3, 2])
}
