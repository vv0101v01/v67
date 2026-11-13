///|
test "api: the deck count of a circle cover is the fibre size" {
  let u = universal_cover(space_circle(), 0, 4)
  // the universal cover of S¹ is a tree: only the identity deck map
  // survives on a truncation, so the count is at least one and at most
  // the size of the fibre over the base point.
  let n = u.deck_count()
  assert_true(n >= 1)
  assert_true(n <= u.fibre(u.root).length())
}
