///|
test "api: the weighted basis counts monomials by degree" {
  let ms = WeightedBasis::new([1, 2], 3)
  // degree_at is the grading, count_up_to is its cumulative sum
  let mut total = 0
  for i in 0..<ms.exps.length() {
    if ms.degree_at(i) <= 2 {
      total += 1
    }
  }
  assert_eq(ms.count_up_to(2), total)
  assert_eq(ms.count_up_to(3), ms.exps.length())
}
