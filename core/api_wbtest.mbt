///|
test "api: ipow is the shared exponentiation" {
  assert_eq(ipow(3, 0), 1)
  assert_eq(ipow(3, 4), 81)
  assert_eq(ipow(2, 10), 1024)
  assert_eq(ipow2(10), ipow(2, 10))
  assert_eq(ipow(5, -1), 1)
}

///|
test "api: a column is a row of the transpose" {
  let m = BoolMat::identity(4)
  for j in 0..<4 {
    let c = m.column(j)
    let t = m.transpose()
    for i in 0..<4 {
      assert_eq(c.get(i), t.get(j, i))
    }
  }
}

///|
test "api: total_dim and profile agree with the Betti numbers" {
  // the sphere S²: dims [1,0,1], one boundary map of rank 0
  let d0 : Array[Bits] = [Bits::new(0)]
  let d1 : Array[Bits] = [Bits::new(1)]
  let cx = ChainComplex::new([1, 0, 1], [d0, d1])
  assert_eq(cx.total_dim(), 2)
  let p = cx.profile()
  assert_true(p.contains("dims="))
  assert_true(p.contains("ranks="))
  assert_true(p.contains("betti="))
}

///|
test "api: the persistence diagram renders every pair" {
  let cells : Array[FilteredCell] = [
    FilteredCell::{ dim: 0, birth: 0, boundary: [], },
    FilteredCell::{ dim: 0, birth: 0, boundary: [], },
    FilteredCell::{ dim: 1, birth: 1, boundary: [0, 1], },
  ]
  let f = Filtration::new(cells)
  let s = f.diagram()
  // one line per persistence pair, and the essential class reads "inf"
  let mut lines = 0
  for line in s.split("\n") {
    if line.length() > 0 {
      lines += 1
    }
  }
  assert_eq(lines, f.persistence().length())
  assert_true(s.contains("dim 0: "))
  assert_true(s.contains("inf"))
}
