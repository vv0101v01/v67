///|
/// A deterministic pseudo-random connection, so the tests exercise
/// genuinely non-flat data rather than only the trivial case.
fn lcg(s : Array[Int32]) -> Int32 {
  s[0] = (s[0] * 1103515245 + 12345) % 2147483647
  if s[0] < 0 {
    s[0] = s[0] + 2147483647
  }
  s[0]
}

///|
fn random_connection(grid : Grid, g : FinGroup, seed : Int32) -> Connection {
  let s = [seed]
  let edges : Array[Int32] = []
  for _ in 0..<(grid.nverts() * grid.ndirs()) {
    edges.push(lcg(s) % g.n)
  }
  Connection::from_edges(grid, g, edges)
}

///|
test "structure groups: Z/5 is abelian, S_3 is not, both satisfy the axioms" {
  let z5 = cyclic(5)
  assert_true(z5.check())
  assert_true(z5.is_abelian())
  let s3 = symmetric3()
  assert_true(s3.check())
  assert_false(s3.is_abelian())
  assert_eq(s3.n, 6)
  // inverses really invert
  for a in 0..<s3.n {
    assert_eq(s3.op(a, s3.inverse(a)), s3.e)
  }
}

///|
test "flat connection: trivial holonomy, and the horizontal foliation is trivial" {
  let grid = Grid::new([3, 3])
  let g = symmetric3()
  let conn = Connection::trivial(grid, g)
  assert_true(conn.is_flat())
  assert_eq(conn.curvature_count(), 0)
  let b = Bundle::new(conn)
  assert_true(b.check_equivariance())
  // Frobenius: |G| leaves, each a graph over the base
  assert_true(b.is_integrable_trivially())
  assert_eq(b.leaves().length(), 6)
  assert_eq(b.leaf_size(0), 9)
  assert_eq(b.holonomy_group(0), [g.e])
}

///|
test "a pure-gauge connection is flat but has nontrivial transport" {
  let grid = Grid::new([3, 3])
  let g = symmetric3()
  let s = [7]
  let gauge : Array[Int32] = []
  for _ in 0..<grid.nverts() {
    gauge.push(lcg(s) % g.n)
  }
  let conn = Connection::trivial(grid, g).gauge_transform(gauge)
  // nontrivial edge data ...
  let mut nontrivial = 0
  for t in conn.transport {
    if t != g.e {
      nontrivial = nontrivial + 1
    }
  }
  assert_true(nontrivial > 0)
  // ... but zero curvature: pure gauge is flat
  assert_true(conn.is_flat())
  let b = Bundle::new(conn)
  assert_true(b.is_integrable_trivially())
  assert_eq(b.holonomy_group(0), [g.e])
}

///|
test "curvature obstructs integrability: non-flat means fewer, larger leaves" {
  let grid = Grid::new([3, 3])
  let g = symmetric3()
  let conn = random_connection(grid, g, 42)
  assert_false(conn.is_flat())
  assert_true(conn.curvature_count() > 0)
  let b = Bundle::new(conn)
  assert_true(b.check_equivariance())
  // Frobenius fails: the holonomy group is nontrivial ...
  let hol = b.holonomy_group(0)
  assert_true(hol.length() > 1)
  // ... so the leaf is |base| * |holonomy| and there are |G|/|hol| leaves
  assert_eq(b.leaf_size(0), grid.nverts() * hol.length())
  assert_eq(b.leaves().length(), g.n / hol.length())
  assert_false(b.is_integrable_trivially())
  // and flat <=> integrable, on this and every random sample
  for seed in [1, 2, 3, 5, 8, 13] {
    let c = random_connection(grid, g, seed)
    let bb = Bundle::new(c)
    assert_eq(c.is_flat(), bb.is_integrable_trivially())
  }
}

///|
test "curvature is gauge covariant, so flatness is gauge invariant" {
  let grid = Grid::new([3, 3])
  let g = symmetric3()
  let s = [99]
  let gauge : Array[Int32] = []
  for _ in 0..<grid.nverts() {
    gauge.push(lcg(s) % g.n)
  }
  for seed in [42, 7, 1234] {
    let conn = random_connection(grid, g, seed)
    assert_true(conn.check_gauge_covariance(gauge))
    let other = conn.gauge_transform(gauge)
    assert_eq(conn.is_flat(), other.is_flat())
    // the number of curved plaquettes is a gauge invariant
    assert_eq(conn.curvature_count(), other.curvature_count())
    // holonomy groups are conjugate, hence the same order
    let b1 = Bundle::new(conn)
    let b2 = Bundle::new(other)
    assert_eq(b1.holonomy_group(0).length(), b2.holonomy_group(0).length())
  }
  // gauge transformations compose and invert
  let conn = random_connection(grid, g, 42)
  let inv : Array[Int32] = []
  for x in gauge {
    inv.push(g.inverse(x))
  }
  assert_eq(conn.gauge_transform(gauge).gauge_transform(inv), conn)
}

///|
test "Bianchi identity d_A F = 0 holds on every 3-cube, flat or not" {
  let grid = Grid::new([3, 3, 3])
  for g in [cyclic(5), symmetric3()] {
    // trivial and pure gauge
    assert_true(Connection::trivial(grid, g).check_bianchi_all())
    for seed in [1, 42, 777, 31337] {
      let conn = random_connection(grid, g, seed)
      // genuinely curved data
      assert_true(conn.curvature_count() > 0)
      assert_true(conn.check_bianchi_all())
    }
  }
}

///|
test "abelian holonomy is the total flux; non-abelian holonomy sees order" {
  let grid = Grid::new([3, 3])
  let z5 = cyclic(5)
  let conn = random_connection(grid, z5, 5)
  // for an abelian group the plaquette holonomy is the signed sum of edges
  for (v, i, j, h) in conn.curvatures() {
    let vi = grid.step(v, i, true)
    let vj = grid.step(v, j, true)
    let expected = (
        conn.transport[grid.edge_slot(v, i)] +
        conn.transport[grid.edge_slot(vi, j)] -
        conn.transport[grid.edge_slot(vj, i)] -
        conn.transport[grid.edge_slot(v, j)]
      ) %
      5
    let norm = if expected < 0 { expected + 5 } else { expected }
    assert_eq(h, norm)
  }
  // in S_3 the two orders of the same two generators generally differ
  let s3 = symmetric3()
  let a = 1
  let b = 3
  assert_true(s3.op(a, b) != s3.op(b, a) || s3.is_abelian())
}

///|
test "higher dimensions: 4-cube grid, curvature and Bianchi in all planes" {
  let grid = Grid::new([2, 2, 2, 2])
  let g = symmetric3()
  let conn = random_connection(grid, g, 2024)
  assert_eq(grid.nverts(), 16)
  // 4 directions give 6 coordinate planes per vertex
  let curv = conn.curvatures()
  assert_true(curv.length() > 0)
  assert_true(conn.check_bianchi_all())
  let b = Bundle::new(conn)
  assert_true(b.check_equivariance())
  let hol = b.holonomy_group(0)
  assert_eq(b.leaf_size(0), 16 * hol.length())
}
