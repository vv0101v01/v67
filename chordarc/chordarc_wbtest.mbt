///|
test "integer square root and gcd are exact" {
  for n in [0, 1, 2, 3, 4, 8, 9, 15, 16, 99, 100, 1024, 1048576] {
    let r = isqrt(n)
    assert_true(r * r <= n)
    assert_true((r + 1) * (r + 1) > n)
  }
  assert_eq(isqrt(1048576), 1024)
  assert_eq(isqrt(2 * 1024 * 1024), 1448)
  assert_eq(gcd(2896, 2048), 16)
  assert_eq(gcd(7, 1), 1)
  assert_eq(gcd(0, 5), 5)
}

///|
test "the regular tetrahedron is 1-chord-arc: intrinsic equals ambient" {
  let p = tetrahedron(1024)
  assert_eq(p.nverts(), 4)
  assert_eq(p.ntris(), 4)
  assert_true(p.non_degenerate())
  assert_true(p.is_closed())
  assert_eq(p.euler(), 2)
  // every pair of vertices is an edge, so the metrics coincide
  match p.chord_arc_constant() {
    Some((num, den)) => {
      assert_eq(num, 1)
      assert_eq(den, 1)
    }
    None => fail("constant")
  }
  assert_true(p.is_chord_arc(1, 1))
  let (pairs, bad) = p.check_bi_lipschitz(1, 1)
  assert_eq(pairs, 6)
  assert_eq(bad, 0)
  // and it is a sphere
  assert_eq(p.to_complex().betti(), [1, 0, 1])
}

///|
test "the regular octahedron has chord-arc constant sqrt(2)" {
  let p = octahedron(1024)
  assert_eq(p.nverts(), 6)
  assert_eq(p.ntris(), 8)
  assert_true(p.non_degenerate())
  assert_true(p.is_closed())
  assert_eq(p.euler(), 2)
  assert_eq(p.to_complex().betti(), [1, 0, 1])
  // opposite vertices: ambient 2048, intrinsic 2*1448 = 2896
  assert_eq(p.ambient(0, 1), 2048)
  let d = p.geodesics()
  assert_eq(d[0][1], 2896)
  // the optimal constant is 2896/2048 = 181/128, a rational approximation
  // of sqrt(2) from below (integer lengths round down)
  match p.chord_arc_constant() {
    Some((num, den)) => {
      assert_eq(num, 181)
      assert_eq(den, 128)
    }
    None => fail("constant")
  }
  assert_true(p.is_chord_arc(181, 128))
  // and it fails for any smaller constant
  assert_false(p.is_chord_arc(180, 128))
  assert_false(p.is_chord_arc(1, 1))
  let (pairs, bad) = p.check_bi_lipschitz(181, 128)
  assert_eq(pairs, 15)
  assert_eq(bad, 0)
}

///|
test "the hairpin ribbon is not uniformly chord-arc" {
  // the two tips are 2s apart in space but 2*arm+2 steps along the ribbon
  for arm in [2, 4, 6] {
    let p = hairpin(arm, 64)
    assert_true(p.non_degenerate())
    // a ribbon has boundary, so it is not a closed surface
    assert_false(p.is_closed())
    let m = arm + 1 + 1 + arm + 1
    assert_eq(p.nverts(), 2 * m)
    let d = p.geodesics()
    // tips: vertex 0 and vertex m-1
    let steps = 2 * arm + 2
    assert_eq(d[0][m - 1], steps * 64)
    assert_eq(p.ambient(0, m - 1), 128)
    // the tip-to-tip ratio alone is arm+1, and the true constant is at
    // most one more (a tip against the far layer of the ribbon)
    match p.chord_arc_constant() {
      Some((num, den)) => {
        assert_true(num >= (arm + 1) * den)
        assert_true(num <= (arm + 2) * den)
      }
      None => fail("constant")
    }
    assert_true(p.is_chord_arc(arm + 2, 1))
    assert_false(p.is_chord_arc(arm, 1))
  }
  // in particular no fixed constant works for the whole family
  let small = hairpin(2, 64)
  let large = hairpin(6, 64)
  assert_true(small.is_chord_arc(4, 1))
  assert_false(large.is_chord_arc(4, 1))
}

///|
test "barycentric subdivision is exact and preserves the chord-arc constant" {
  for base in [tetrahedron(1024), octahedron(1024)] {
    let sub = base.subdivide()
    assert_true(sub.non_degenerate())
    assert_true(sub.is_closed())
    // V - E + F is unchanged: subdivision does not change the topology
    assert_eq(sub.euler(), base.euler())
    assert_eq(sub.to_complex().betti(), base.to_complex().betti())
    // each original triangle became six
    assert_eq(sub.ntris(), 6 * base.ntris())
    // Each original edge uv becomes u-m-v of length exactly 6|uv|, so the
    // edge-path metric can only decrease: d_sub <= 6 * d_orig.  It never
    // increases, because every original path lifts to a path of exactly
    // six times the length.
    let d0 = base.geodesics()
    let d1 = sub.geodesics()
    for u in 0..<base.nverts() {
      for v in 0..<base.nverts() {
        assert_true(d1[u][v] <= 6 * d0[u][v])
      }
    }
    // hence the chord-arc constant *on the original vertices* is
    // unchanged.  Over all pairs it can grow: the new centroids and
    // midpoints introduce pairs that the original triangulation did not
    // have, and for the tetrahedron the constant rises from 1 to sqrt(3).
    let originals : Array[Int32] = []
    for i in 0..<base.nverts() {
      originals.push(i)
    }
    match (base.chord_arc_constant(), sub.chord_arc_constant_on(originals)) {
      (Some((a, b)), Some((c, d))) => assert_true(c * b <= a * d)
      _ => fail("constants")
    }
  }
  // For the tetrahedron the original edge paths are already geodesic, so
  // subdivision changes nothing: equality holds on every pair.
  let tet = tetrahedron(1024)
  let ts = tet.subdivide()
  let t0 = tet.geodesics()
  let t1 = ts.geodesics()
  for u in 0..<4 {
    for v in 0..<4 {
      assert_eq(t1[u][v], 6 * t0[u][v])
    }
  }
  // For the octahedron it strictly improves the opposite-vertex distance,
  // from 2*sqrt(2)*s to sqrt(6)*s -- the true surface geodesic, which
  // crosses the shared edge of two faces at its midpoint.
  let oct = octahedron(1024)
  let os = oct.subdivide()
  assert_eq(oct.geodesics()[0][1], 2896)
  assert_eq(os.geodesics()[0][1], 6 * 2508)
  assert_true(os.geodesics()[0][1] < 6 * oct.geodesics()[0][1])
  // sqrt(6)*1024 = 2508.4..., so 2508 is the correct integer length
  assert_eq(isqrt(6 * 1024 * 1024), 2508)
}

///|
test "chord-arc gives a quantitative bound on filling paths" {
  // hops * min_edge <= C * ambient: a short ambient pair is joined by few
  // edges, which is the metric form of local fillability
  let oct = octahedron(1024)
  let (pairs, bad) = oct.check_short_paths(181, 128)
  assert_eq(pairs, 15)
  assert_eq(bad, 0)
  assert_eq(oct.hop_diameter(), 2)
  assert_eq(oct.min_edge(), 1448)
  let tet = tetrahedron(1024)
  let (p2, b2) = tet.check_short_paths(1, 1)
  assert_eq(p2, 6)
  assert_eq(b2, 0)
  assert_eq(tet.hop_diameter(), 1)
  // the hairpin needs many hops between nearby points: the bound is
  // violated for any constant below its chord-arc constant
  let hair = hairpin(6, 64)
  let (_, bad_hair) = hair.check_short_paths(3, 1)
  assert_true(bad_hair > 0)
  let (ph, bh) = hair.check_short_paths(8, 1)
  assert_true(ph > 0)
  assert_eq(bh, 0)
}

///|
test "degenerate and non-manifold triangulations are detected" {
  // a triangle with a repeated vertex
  let bad = Polyhedron::new([[0, 0, 0], [1, 0, 0], [0, 1, 0]], [(0, 0, 1)])
  assert_false(bad.non_degenerate())
  // three collinear points: zero cross product
  let flat = Polyhedron::new([[0, 0, 0], [1, 0, 0], [2, 0, 0]], [(0, 1, 2)])
  assert_false(flat.non_degenerate())
  // a single triangle is non-degenerate but has boundary
  let tri = Polyhedron::new([[0, 0, 0], [1, 0, 0], [0, 1, 0]], [(0, 1, 2)])
  assert_true(tri.non_degenerate())
  assert_false(tri.is_closed())
  assert_eq(tri.euler(), 1)
  // gluing two triangles along an edge gives a disc, still with boundary
  let disc = Polyhedron::new([[0, 0, 0], [1, 0, 0], [0, 1, 0], [1, 1, 0]], [
    (0, 1, 2),
    (1, 3, 2),
  ])
  assert_true(disc.non_degenerate())
  assert_false(disc.is_closed())
  assert_eq(disc.euler(), 1)
  // three triangles around one edge: not a manifold
  let fan = Polyhedron::new(
    [[0, 0, 0], [1, 0, 0], [0, 1, 0], [0, 0, 1], [0, -1, 0]],
    [(0, 1, 2), (0, 1, 3), (0, 1, 4)],
  )
  assert_true(fan.non_degenerate())
  assert_false(fan.is_closed())
}

///|
test "the ambient metric never exceeds the intrinsic one" {
  // the lower half of the bi-Lipschitz condition, checked on every example
  for p in [tetrahedron(256), octahedron(256), hairpin(4, 32)] {
    let d = p.geodesics()
    for u in 0..<p.nverts() {
      for v in 0..<p.nverts() {
        assert_true(d[u][v] >= p.ambient(u, v))
      }
    }
    // symmetry and the triangle inequality of the computed metric
    for u in 0..<p.nverts() {
      assert_eq(d[u][u], 0)
      for v in 0..<p.nverts() {
        assert_eq(d[u][v], d[v][u])
        for w in 0..<p.nverts() {
          assert_true(d[u][w] <= d[u][v] + d[v][w])
        }
      }
    }
  }
}
