///|
/// Floyd–Warshall tracking both the length and the number of edges of a
/// shortest path, so a length bound can be converted into a hop bound.
pub fn Polyhedron::geodesics_with_hops(
  self : Polyhedron,
) -> (Array[Array[Int32]], Array[Array[Int32]]) {
  let n = self.nverts()
  let big = 1000000000
  let d : Array[Array[Int32]] = []
  let h : Array[Array[Int32]] = []
  for i in 0..<n {
    let row = Array::make(n, big)
    let hrow = Array::make(n, big)
    row[i] = 0
    hrow[i] = 0
    d.push(row)
    h.push(hrow)
  }
  for (u, v) in self.edges() {
    let w = self.ambient(u, v)
    if w < d[u][v] {
      d[u][v] = w
      d[v][u] = w
      h[u][v] = 1
      h[v][u] = 1
    }
  }
  for k in 0..<n {
    for i in 0..<n {
      if d[i][k] < big {
        for j in 0..<n {
          let cand = d[i][k] + d[k][j]
          if cand < d[i][j] {
            d[i][j] = cand
            h[i][j] = h[i][k] + h[k][j]
          }
        }
      }
    }
  }
  (d, h)
}

///|
/// **Quantitative local fillability.**  A `C`-chord-arc bound turns an
/// ambient radius into a bound on the number of edges needed to join two
/// vertices: `hops(u,v) · min_edge ≤ C · ambient(u,v)`.  This is the
/// combinatorial shadow of "short paths exist locally", the metric
/// counterpart of the local complementability of path types.
/// Returns the number of pairs tested and the number of violations.
pub fn Polyhedron::check_short_paths(
  self : Polyhedron,
  c_num : Int32,
  c_den : Int32,
) -> (Int32, Int32) {
  let (_, hops) = self.geodesics_with_hops()
  let n = self.nverts()
  let shortest = self.min_edge()
  let mut pairs = 0
  let mut bad = 0
  for u in 0..<n {
    for v in (u + 1)..<n {
      pairs = pairs + 1
      let amb = self.ambient(u, v)
      if hops[u][v] * shortest * c_den > amb * c_num {
        bad = bad + 1
      }
    }
  }
  (pairs, bad)
}

///|
/// The regular tetrahedron, coordinates scaled by `s`.  Every pair of
/// vertices is an edge, so the intrinsic and ambient metrics agree and
/// the chord-arc constant is exactly `1`.
pub fn tetrahedron(s : Int32) -> Polyhedron {
  Polyhedron::new([[s, s, s], [s, -s, -s], [-s, s, -s], [-s, -s, s]], [
    (0, 1, 2),
    (0, 1, 3),
    (0, 2, 3),
    (1, 2, 3),
  ])
}

///|
/// The regular octahedron, coordinates scaled by `s`.  Opposite vertices
/// are at ambient distance `2s` but must travel two edges of length
/// `s√2`, so the chord-arc constant is `√2`.
pub fn octahedron(s : Int32) -> Polyhedron {
  Polyhedron::new(
    [[s, 0, 0], [-s, 0, 0], [0, s, 0], [0, -s, 0], [0, 0, s], [0, 0, -s]],
    [
      (0, 2, 4),
      (2, 1, 4),
      (1, 3, 4),
      (3, 0, 4),
      (2, 0, 5),
      (1, 2, 5),
      (3, 1, 5),
      (0, 3, 5),
    ],
  )
}

///|
/// A **hairpin ribbon**: a U-shaped strip, the standard example of a
/// surface that is *not* uniformly chord-arc.  The two tips are close in
/// space but far along the surface, so the chord-arc constant grows
/// linearly with the arm length.  This is the metric obstruction that
/// chord-arc conditions are designed to exclude.
pub fn hairpin(arm : Int32, s : Int32) -> Polyhedron {
  // the spine of the U, in the plane z = 0
  let spine : Array[Array[Int32]] = []
  for i in 0..<=arm {
    spine.push([i * s, 0, 0])
  }
  spine.push([arm * s, s, 0])
  for i in 0..<=arm {
    spine.push([(arm - i) * s, 2 * s, 0])
  }
  let m = spine.length()
  let coords : Array[Array[Int32]] = []
  for p in spine {
    coords.push([p[0], p[1], 0])
  }
  for p in spine {
    coords.push([p[0], p[1], s])
  }
  let tris : Array[(Int32, Int32, Int32)] = []
  for i in 0..<(m - 1) {
    let p0 = i
    let p1 = i + 1
    let q0 = m + i
    let q1 = m + i + 1
    tris.push((p0, p1, q0))
    tris.push((p1, q1, q0))
  }
  Polyhedron::new(coords, tris)
}

///|
/// **Barycentric subdivision.**  Each triangle is split into six by its
/// edge midpoints and centroid.  Coordinates are multiplied by 6 first so
/// that midpoints (`3(A+B)`) and centroids (`2(A+B+C)`) stay integral —
/// subdivision is exact, with no rounding at all.
///
/// Every original edge `uv` becomes `u–m–v` of length exactly `6|uv|`, so
/// the edge-path metric can only *decrease*: `d_sub ≤ 6·d_orig`.  It
/// generally does decrease, because the finer skeleton can cut across
/// faces and so approximates the true surface geodesic better.  Equality
/// holds exactly when the original edge paths were already geodesic (the
/// tetrahedron); for the octahedron the opposite-vertex distance drops
/// from `2√2·s` to `√6·s`, which is the genuine intrinsic distance.
pub fn Polyhedron::subdivide(self : Polyhedron) -> Polyhedron {
  let n = self.nverts()
  let coords : Array[Array[Int32]] = []
  for p in self.coords {
    let row : Array[Int32] = []
    for x in p {
      row.push(6 * x)
    }
    coords.push(row)
  }
  let mid : Map[Int32, Int32] = Map([])
  let tris : Array[(Int32, Int32, Int32)] = []
  fn midpoint(u : Int32, v : Int32) -> Int32 {
    let lo = if u < v { u } else { v }
    let hi = if u < v { v } else { u }
    let key = lo * 1000000 + hi
    match mid.get(key) {
      Some(i) => i
      None => {
        let a = coords[lo]
        let b = coords[hi]
        let row : Array[Int32] = []
        for i in 0..<a.length() {
          row.push((a[i] + b[i]) / 2)
        }
        coords.push(row)
        let idx = coords.length() - 1
        mid[key] = idx
        idx
      }
    }
  }

  for (a, b, c) in self.tris {
    let ab = midpoint(a, b)
    let bc = midpoint(b, c)
    let ca = midpoint(c, a)
    let pa = coords[a]
    let pb = coords[b]
    let pc = coords[c]
    let g : Array[Int32] = []
    for i in 0..<pa.length() {
      g.push((pa[i] + pb[i] + pc[i]) / 3)
    }
    coords.push(g)
    let gi = coords.length() - 1
    tris.push((a, ab, gi))
    tris.push((ab, b, gi))
    tris.push((b, bc, gi))
    tris.push((bc, c, gi))
    tris.push((c, ca, gi))
    tris.push((ca, a, gi))
  }
  let _ = n
  Polyhedron::new(coords, tris)
}
