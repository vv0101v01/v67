///|
/// Integer square root by Newton's method, exact: `isqrt(n)² ≤ n <
/// (isqrt(n)+1)²`.  All lengths in this package are integers, so every
/// comparison below is exact — no floating point anywhere.
pub fn isqrt(n : Int32) -> Int32 {
  if n <= 0 {
    return 0
  }
  let mut x = n
  let mut y = (x + 1) / 2
  while y < x {
    x = y
    y = (x + n / x) / 2
  }
  x
}

///|
pub fn gcd(a : Int32, b : Int32) -> Int32 {
  let mut x = if a < 0 { -a } else { a }
  let mut y = if b < 0 { -b } else { b }
  while y != 0 {
    let t = x % y
    x = y
    y = t
  }
  x
}

///|
/// A **triangulated polyhedron**: vertices with integer coordinates in
/// `Z³` and a list of triangles.  Integer coordinates make every ambient
/// distance an exact integer square root, and scaling the coordinates is
/// the standard way to buy precision (the examples use a scale of 1024).
#derive(Debug, Eq)
pub struct Polyhedron {
  coords : Array[Array[Int32]]
  tris : Array[(Int32, Int32, Int32)]
}

///|
pub fn Polyhedron::new(
  coords : Array[Array[Int32]],
  tris : Array[(Int32, Int32, Int32)],
) -> Polyhedron {
  Polyhedron::{ coords, tris, }
}

///|
pub fn Polyhedron::nverts(self : Polyhedron) -> Int32 {
  self.coords.length()
}

///|
pub fn Polyhedron::ntris(self : Polyhedron) -> Int32 {
  self.tris.length()
}

///|
/// Squared ambient distance — exact, and the quantity all comparisons are
/// ultimately reduced to.
pub fn Polyhedron::dist2(self : Polyhedron, u : Int32, v : Int32) -> Int32 {
  let a = self.coords[u]
  let b = self.coords[v]
  let mut s = 0
  for i in 0..<a.length() {
    let d = a[i] - b[i]
    s = s + d * d
  }
  s
}

///|
/// Ambient distance, rounded down to an integer.  Coordinates are assumed
/// pre-scaled, so the relative error is `O(1/scale)`.
pub fn Polyhedron::ambient(self : Polyhedron, u : Int32, v : Int32) -> Int32 {
  isqrt(self.dist2(u, v))
}

///|
/// The edge set of the 1-skeleton, as sorted pairs.
pub fn Polyhedron::edges(self : Polyhedron) -> Array[(Int32, Int32)] {
  let n = self.nverts()
  let seen : Map[Int32, Bool] = Map([])
  let out : Array[(Int32, Int32)] = []
  for (a, b, c) in self.tris {
    for (u, v) in [(a, b), (b, c), (a, c)] {
      let lo = if u < v { u } else { v }
      let hi = if u < v { v } else { u }
      let key = lo * n + hi
      if seen.get(key) is None {
        seen[key] = true
        out.push((lo, hi))
      }
    }
  }
  out
}

///|
/// Twice the signed area vector of a triangle (the cross product).  A
/// triangle is degenerate exactly when this vanishes.
pub fn Polyhedron::cross(
  self : Polyhedron,
  t : (Int32, Int32, Int32),
) -> Array[Int32] {
  let (i, j, k) = t
  let a = self.coords[i]
  let b = self.coords[j]
  let c = self.coords[k]
  let u = [b[0] - a[0], b[1] - a[1], b[2] - a[2]]
  let v = [c[0] - a[0], c[1] - a[1], c[2] - a[2]]
  [
    u[1] * v[2] - u[2] * v[1],
    u[2] * v[0] - u[0] * v[2],
    u[0] * v[1] - u[1] * v[0],
  ]
}

///|
/// No degenerate triangles and no repeated vertices in a triangle.
pub fn Polyhedron::non_degenerate(self : Polyhedron) -> Bool {
  for (a, b, c) in self.tris {
    if a == b || b == c || a == c {
      return false
    }
    if a < 0 ||
      b < 0 ||
      c < 0 ||
      a >= self.nverts() ||
      b >= self.nverts() ||
      c >= self.nverts() {
      return false
    }
    let n = self.cross((a, b, c))
    if n[0] == 0 && n[1] == 0 && n[2] == 0 {
      return false
    }
  }
  true
}

///|
/// Is the surface closed: every edge lies in exactly two triangles?
/// A ribbon or a disc fails this, which is expected — the chord-arc
/// condition makes sense for surfaces with boundary too.
pub fn Polyhedron::is_closed(self : Polyhedron) -> Bool {
  let n = self.nverts()
  let count : Map[Int32, Int32] = Map([])
  for (a, b, c) in self.tris {
    for (u, v) in [(a, b), (b, c), (a, c)] {
      let lo = if u < v { u } else { v }
      let hi = if u < v { v } else { u }
      let key = lo * n + hi
      count[key] = count.get(key).unwrap_or(0) + 1
    }
  }
  for k in count {
    if k.1 != 2 {
      return false
    }
  }
  true
}

///|
/// The intrinsic (edge-path) metric of the 1-skeleton, by Floyd–Warshall
/// with exact integer edge lengths.  This is the finite surrogate for the
/// geodesic metric of the surface: a path in the surface can be pushed to
/// the 1-skeleton with bounded distortion, and on a triangulation the
/// edge-path metric is the natural computable one.
/// Cost `O(V³)`.
pub fn Polyhedron::geodesics(self : Polyhedron) -> Array[Array[Int32]] {
  let n = self.nverts()
  let big = 1000000000
  let d : Array[Array[Int32]] = []
  for i in 0..<n {
    let row = Array::make(n, big)
    row[i] = 0
    d.push(row)
  }
  for (u, v) in self.edges() {
    let w = self.ambient(u, v)
    if w < d[u][v] {
      d[u][v] = w
      d[v][u] = w
    }
  }
  for k in 0..<n {
    for i in 0..<n {
      if d[i][k] < big {
        for j in 0..<n {
          let cand = d[i][k] + d[k][j]
          if cand < d[i][j] {
            d[i][j] = cand
          }
        }
      }
    }
  }
  d
}

///|
/// The **chord-arc condition**: the surface is `C`-chord-arc when
///
/// ```text
///   d_intrinsic(u, v)  ≤  C · d_ambient(u, v)     for all vertices u, v.
/// ```
///
/// With integer metrics this is an exact integer comparison, so the
/// property is decidable.  The lower bound `d_ambient ≤ d_intrinsic` is
/// automatic for a straight-line-shortest ambient metric and is checked
/// separately by `check_bi_lipschitz`.
pub fn Polyhedron::is_chord_arc(
  self : Polyhedron,
  c_num : Int32,
  c_den : Int32,
) -> Bool {
  if c_den <= 0 || c_num <= 0 {
    return false
  }
  let d = self.geodesics()
  let n = self.nverts()
  for u in 0..<n {
    for v in (u + 1)..<n {
      let amb = self.ambient(u, v)
      if amb == 0 {
        // coincident vertices: the intrinsic distance must also vanish
        if d[u][v] != 0 {
          return false
        }
      } else if d[u][v] * c_den > amb * c_num {
        return false
      }
    }
  }
  true
}

///|
/// The **optimal chord-arc constant** as an exact reduced fraction
/// `max_{u≠v} d_intrinsic(u,v) / d_ambient(u,v)`.  Returns `None` if two
/// distinct vertices coincide (the constant is then infinite).
pub fn Polyhedron::chord_arc_constant(self : Polyhedron) -> (Int32, Int32)? {
  let all : Array[Int32] = []
  for i in 0..<self.nverts() {
    all.push(i)
  }
  self.chord_arc_constant_on(all)
}

///|
/// The chord-arc constant measured only on a subset of the vertices.
/// This is what is preserved by subdivision: refining a triangulation
/// adds new vertex pairs (a centroid and a midpoint can be closer in
/// space than the originals ever were), so the constant over *all* pairs
/// may grow even though the geometry has not changed at all.
pub fn Polyhedron::chord_arc_constant_on(
  self : Polyhedron,
  verts : Array[Int32],
) -> (Int32, Int32)? {
  let d = self.geodesics()
  let mut best_num = 1
  let mut best_den = 1
  for i in 0..<verts.length() {
    for j in (i + 1)..<verts.length() {
      let u = verts[i]
      let v = verts[j]
      let amb = self.ambient(u, v)
      if amb == 0 {
        if d[u][v] != 0 {
          return None
        }
        continue
      }
      let num = d[u][v]
      // compare num/amb > best_num/best_den by cross multiplication
      if num * best_den > best_num * amb {
        best_num = num
        best_den = amb
      }
    }
  }
  let g = gcd(best_num, best_den)
  Some((best_num / g, best_den / g))
}

///|
/// The two-sided (bi-Lipschitz) comparison
/// `d_ambient ≤ d_intrinsic ≤ C · d_ambient`, checked pair by pair.
/// Returns the number of pairs and the number of violations.
pub fn Polyhedron::check_bi_lipschitz(
  self : Polyhedron,
  c_num : Int32,
  c_den : Int32,
) -> (Int32, Int32) {
  let d = self.geodesics()
  let n = self.nverts()
  let mut pairs = 0
  let mut bad = 0
  for u in 0..<n {
    for v in (u + 1)..<n {
      pairs = pairs + 1
      let amb = self.ambient(u, v)
      if d[u][v] < amb {
        bad = bad + 1
      }
      if d[u][v] * c_den > amb * c_num {
        bad = bad + 1
      }
    }
  }
  (pairs, bad)
}

///|
/// The hop diameter: the largest number of edges on a shortest edge path.
/// A chord-arc bound controls it, since every edge has length at least
/// the minimum edge length.
pub fn Polyhedron::hop_diameter(self : Polyhedron) -> Int32 {
  let n = self.nverts()
  let big = 1000000
  let d : Array[Array[Int32]] = []
  for i in 0..<n {
    let row = Array::make(n, big)
    row[i] = 0
    d.push(row)
  }
  for (u, v) in self.edges() {
    d[u][v] = 1
    d[v][u] = 1
  }
  for k in 0..<n {
    for i in 0..<n {
      for j in 0..<n {
        if d[i][k] + d[k][j] < d[i][j] {
          d[i][j] = d[i][k] + d[k][j]
        }
      }
    }
  }
  let mut m = 0
  for i in 0..<n {
    for j in 0..<n {
      if d[i][j] < big && d[i][j] > m {
        m = d[i][j]
      }
    }
  }
  m
}

///|
/// The shortest edge length, the scale that turns a length bound into a
/// hop bound.
pub fn Polyhedron::min_edge(self : Polyhedron) -> Int32 {
  let mut m = 1000000000
  for (u, v) in self.edges() {
    let w = self.ambient(u, v)
    if w < m {
      m = w
    }
  }
  m
}

///|
/// The underlying simplicial complex, for homology.  Vertices must be
/// fewer than 64, the bitmask limit of the complex representation.
pub fn Polyhedron::to_complex(self : Polyhedron) -> @homotopy.SimplicialComplex {
  let maximal : Array[UInt64] = []
  for (a, b, c) in self.tris {
    maximal.push(@homotopy.mask_of([a, b, c]))
  }
  @homotopy.SimplicialComplex::from_maximal(maximal)
}

///|
/// Euler characteristic `V - E + F`, a cheap sanity check before homology.
pub fn Polyhedron::euler(self : Polyhedron) -> Int32 {
  self.nverts() - self.edges().length() + self.ntris()
}
