///|
/// A finite graph as a base space.  Vertices are points, edges are paths,
/// and the fundamental group is free of rank `E - V + 1` on each component.
#derive(Debug, Eq)
pub struct Space {
  nverts : Int32
  edges : Array[(Int32, Int32)]
}

///|
pub fn Space::new(nverts : Int32, edges : Array[(Int32, Int32)]) -> Space {
  Space::{ nverts, edges, }
}

///|
pub fn Space::nedges(self : Space) -> Int32 {
  self.edges.length()
}

///|
/// The circle: one vertex, one loop.
pub fn space_circle() -> Space {
  Space::new(1, [(0, 0)])
}

///|
/// The figure eight.
pub fn space_wedge(n : Int32) -> Space {
  let es : Array[(Int32, Int32)] = []
  for _ in 0..<n {
    es.push((0, 0))
  }
  Space::new(1, es)
}

///|
/// A cycle of length `n`, the standard base whose universal cover is a line
/// and whose `k`-fold covers are cycles of length `k*n`.
pub fn space_cycle(n : Int32) -> Space {
  let es : Array[(Int32, Int32)] = []
  for i in 0..<n {
    es.push((i, (i + 1) % n))
  }
  Space::new(n, es)
}

///|
/// A signed letter: `e >= 0` traverses edge `e` forwards, `e < 0` backwards.
pub fn letter_ends(sp : Space, l : Int32) -> (Int32, Int32) {
  if l >= 0 {
    sp.edges[l]
  } else {
    let (a, b) = sp.edges[-l - 1]
    (b, a)
  }
}

///|
/// Reduce a word by cancelling adjacent inverse pairs: the normal form in
/// the free groupoid.  Terminating and confluent, so it is a decision
/// procedure for path homotopy.
pub fn reduce(w : Array[Int32]) -> Array[Int32] {
  let st : Array[Int32] = []
  for x in w {
    if st.length() > 0 && st[st.length() - 1] == -x - 1 {
      ignore(st.pop())
    } else {
      st.push(x)
    }
  }
  st
}

///|
/// A point of the universal cover: a homotopy class of paths from the base
/// point, represented by its reduced word.  This is the *path-fibration*
/// construction `Σ (x : X), Id(x0, x)`, made finite by bounding length.
#derive(Debug, Eq)
pub struct CoverPoint {
  word : Array[Int32]
  endpoint : Int32
}

///|
/// The universal cover of a graph, truncated at path length `radius`.
/// It is a tree (simply connected) and the projection to the base is a
/// local bijection on edges — the two defining properties of a universal
/// covering space, both checked below.
#derive(Debug, Eq)
pub struct UniversalCover {
  base : Space
  root : Int32
  radius : Int32
  points : Array[CoverPoint]
  /// `lift[p][letter]` = index of the lifted endpoint, or -1
  lift : Array[Array[Int32]]
}

///|
/// Build the universal cover by breadth-first exploration of reduced words.
/// Cost `O((2E)^radius)` in the worst case, which is why the radius is
/// explicit: the universal cover of a graph with a loop is infinite, and
/// any finite computation must truncate.
pub fn universal_cover(
  base : Space,
  root : Int32,
  radius : Int32,
) -> UniversalCover {
  let width = 2 * base.nedges()
  let points : Array[CoverPoint] = [CoverPoint::{ word: [], endpoint: root, }]
  let lift : Array[Array[Int32]] = [Array::make(width, -1)]
  // parent[p] is the point reached by cancelling the last letter; the
  // backwards edge out of p must lift to it, not to a fresh point.
  let parent : Array[Int32] = [-1]
  let mut head = 0
  while head < points.length() {
    let p = head
    head = head + 1
    if points[p].word.length() >= radius {
      continue
    }
    let here = points[p].endpoint
    for e in 0..<base.nedges() {
      for s in 0..<2 {
        let l = if s == 0 { e } else { -e - 1 }
        let (a, b) = letter_ends(base, l)
        if a != here {
          continue
        }
        // Reduced words only: never append the inverse of the last letter.
        // Then each reduced word is generated exactly once, so no duplicate
        // search is needed -- this is exactly the tree property of the cover.
        let prev = points[p].word
        if prev.length() > 0 && prev[prev.length() - 1] == -l - 1 {
          // backtracking: this edge returns to the parent point
          lift[p][2 * e + s] = parent[p]
          continue
        }
        let w = prev[:].to_owned()
        w.push(l)
        points.push(CoverPoint::{ word: w, endpoint: b, })
        lift.push(Array::make(width, -1))
        parent.push(p)
        lift[p][2 * e + s] = points.length() - 1
      }
    }
  }
  UniversalCover::{ base, root, radius, points, lift, }
}

///|
pub fn UniversalCover::size(self : UniversalCover) -> Int32 {
  self.points.length()
}

///|
/// The covering projection: a point of the cover maps to its endpoint.
pub fn UniversalCover::project(self : UniversalCover, p : Int32) -> Int32 {
  self.points[p].endpoint
}

///|
/// The fibre over a base vertex: all path classes ending there.
pub fn UniversalCover::fibre(self : UniversalCover, v : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for p in 0..<self.size() {
    if self.project(p) == v {
      out.push(p)
    }
  }
  out
}

///|
/// Local triviality: at every point of the cover, the lifted edges are in
/// bijection with the base edges at its projection.  This is the defining
/// property of a covering map, and it is what makes path lifting work.
/// Points at the truncation boundary are exempt (their neighbours were
/// not generated), so the check is restricted to the interior.
pub fn UniversalCover::is_local_bijection(self : UniversalCover) -> Bool {
  for p in 0..<self.size() {
    if self.points[p].word.length() >= self.radius {
      continue
    }
    let v = self.project(p)
    // count base edge-ends at v
    let mut base_deg = 0
    for e in 0..<self.base.nedges() {
      let (a, b) = self.base.edges[e]
      if a == v {
        base_deg = base_deg + 1
      }
      if b == v {
        base_deg = base_deg + 1
      }
    }
    let mut lift_deg = 0
    for x in self.lift[p] {
      if x >= 0 {
        lift_deg = lift_deg + 1
      }
    }
    if lift_deg != base_deg {
      return false
    }
    // and the lifted edges land over the right endpoints
    for e in 0..<self.base.nedges() {
      for s in 0..<2 {
        let l = if s == 0 { e } else { -e - 1 }
        let (a, b) = letter_ends(self.base, l)
        let q = self.lift[p][2 * e + s]
        if a == v {
          if q < 0 || self.project(q) != b {
            return false
          }
        } else if q >= 0 {
          return false
        }
      }
    }
  }
  true
}

///|
/// Simple connectivity of the (truncated) cover: it is a tree, so it has
/// no reduced cycles.  Checked by `#points - #edges = 1` on the interior,
/// the Euler characteristic of a tree.
pub fn UniversalCover::is_tree(self : UniversalCover) -> Bool {
  // count undirected lifted edges among interior points
  let mut edge_count = 0
  for p in 0..<self.size() {
    for e in 0..<self.base.nedges() {
      for s in 0..<2 {
        let q = self.lift[p][2 * e + s]
        if q >= 0 && p < q {
          edge_count = edge_count + 1
        }
      }
    }
  }
  // a tree on all generated points
  self.size() - edge_count == 1
}

///|
/// Unique path lifting: given a base word and a starting point in the
/// fibre, there is exactly one lifted walk.  Returns its endpoint.
pub fn UniversalCover::lift_path(
  self : UniversalCover,
  start : Int32,
  word : Array[Int32],
) -> Int32? {
  let mut cur = start
  for l in word {
    if l < -self.base.nedges() || l >= self.base.nedges() {
      return None
    }
    let slot = if l >= 0 { 2 * l } else { 2 * (-l - 1) + 1 }
    let next = self.lift[cur][slot]
    if next < 0 {
      return None
    }
    cur = next
  }
  Some(cur)
}

///|
/// The deck transformation group: automorphisms of the cover over the
/// base.  For a universal cover it is isomorphic to `pi1` of the base, and
/// here it is realised concretely as left multiplication of path classes.
/// A deck transformation is determined by where it sends the root, and it
/// exists exactly when that target is in the fibre over the root.
pub fn UniversalCover::deck_translation(
  self : UniversalCover,
  target : Int32,
) -> Array[Int32]? {
  if self.project(target) != self.root {
    return None
  }
  let prefix = self.points[target].word
  let out : Array[Int32] = []
  for p in 0..<self.size() {
    // concatenate prefix with the point's word, then reduce
    let w : Array[Int32] = []
    for x in prefix {
      w.push(x)
    }
    for x in self.points[p].word {
      w.push(x)
    }
    let r = reduce(w)
    let mut found = -1
    for q in 0..<self.size() {
      if self.points[q].word == r {
        found = q
      }
    }
    out.push(found)
  }
  Some(out)
}

///|
/// Is a deck translation a bijection on the (truncated) cover?  Interior
/// points must map to points, and the map must be injective there.
pub fn UniversalCover::check_deck(
  self : UniversalCover,
  target : Int32,
) -> Bool {
  match self.deck_translation(target) {
    None => false
    Some(f) => {
      let seen : Array[Int32] = []
      for p in 0..<self.size() {
        let q = f[p]
        if q < 0 {
          // left the truncation window: allowed only near the boundary
          if self.points[p].word.length() + self.points[target].word.length() <=
            self.radius {
            return false
          }
        } else {
          // must preserve the projection
          if self.project(q) != self.project(p) {
            return false
          }
          if seen.contains(q) {
            return false
          }
          seen.push(q)
        }
      }
      true
    }
  }
}

///|
/// The number of deck transformations defined on the whole truncated
/// cover: this grows to `|pi1|` as the radius grows, and for a finite
/// `pi1` it stabilises.
pub fn UniversalCover::deck_count(self : UniversalCover) -> Int32 {
  let mut c = 0
  for p in self.fibre(self.root) {
    if self.check_deck(p) {
      c = c + 1
    }
  }
  c
}

///|
/// A `k`-fold cyclic cover of the circle: the cycle of length `k`, with
/// projection `i |-> 0`.  Its deck group is `Z/k`.
#derive(Debug, Eq)
pub struct CyclicCover {
  k : Int32
  total : Space
}

///|
pub fn cyclic_cover(k : Int32) -> CyclicCover {
  CyclicCover::{ k, total: space_cycle(k), }
}

///|
pub fn CyclicCover::project(self : CyclicCover, v : Int32) -> Int32 {
  // the base circle has a single vertex, so every point lies over it
  v % self.k - v % self.k
}

///|
/// Deck transformations of the `k`-fold cover: the `k` rotations.
pub fn CyclicCover::deck_group(self : CyclicCover) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for s in 0..<self.k {
    let f : Array[Int32] = []
    for v in 0..<self.k {
      f.push((v + s) % self.k)
    }
    out.push(f)
  }
  out
}

///|
/// The covering is regular (normal): the deck group acts transitively on
/// each fibre.  For the cyclic cover the fibre is everything, so this is
/// transitivity of the rotation action.
pub fn CyclicCover::is_regular(self : CyclicCover) -> Bool {
  let deck = self.deck_group()
  for v in 0..<self.k {
    let orbit : Array[Int32] = []
    for f in deck {
      if !orbit.contains(f[v]) {
        orbit.push(f[v])
      }
    }
    if orbit.length() != self.k {
      return false
    }
  }
  true
}
