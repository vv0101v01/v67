///|
/// The total space of the trivial principal `G`-bundle over the grid:
/// points are pairs `(vertex, fibre element)`, coded `v * |G| + g`.
///
/// A connection is exactly a *horizontal distribution* on this space: at
/// each point, a choice of lift of each base direction.  Frobenius'
/// theorem then says the distribution is integrable — the horizontal
/// leaves foliate the bundle — precisely when the curvature vanishes.
/// Everything here is finite, so "integrable" becomes a graph connectivity
/// computation and the theorem becomes a testable identity.
#derive(Debug, Eq)
pub struct Bundle {
  conn : Connection
}

///|
pub fn Bundle::new(conn : Connection) -> Bundle {
  Bundle::{ conn, }
}

///|
pub fn Bundle::size(self : Bundle) -> Int32 {
  self.conn.grid.nverts() * self.conn.group.n
}

///|
pub fn Bundle::point(self : Bundle, v : Int32, g : Int32) -> Int32 {
  v * self.conn.group.n + g
}

///|
pub fn Bundle::base(self : Bundle, p : Int32) -> Int32 {
  p / self.conn.group.n
}

///|
pub fn Bundle::fibre(self : Bundle, p : Int32) -> Int32 {
  p % self.conn.group.n
}

///|
/// The horizontal lift of the base step `v -> v + e_d` at the point
/// `(v, g)`: it lands at `(v + e_d, a(v,d) * g)`.
///
/// The transport multiplies on the side opposite to the structure-group
/// action, which is exactly what makes the lift equivariant: for a
/// non-abelian group the two sides differ, and choosing the wrong one
/// breaks `check_equivariance` below.
pub fn Bundle::horizontal(
  self : Bundle,
  p : Int32,
  d : Int32,
  forward : Bool,
) -> Int32? {
  let v = self.base(p)
  let g = self.fibre(p)
  let next = self.conn.grid.step(v, d, forward)
  if next < 0 {
    return None
  }
  let a = if forward {
    self.conn.transport[self.conn.grid.edge_slot(v, d)]
  } else {
    self.conn.group.inverse(
      self.conn.transport[self.conn.grid.edge_slot(next, d)],
    )
  }
  Some(self.point(next, self.conn.group.op(a, g)))
}

///|
/// The horizontal distribution is right-equivariant: lifting at `g * h`
/// equals the lift at `g`, right-translated by `h`.  This is the axiom that distinguishes a
/// *principal* connection from an arbitrary distribution, and it is the
/// reason curvature is conjugation-covariant rather than invariant.
pub fn Bundle::check_equivariance(self : Bundle) -> Bool {
  let gn = self.conn.group.n
  for v in 0..<self.conn.grid.nverts() {
    for g in 0..<gn {
      for h in 0..<gn {
        for d in 0..<self.conn.grid.ndirs() {
          for fwd in [true, false] {
            let p = self.point(v, g)
            let ph = self.point(v, self.conn.group.op(g, h))
            match (self.horizontal(p, d, fwd), self.horizontal(ph, d, fwd)) {
              (None, None) => ()
              (Some(a), Some(b)) => {
                let expected = self.point(
                  self.base(a),
                  self.conn.group.op(self.fibre(a), h),
                )
                if b != expected {
                  return false
                }
              }
              _ => return false
            }
          }
        }
      }
    }
  }
  true
}

///|
/// The horizontal leaf through a point: everything reachable by horizontal
/// moves.  Computed by breadth-first search on the horizontal graph.
pub fn Bundle::leaf(self : Bundle, start : Int32) -> Array[Int32] {
  let seen = Array::make(self.size(), false)
  let queue : Array[Int32] = [start]
  seen[start] = true
  let out : Array[Int32] = []
  let mut head = 0
  while head < queue.length() {
    let p = queue[head]
    head = head + 1
    out.push(p)
    for d in 0..<self.conn.grid.ndirs() {
      for fwd in [true, false] {
        match self.horizontal(p, d, fwd) {
          None => ()
          Some(q) =>
            if !seen[q] {
              seen[q] = true
              queue.push(q)
            }
        }
      }
    }
  }
  out.sort()
  out
}

///|
/// All horizontal leaves, i.e. the integral manifolds of the distribution.
pub fn Bundle::leaves(self : Bundle) -> Array[Array[Int32]] {
  let seen = Array::make(self.size(), false)
  let out : Array[Array[Int32]] = []
  for p in 0..<self.size() {
    if !seen[p] {
      let l = self.leaf(p)
      for q in l {
        seen[q] = true
      }
      out.push(l)
    }
  }
  out
}

///|
/// Frobenius integrability, in its finite form: the horizontal distribution
/// integrates to a foliation whose leaves each cover the base exactly once
/// (a flat connection on a contractible base is trivial).  Equivalently
/// there are exactly `|G|` leaves, each of size `|base|`.
///
/// The theorem this checks: **flat <=> integrable with trivial holonomy**.
pub fn Bundle::is_integrable_trivially(self : Bundle) -> Bool {
  let ls = self.leaves()
  if ls.length() != self.conn.group.n {
    return false
  }
  for l in ls {
    if l.length() != self.conn.grid.nverts() {
      return false
    }
    // one point per base vertex: the leaf is a graph over the base
    let bases : Array[Int32] = []
    for p in l {
      let b = self.base(p)
      if bases.contains(b) {
        return false
      }
      bases.push(b)
    }
  }
  true
}

///|
/// The holonomy group at a base vertex: all transports around loops based
/// there.  For a grid (contractible base) it is generated by the plaquette
/// holonomies, and it is trivial exactly when the connection is flat.
pub fn Bundle::holonomy_group(self : Bundle, v : Int32) -> Array[Int32] {
  let start = self.point(v, self.conn.group.e)
  let l = self.leaf(start)
  let out : Array[Int32] = []
  for p in l {
    if self.base(p) == v {
      out.push(self.fibre(p))
    }
  }
  out.sort()
  out
}

///|
/// The leaf size measures the failure of integrability: a nontrivial
/// holonomy group of order `h` merges `h` sheets into one leaf.
pub fn Bundle::leaf_size(self : Bundle, v : Int32) -> Int32 {
  self.leaf(self.point(v, self.conn.group.e)).length()
}

///|
/// The discrete Bianchi identity `d_A F = 0`, as an exact group identity.
///
/// Take the unit 3-cube at `v` in directions `i < j < k` and its "hexagonal"
/// loop `+i +j +k -i -j -k`.  That hexagon bounds two different staircase
/// surfaces, each a fan of three plaquettes around an interior vertex:
///
/// * filling A fans around `v + e_j`, using the faces (i,j)@v, (i,k)@v+e_j,
///   (j,k)@v;
/// * filling B fans around `v + e_i + e_k`, using (i,k)@v, (j,k)@v+e_i,
///   (i,j)@v+e_k.
///
/// For a fan, the spokes cancel and the product of the three face
/// holonomies (each based at the fan centre, in cyclic order) is the outer
/// boundary loop.  Conjugating back to `v` must therefore give the *same*
/// hexagon holonomy both ways.  Equating the two expressions is exactly the
/// Bianchi identity, and it holds for every connection — flat or not.
pub fn Connection::bianchi_sides(
  self : Connection,
  v : Int32,
  i : Int32,
  j : Int32,
  k : Int32,
) -> (Int32, Int32)? {
  let g = self.group
  // filling A : fan centre v + e_j
  let ua = match self.along(v, [(j, true)]) {
    Some(t) => t
    None => return None
  }
  let sa1 = match
    self.along(self.grid.step(v, j, true), [
      (j, false),
      (i, true),
      (j, true),
      (i, false),
    ]) {
    Some(t) => t
    None => return None
  }
  let sa2 = match
    self.along(self.grid.step(v, j, true), [
      (i, true),
      (k, true),
      (i, false),
      (k, false),
    ]) {
    Some(t) => t
    None => return None
  }
  let sa3 = match
    self.along(self.grid.step(v, j, true), [
      (k, true),
      (j, false),
      (k, false),
      (j, true),
    ]) {
    Some(t) => t
    None => return None
  }
  // Wilson lines compose in reverse path order, so the fan product is
  // sa3*sa2*sa1 and the spoke conjugation is ua^{-1} (...) ua.
  let fan_a = g.product([sa3, sa2, sa1])
  let lhs = g.product([g.inverse(ua), fan_a, ua])
  // filling B : fan centre v + e_i + e_k
  let vi = self.grid.step(v, i, true)
  if vi < 0 {
    return None
  }
  let cent_b = self.grid.step(vi, k, true)
  if cent_b < 0 {
    return None
  }
  // the path realising fan B's spoke is +k then +i (000 -> 001 -> 101),
  // not +i then +k: for a curved connection the two differ.
  let ub = match self.along(v, [(k, true), (i, true)]) {
    Some(t) => t
    None => return None
  }
  let sb1 = match
    self.along(cent_b, [(i, false), (k, false), (i, true), (k, true)]) {
    Some(t) => t
    None => return None
  }
  let sb2 = match
    self.along(cent_b, [(k, false), (j, true), (k, true), (j, false)]) {
    Some(t) => t
    None => return None
  }
  let sb3 = match
    self.along(cent_b, [(j, true), (i, false), (j, false), (i, true)]) {
    Some(t) => t
    None => return None
  }
  let fan_b = g.product([sb3, sb2, sb1])
  let rhs = g.product([g.inverse(ub), fan_b, ub])
  Some((lhs, rhs))
}

///|
/// `d_A F = 0` on the unit 3-cube at `v`.  Returns `false` only if the
/// identity genuinely fails; `None`-like boundary cases are reported as
/// `true` because there is no 3-cube there to check.
pub fn Connection::check_bianchi(
  self : Connection,
  v : Int32,
  i : Int32,
  j : Int32,
  k : Int32,
) -> Bool {
  match self.bianchi_sides(v, i, j, k) {
    None => true
    Some((lhs, rhs)) => lhs == rhs
  }
}

///|
/// Bianchi on every 3-cube of the grid.
pub fn Connection::check_bianchi_all(self : Connection) -> Bool {
  for v in 0..<self.grid.nverts() {
    for i in 0..<self.grid.ndirs() {
      for j in (i + 1)..<self.grid.ndirs() {
        for k in (j + 1)..<self.grid.ndirs() {
          if !self.check_bianchi(v, i, j, k) {
            return false
          }
        }
      }
    }
  }
  true
}
