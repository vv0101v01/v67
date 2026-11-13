///|
/// A finite group given by its Cayley table.  Using an honest non-abelian
/// group matters: curvature is only interesting when parallel transports
/// fail to commute, and an abelian structure group hides that.
#derive(Debug, Eq)
pub struct FinGroup {
  n : Int32
  mul : Array[Array[Int32]]
  e : Int32
  inv : Array[Int32]
}

///|
pub fn FinGroup::new(mul : Array[Array[Int32]], e : Int32) -> FinGroup {
  let n = mul.length()
  let inv = Array::make(n, -1)
  for i in 0..<n {
    for j in 0..<n {
      if mul[i][j] == e {
        inv[i] = j
      }
    }
  }
  FinGroup::{ n, mul, e, inv, }
}

///|
pub fn FinGroup::op(self : FinGroup, a : Int32, b : Int32) -> Int32 {
  self.mul[a][b]
}

///|
pub fn FinGroup::inverse(self : FinGroup, a : Int32) -> Int32 {
  self.inv[a]
}

///|
/// The group axioms, checked exhaustively: associativity, unit, inverses.
pub fn FinGroup::check(self : FinGroup) -> Bool {
  for a in 0..<self.n {
    if self.mul[self.e][a] != a || self.mul[a][self.e] != a {
      return false
    }
    if self.mul[a][self.inv[a]] != self.e || self.mul[self.inv[a]][a] != self.e {
      return false
    }
    for b in 0..<self.n {
      for c in 0..<self.n {
        if self.mul[self.mul[a][b]][c] != self.mul[a][self.mul[b][c]] {
          return false
        }
      }
    }
  }
  true
}

///|
pub fn FinGroup::is_abelian(self : FinGroup) -> Bool {
  for a in 0..<self.n {
    for b in 0..<self.n {
      if self.mul[a][b] != self.mul[b][a] {
        return false
      }
    }
  }
  true
}

///|
/// Product of a list, left to right.
pub fn FinGroup::product(self : FinGroup, xs : Array[Int32]) -> Int32 {
  let mut acc = self.e
  for x in xs {
    acc = self.mul[acc][x]
  }
  acc
}

///|
/// The cyclic group `Z/n`.
pub fn cyclic(n : Int32) -> FinGroup {
  let mul : Array[Array[Int32]] = []
  for i in 0..<n {
    let row : Array[Int32] = []
    for j in 0..<n {
      row.push((i + j) % n)
    }
    mul.push(row)
  }
  FinGroup::new(mul, 0)
}

///|
/// The symmetric group `S_3`, the smallest non-abelian group.  Permutations
/// are coded in lexicographic order of their one-line notation.
pub fn symmetric3() -> FinGroup {
  let perms : Array[Array[Int32]] = []
  fn rec(cur : Array[Int32], used : Array[Bool]) -> Unit {
    if cur.length() == 3 {
      let p : Array[Int32] = []
      for x in cur {
        p.push(x)
      }
      perms.push(p)
    } else {
      for i in 0..<3 {
        if !used[i] {
          used[i] = true
          cur.push(i)
          rec(cur, used)
          ignore(cur.pop())
          used[i] = false
        }
      }
    }
  }

  rec([], [false, false, false])
  let mul : Array[Array[Int32]] = []
  for i in 0..<6 {
    let row : Array[Int32] = []
    for j in 0..<6 {
      // (i * j)(x) = i(j(x))
      let comp : Array[Int32] = [
        perms[i][perms[j][0]],
        perms[i][perms[j][1]],
        perms[i][perms[j][2]],
      ]
      let mut idx = -1
      for k in 0..<6 {
        if perms[k] == comp {
          idx = k
        }
      }
      row.push(idx)
    }
    mul.push(row)
  }
  let mut e = 0
  for k in 0..<6 {
    if perms[k] == [0, 1, 2] {
      e = k
    }
  }
  FinGroup::new(mul, e)
}

///|
/// A rectangular grid of any dimension, the base "manifold".  Vertices are
/// coded in mixed radix; the grid is contractible, so every flat connection
/// on it is gauge-trivial — which is what makes it a good test bed.
#derive(Debug, Eq)
pub struct Grid {
  dims : Array[Int32]
}

///|
pub fn Grid::new(dims : Array[Int32]) -> Grid {
  Grid::{ dims, }
}

///|
pub fn Grid::ndirs(self : Grid) -> Int32 {
  self.dims.length()
}

///|
pub fn Grid::nverts(self : Grid) -> Int32 {
  let mut n = 1
  for d in self.dims {
    n = n * d
  }
  n
}

///|
pub fn Grid::coords(self : Grid, v : Int32) -> Array[Int32] {
  let out = Array::make(self.ndirs(), 0)
  let mut cur = v
  for d in 0..<self.ndirs() {
    out[d] = cur % self.dims[d]
    cur = cur / self.dims[d]
  }
  out
}

///|
pub fn Grid::index(self : Grid, cs : Array[Int32]) -> Int32 {
  let mut acc = 0
  let mut scale = 1
  for d in 0..<self.ndirs() {
    acc = acc + cs[d] * scale
    scale = scale * self.dims[d]
  }
  acc
}

///|
/// The neighbour of `v` in direction `d`, or `-1` at the boundary.
pub fn Grid::step(self : Grid, v : Int32, d : Int32, forward : Bool) -> Int32 {
  let cs = self.coords(v)
  let next = if forward { cs[d] + 1 } else { cs[d] - 1 }
  if next < 0 || next >= self.dims[d] {
    -1
  } else {
    cs[d] = next
    self.index(cs)
  }
}

///|
/// Slot for the directed edge `v -> v + e_d` in the connection array.
pub fn Grid::edge_slot(self : Grid, v : Int32, d : Int32) -> Int32 {
  v * self.ndirs() + d
}

///|
/// A discrete connection: a group element on every directed edge, the
/// parallel transport along it.  Backward edges carry the inverse, so the
/// data is a genuine connection rather than an arbitrary labelling.
#derive(Debug, Eq)
pub struct Connection {
  grid : Grid
  group : FinGroup
  transport : Array[Int32]
}

///|
/// The trivial connection: every transport is the identity.
pub fn Connection::trivial(grid : Grid, group : FinGroup) -> Connection {
  Connection::{
    grid,
    group,
    transport: Array::make(grid.nverts() * grid.ndirs(), group.e),
  }
}

///|
pub fn Connection::from_edges(
  grid : Grid,
  group : FinGroup,
  edges : Array[Int32],
) -> Connection {
  Connection::{ grid, group, transport: edges, }
}

///|
/// Transport along one step; `None` at the boundary.
pub fn Connection::step(
  self : Connection,
  v : Int32,
  d : Int32,
  forward : Bool,
) -> Int32? {
  if forward {
    if self.grid.step(v, d, true) < 0 {
      None
    } else {
      Some(self.transport[self.grid.edge_slot(v, d)])
    }
  } else if self.grid.step(v, d, false) < 0 {
    None
  } else {
    let prev = self.grid.step(v, d, false)
    Some(self.group.inverse(self.transport[self.grid.edge_slot(prev, d)]))
  }
}

///|
/// Parallel transport along a path given as a list of `(direction, forward)`,
/// as a Wilson line: `W = a_n * ... * a_1`, the later edges multiplying on
/// the left.  This is the convention that makes the horizontal lift
/// `(v,h) |-> (v+e_d, a * h)` compose correctly and commute with the right
/// `G`-action; the opposite order breaks equivariance for non-abelian `G`.
/// Returns `None` if the path leaves the grid.
pub fn Connection::along(
  self : Connection,
  start : Int32,
  path : Array[(Int32, Bool)],
) -> Int32? {
  let mut acc = self.group.e
  let mut v = start
  for (d, fwd) in path {
    let next = self.grid.step(v, d, fwd)
    if next < 0 {
      return None
    }
    let g = if fwd {
      self.transport[self.grid.edge_slot(v, d)]
    } else {
      self.group.inverse(self.transport[self.grid.edge_slot(next, d)])
    }
    acc = self.group.op(g, acc)
    v = next
  }
  Some(acc)
}

///|
/// The plaquette holonomy at `v` in the plane `(i, j)`: transport around
/// the unit square `v -> v+e_i -> v+e_i+e_j -> v+e_j -> v`.
///
/// This *is* the curvature.  A connection is flat exactly when every
/// plaquette holonomy is the identity, and for a non-abelian group the
/// holonomy is only defined up to conjugation (choice of base point),
/// which is why flatness — not the individual value — is gauge invariant.
pub fn Connection::curvature(
  self : Connection,
  v : Int32,
  i : Int32,
  j : Int32,
) -> Int32? {
  self.along(v, [(i, true), (j, true), (i, false), (j, false)])
}

///|
/// All plaquette holonomies, as `(vertex, i, j, holonomy)`.
pub fn Connection::curvatures(
  self : Connection,
) -> Array[(Int32, Int32, Int32, Int32)] {
  let out : Array[(Int32, Int32, Int32, Int32)] = []
  for v in 0..<self.grid.nverts() {
    for i in 0..<self.grid.ndirs() {
      for j in (i + 1)..<self.grid.ndirs() {
        match self.curvature(v, i, j) {
          None => ()
          Some(g) => out.push((v, i, j, g))
        }
      }
    }
  }
  out
}

///|
pub fn Connection::is_flat(self : Connection) -> Bool {
  for (_, _, _, g) in self.curvatures() {
    if g != self.group.e {
      return false
    }
  }
  true
}

///|
/// Total curvature energy: the number of non-identity plaquettes, the
/// discrete Yang–Mills functional's simplest cousin.
pub fn Connection::curvature_count(self : Connection) -> Int32 {
  let mut c = 0
  for (_, _, _, g) in self.curvatures() {
    if g != self.group.e {
      c = c + 1
    }
  }
  c
}

///|
/// A gauge transformation `g : vertices -> G` acts by
/// `a(v,d) |-> g(v+e_d) a(v,d) g(v)^{-1}`, so that a Wilson line from `u`
/// to `w` transforms as `W |-> g(w) W g(u)^{-1}`.
pub fn Connection::gauge_transform(
  self : Connection,
  g : Array[Int32],
) -> Connection {
  // start from a copy so that boundary slots (which carry no edge) are
  // preserved verbatim; gauge transformations must be invertible on data
  let out : Array[Int32] = []
  for t in self.transport {
    out.push(t)
  }
  for v in 0..<self.grid.nverts() {
    for d in 0..<self.grid.ndirs() {
      let next = self.grid.step(v, d, true)
      if next >= 0 {
        let slot = self.grid.edge_slot(v, d)
        out[slot] = self.group.op(
          self.group.op(g[next], self.transport[slot]),
          self.group.inverse(g[v]),
        )
      }
    }
  }
  Connection::{ grid: self.grid, group: self.group, transport: out, }
}

///|
/// Curvature is *covariant* under gauge transformations: the holonomy at
/// `v` is conjugated by `g(v)`.  In particular flatness is gauge invariant,
/// which is the statement that flatness is a property of the bundle.
pub fn Connection::check_gauge_covariance(
  self : Connection,
  g : Array[Int32],
) -> Bool {
  let other = self.gauge_transform(g)
  for (v, i, j, h) in self.curvatures() {
    match other.curvature(v, i, j) {
      None => return false
      Some(h2) => {
        let expected = self.group.op(
          self.group.op(g[v], h),
          self.group.inverse(g[v]),
        )
        if h2 != expected {
          return false
        }
      }
    }
  }
  true
}
