///|
/// A globular set: cells in each dimension with source and target in the
/// dimension below, satisfying the globularity identities
/// `s(s(x)) = s(t(x))` and `t(s(x)) = t(t(x))`.
///
/// This is the shape of an omega-category.  Cells are coded by `Int32`
/// within each dimension, so the whole structure is finite and every law
/// below is decidable by exhaustion.
#derive(Debug, Eq)
pub struct Globular {
  dims : Array[Int32]
  src : Array[Array[Int32]]
  tgt : Array[Array[Int32]]
}

///|
pub fn Globular::new(
  dims : Array[Int32],
  src : Array[Array[Int32]],
  tgt : Array[Array[Int32]],
) -> Globular {
  Globular::{ dims, src, tgt, }
}

///|
pub fn Globular::top(self : Globular) -> Int32 {
  self.dims.length() - 1
}

///|
pub fn Globular::count(self : Globular, k : Int32) -> Int32 {
  if k < 0 || k >= self.dims.length() {
    0
  } else {
    self.dims[k]
  }
}

///|
/// The globularity identities plus well-definedness of the face maps.
pub fn Globular::check(self : Globular) -> Bool {
  for k in 1..<self.dims.length() {
    if self.src[k].length() != self.dims[k] ||
      self.tgt[k].length() != self.dims[k] {
      return false
    }
    for x in 0..<self.dims[k] {
      let s = self.src[k][x]
      let t = self.tgt[k][x]
      if s < 0 || s >= self.dims[k - 1] || t < 0 || t >= self.dims[k - 1] {
        return false
      }
      if k >= 2 {
        // s s = s t and t s = t t
        if self.src[k - 1][s] != self.src[k - 1][t] {
          return false
        }
        if self.tgt[k - 1][s] != self.tgt[k - 1][t] {
          return false
        }
      }
    }
  }
  true
}

///|
/// Is the globular set `n`-truncated: no cells above dimension `n`?
pub fn Globular::is_truncated(self : Globular, n : Int32) -> Bool {
  for k in (n + 1)..<self.dims.length() {
    if self.dims[k] != 0 {
      return false
    }
  }
  true
}

///|
/// A strict omega-category structure on a globular set: partially defined
/// compositions `comp[k][a][b]` (or -1 when not composable) and identities
/// `ident[k][x]` lifting an `(k-1)`-cell to a `k`-cell.
///
/// Strictness means associativity and the interchange law hold *on the
/// nose*.  The weak version below replaces those equations by cells, which
/// is the whole point of an omega-groupoid.
#derive(Debug, Eq)
pub struct StrictOmega {
  shape : Globular
  comp : Array[Array[Array[Int32]]]
  ident : Array[Array[Int32]]
}

///|
pub fn StrictOmega::new(
  shape : Globular,
  comp : Array[Array[Array[Int32]]],
  ident : Array[Array[Int32]],
) -> StrictOmega {
  StrictOmega::{ shape, comp, ident, }
}

///|
/// `k`-composition of `a` and `b` (written `a ; b`), if defined.
pub fn StrictOmega::compose(
  self : StrictOmega,
  k : Int32,
  a : Int32,
  b : Int32,
) -> Int32? {
  if k < 0 || k >= self.comp.len_guard() {
    return None
  }
  let table = self.comp[k]
  if a < 0 || a >= table.length() {
    return None
  }
  let row = table[a]
  if b < 0 || b >= row.length() {
    return None
  }
  if row[b] < 0 {
    None
  } else {
    Some(row[b])
  }
}

///|
fn Array::len_guard(self : Array[Array[Array[Int32]]]) -> Int32 {
  self.length()
}

///|
/// Two `n`-cells are `k`-composable when the iterated `k`-source of the
/// second matches the iterated `k`-target of the first.
pub fn StrictOmega::composable(
  self : StrictOmega,
  k : Int32,
  n : Int32,
  a : Int32,
  b : Int32,
) -> Bool {
  let mut ta = a
  let mut sb = b
  for _ in k..<n {
    ta = self.shape.tgt[n][ta]
    sb = self.shape.src[n][sb]
    break
  }
  // iterate down to level k properly
  let mut x = a
  let mut y = b
  for lvl in (k + 1)..<=n {
    x = self.shape.tgt[lvl][x]
    y = self.shape.src[lvl][y]
  }
  let _ = ta
  let _ = sb
  x == y
}

///|
/// Strict associativity at every level where both sides are defined.
pub fn StrictOmega::check_associative(self : StrictOmega) -> Bool {
  for k in 0..<self.comp.length() {
    let table = self.comp[k]
    let n = table.length()
    for a in 0..<n {
      for b in 0..<n {
        for c in 0..<n {
          match (self.compose(k, a, b), self.compose(k, b, c)) {
            (Some(ab), Some(bc)) => {
              let lhs = self.compose(k, ab, c)
              let rhs = self.compose(k, a, bc)
              match (lhs, rhs) {
                (Some(x), Some(y)) => if x != y { return false }
                (None, None) => ()
                _ => return false
              }
            }
            _ => ()
          }
        }
      }
    }
  }
  true
}

///|
/// Identity laws: `ident(k, s(x)) ; x = x = x ; ident(k, t(x))`.
pub fn StrictOmega::check_units(self : StrictOmega) -> Bool {
  for k in 1..<self.shape.dims.length() {
    if k - 1 >= self.ident.length() {
      return false
    }
    for x in 0..<self.shape.dims[k] {
      let s = self.shape.src[k][x]
      let t = self.shape.tgt[k][x]
      match self.compose(k - 1, self.ident[k - 1][s], x) {
        Some(y) => if y != x { return false }
        None => return false
      }
      match self.compose(k - 1, x, self.ident[k - 1][t]) {
        Some(y) => if y != x { return false }
        None => return false
      }
    }
  }
  true
}

///|
/// Every cell has an inverse for its top-level composition: the groupoid
/// condition.  `inv[k][x]` is stored implicitly by searching, so this is a
/// decision procedure rather than extra data.
pub fn StrictOmega::check_inverses(self : StrictOmega) -> Bool {
  for k in 1..<self.shape.dims.length() {
    for x in 0..<self.shape.dims[k] {
      let s = self.shape.src[k][x]
      let t = self.shape.tgt[k][x]
      let mut found_left = false
      let mut found_right = false
      for y in 0..<self.shape.dims[k] {
        if self.shape.src[k][y] == t && self.shape.tgt[k][y] == s {
          match self.compose(k - 1, x, y) {
            Some(id) => if id == self.ident[k - 1][s] { found_right = true }
            None => ()
          }
          match self.compose(k - 1, y, x) {
            Some(id) => if id == self.ident[k - 1][t] { found_left = true }
            None => ()
          }
        }
      }
      if !found_left || !found_right {
        return false
      }
    }
  }
  true
}

///|
/// The interchange (Godement) law:
/// `(a ;_k b) ;_j (c ;_k d) = (a ;_j c) ;_k (b ;_j d)` for `j < k`.
/// In a strict omega-category this is an equation; in a weak one it is a
/// higher cell, and that cell is exactly what the weak model records.
pub fn StrictOmega::check_interchange(self : StrictOmega) -> Bool {
  for j in 0..<self.comp.length() {
    for k in (j + 1)..<self.comp.length() {
      let n = self.shape.dims[k + 1]
      if n == 0 {
        continue
      }
      for a in 0..<n {
        for b in 0..<n {
          for c in 0..<n {
            for d in 0..<n {
              let ab = self.compose(k, a, b)
              let cd = self.compose(k, c, d)
              let ac = self.compose(j, a, c)
              let bd = self.compose(j, b, d)
              match (ab, cd, ac, bd) {
                (Some(x), Some(y), Some(u), Some(w)) => {
                  let lhs = self.compose(j, x, y)
                  let rhs = self.compose(k, u, w)
                  match (lhs, rhs) {
                    (Some(p), Some(q)) => if p != q { return false }
                    (None, None) => ()
                    _ => return false
                  }
                }
                _ => ()
              }
            }
          }
        }
      }
    }
  }
  true
}
