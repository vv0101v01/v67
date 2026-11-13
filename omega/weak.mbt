///|
/// A finite group by Cayley table, with elements `0 .. n-1`.
#derive(Debug, Eq)
pub struct Gp {
  n : Int32
  mul : Array[Array[Int32]]
  e : Int32
  inv : Array[Int32]
}

///|
pub fn Gp::new(mul : Array[Array[Int32]], e : Int32) -> Gp {
  let n = mul.length()
  let inv = Array::make(n, 0)
  for a in 0..<n {
    for b in 0..<n {
      if mul[a][b] == e {
        inv[a] = b
      }
    }
  }
  Gp::{ n, mul, e, inv, }
}

///|
pub fn Gp::op(self : Gp, a : Int32, b : Int32) -> Int32 {
  self.mul[a][b]
}

///|
pub fn Gp::check(self : Gp) -> Bool {
  for a in 0..<self.n {
    if self.mul[self.e][a] != a || self.mul[a][self.e] != a {
      return false
    }
    if self.mul[a][self.inv[a]] != self.e {
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
pub fn gp_cyclic(n : Int32) -> Gp {
  let mul : Array[Array[Int32]] = []
  for a in 0..<n {
    let row : Array[Int32] = []
    for b in 0..<n {
      row.push((a + b) % n)
    }
    mul.push(row)
  }
  Gp::new(mul, 0)
}

///|
/// A weak 2-group with one object, presented by Postnikov data:
///
/// * `pi0 = G`, the group of 1-cells (objects of the underlying monoidal
///   category, up to iso);
/// * `pi1 = Z/m`, the abelian group of 2-cells at the unit;
/// * `action : G x Z/m -> Z/m`, the `G`-module structure;
/// * `alpha : G^3 -> Z/m`, the **associator**.
///
/// Composition of 1-cells is strictly associative, but the *monoidal*
/// associativity `(g h) k ≅ g (h k)` holds only up to the 2-cell
/// `alpha(g,h,k)`.  That is exactly what "weak" means here, and the
/// coherence theorem is a finite check: the **pentagon** identity for
/// `alpha` is literally the group-cohomology 3-cocycle condition
///
/// ```text
/// g·alpha(h,k,l) - alpha(gh,k,l) + alpha(g,hk,l)
///                - alpha(g,h,kl) + alpha(g,h,k) = 0 .
/// ```
///
/// So `H^3(G, A)` classifies these weak 2-groups: the trivial class gives a
/// strictifiable one, a nonzero class gives a genuinely weak structure.
#derive(Debug, Eq)
pub struct WeakTwoGroup {
  g : Gp
  m : Int32
  action : Array[Array[Int32]]
  alpha : Array[Array[Array[Int32]]]
}

///|
pub fn WeakTwoGroup::new(
  g : Gp,
  m : Int32,
  action : Array[Array[Int32]],
  alpha : Array[Array[Array[Int32]]],
) -> WeakTwoGroup {
  WeakTwoGroup::{ g, m, action, alpha, }
}

///|
/// The strict 2-group on the same data: associator identically zero.
pub fn strict_two_group(g : Gp, m : Int32) -> WeakTwoGroup {
  let action : Array[Array[Int32]] = []
  for _ in 0..<g.n {
    let row : Array[Int32] = []
    for a in 0..<m {
      row.push(a)
    }
    action.push(row)
  }
  let alpha : Array[Array[Array[Int32]]] = []
  for _ in 0..<g.n {
    let plane : Array[Array[Int32]] = []
    for _ in 0..<g.n {
      let row : Array[Int32] = []
      for _ in 0..<g.n {
        row.push(0)
      }
      plane.push(row)
    }
    alpha.push(plane)
  }
  WeakTwoGroup::{ g, m, action, alpha, }
}

///|
fn zn(x : Int32, m : Int32) -> Int32 {
  let r = x % m
  if r < 0 {
    r + m
  } else {
    r
  }
}

///|
/// The action is by group automorphisms of `Z/m`.
pub fn WeakTwoGroup::check_action(self : WeakTwoGroup) -> Bool {
  for x in 0..<self.g.n {
    // identity acts trivially
    for a in 0..<self.m {
      if self.action[self.g.e][a] != a {
        return false
      }
    }
    for y in 0..<self.g.n {
      for a in 0..<self.m {
        // (xy)·a = x·(y·a)
        let lhs = self.action[self.g.op(x, y)][a]
        let rhs = self.action[x][self.action[y][a]]
        if lhs != rhs {
          return false
        }
      }
    }
    // each x acts additively
    for a in 0..<self.m {
      for b in 0..<self.m {
        if self.action[x][zn(a + b, self.m)] !=
          zn(self.action[x][a] + self.action[x][b], self.m) {
          return false
        }
      }
    }
  }
  true
}

///|
/// Normalisation: `alpha` vanishes whenever any argument is the unit.
/// Every cohomology class has a normalised representative, so this is no
/// loss of generality and it makes the unit coherence automatic.
pub fn WeakTwoGroup::is_normalised(self : WeakTwoGroup) -> Bool {
  let e = self.g.e
  for a in 0..<self.g.n {
    for b in 0..<self.g.n {
      if self.alpha[e][a][b] != 0 ||
        self.alpha[a][e][b] != 0 ||
        self.alpha[a][b][e] != 0 {
        return false
      }
    }
  }
  true
}

///|
/// The pentagon axiom, i.e. the 3-cocycle condition.  Returns the number of
/// quadruples `(g,h,k,l)` where it fails, so a failure is quantitative.
pub fn WeakTwoGroup::pentagon_defects(self : WeakTwoGroup) -> Int32 {
  let mut bad = 0
  let n = self.g.n
  for g in 0..<n {
    for h in 0..<n {
      for k in 0..<n {
        for l in 0..<n {
          let gh = self.g.op(g, h)
          let hk = self.g.op(h, k)
          let kl = self.g.op(k, l)
          // the two routes around the pentagon
          let route1 = self.alpha[g][h][k] +
            self.alpha[g][hk][l] +
            self.action[g][self.alpha[h][k][l]]
          let route2 = self.alpha[gh][k][l] + self.alpha[g][h][kl]
          if zn(route1, self.m) != zn(route2, self.m) {
            bad = bad + 1
          }
        }
      }
    }
  }
  bad
}

///|
pub fn WeakTwoGroup::is_coherent(self : WeakTwoGroup) -> Bool {
  self.check_action() && self.is_normalised() && self.pentagon_defects() == 0
}

///|
/// The coboundary of a 2-cochain `beta : G^2 -> Z/m`:
/// `(d beta)(g,h,k) = g·beta(h,k) - beta(gh,k) + beta(g,hk) - beta(g,h)`.
/// Associators differing by a coboundary give monoidally equivalent
/// 2-groups, so `B^3` is exactly the ambiguity in the presentation.
pub fn WeakTwoGroup::coboundary(
  self : WeakTwoGroup,
  beta : Array[Array[Int32]],
) -> Array[Array[Array[Int32]]] {
  let n = self.g.n
  let out : Array[Array[Array[Int32]]] = []
  for g in 0..<n {
    let plane : Array[Array[Int32]] = []
    for h in 0..<n {
      let row : Array[Int32] = []
      for k in 0..<n {
        let v = self.action[g][beta[h][k]] -
          beta[self.g.op(g, h)][k] +
          beta[g][self.g.op(h, k)] -
          beta[g][h]
        row.push(zn(v, self.m))
      }
      plane.push(row)
    }
    out.push(plane)
  }
  out
}

///|
/// Replace the associator by `alpha + d beta`: a monoidal equivalence
/// (a "gauge transformation" of the 2-group).  Coherence is preserved.
pub fn WeakTwoGroup::regauge(
  self : WeakTwoGroup,
  beta : Array[Array[Int32]],
) -> WeakTwoGroup {
  let d = self.coboundary(beta)
  let alpha : Array[Array[Array[Int32]]] = []
  for g in 0..<self.g.n {
    let plane : Array[Array[Int32]] = []
    for h in 0..<self.g.n {
      let row : Array[Int32] = []
      for k in 0..<self.g.n {
        row.push(zn(self.alpha[g][h][k] + d[g][h][k], self.m))
      }
      plane.push(row)
    }
    alpha.push(plane)
  }
  WeakTwoGroup::{ g: self.g, m: self.m, action: self.action, alpha, }
}

///|
/// Is the associator a coboundary, i.e. is this weak 2-group
/// *strictifiable*?  Decided by searching the finite space of normalised
/// 2-cochains — `m^(|G|-1)^2` of them, so this is practical for small `G`.
pub fn WeakTwoGroup::is_strictifiable(self : WeakTwoGroup) -> Bool {
  match self.strictifying_cochain() {
    Some(_) => true
    None => false
  }
}

///|
/// Find `beta` with `alpha + d beta = 0`, by brute force over normalised
/// 2-cochains.  Returns the first one found.
pub fn WeakTwoGroup::strictifying_cochain(
  self : WeakTwoGroup,
) -> Array[Array[Int32]]? {
  let n = self.g.n
  let e = self.g.e
  // free slots: pairs (h,k) with h != e and k != e
  let slots : Array[(Int32, Int32)] = []
  for h in 0..<n {
    for k in 0..<n {
      if h != e && k != e {
        slots.push((h, k))
      }
    }
  }
  let total = @core.ipow(self.m, slots.length())
  for code in 0..<total {
    let beta : Array[Array[Int32]] = []
    for _ in 0..<n {
      beta.push(Array::make(n, 0))
    }
    let mut cur = code
    for (h, k) in slots {
      beta[h][k] = cur % self.m
      cur = cur / self.m
    }
    let d = self.coboundary(beta)
    let mut ok = true
    for g in 0..<n {
      for h in 0..<n {
        for k in 0..<n {
          if zn(self.alpha[g][h][k] + d[g][h][k], self.m) != 0 {
            ok = false
          }
        }
      }
    }
    if ok {
      return Some(beta)
    }
  }
  None
}

///|
/// Enumerate all normalised 3-cocycles for the given `G`-module `Z/m`.
/// The count is `|Z^3|`; dividing by `|B^3|` gives `|H^3|`.
pub fn three_cocycles(
  g : Gp,
  m : Int32,
  action : Array[Array[Int32]],
  limit~ : Int32 = 200000,
) -> Array[Array[Array[Array[Int32]]]] {
  let n = g.n
  let e = g.e
  let slots : Array[(Int32, Int32, Int32)] = []
  for a in 0..<n {
    for b in 0..<n {
      for c in 0..<n {
        if a != e && b != e && c != e {
          slots.push((a, b, c))
        }
      }
    }
  }
  let total = @core.ipow(m, slots.length())
  let out : Array[Array[Array[Array[Int32]]]] = []
  let mut tried = 0
  for code in 0..<total {
    if tried >= limit {
      break
    }
    tried = tried + 1
    let alpha : Array[Array[Array[Int32]]] = []
    for _ in 0..<n {
      let plane : Array[Array[Int32]] = []
      for _ in 0..<n {
        plane.push(Array::make(n, 0))
      }
      alpha.push(plane)
    }
    let mut cur = code
    for (a, b, c) in slots {
      alpha[a][b][c] = cur % m
      cur = cur / m
    }
    let w = WeakTwoGroup::{ g, m, action, alpha, }
    if w.pentagon_defects() == 0 {
      out.push(alpha)
    }
  }
  out
}

///|
/// The order of `H^3(G, Z/m)` for a trivial action, computed as
/// `|Z^3| / |B^3|` by enumerating both finite sets.  This is the number of
/// inequivalent weak 2-groups with the given `pi0` and `pi1`.
pub fn h3_order(
  g : Gp,
  m : Int32,
  limit~ : Int32 = 200000,
) -> (Int32, Int32, Int32) {
  let action : Array[Array[Int32]] = []
  for _ in 0..<g.n {
    let row : Array[Int32] = []
    for a in 0..<m {
      row.push(a)
    }
    action.push(row)
  }
  let zs = three_cocycles(g, m, action, limit~)
  // count distinct coboundaries
  let n = g.n
  let e = g.e
  let slots : Array[(Int32, Int32)] = []
  for h in 0..<n {
    for k in 0..<n {
      if h != e && k != e {
        slots.push((h, k))
      }
    }
  }
  let w = strict_two_group(g, m)
  let seen : Array[Array[Array[Array[Int32]]]] = []
  let total = @core.ipow(m, slots.length())
  let mut tried = 0
  for code in 0..<total {
    if tried >= limit {
      break
    }
    tried = tried + 1
    let beta : Array[Array[Int32]] = []
    for _ in 0..<n {
      beta.push(Array::make(n, 0))
    }
    let mut cur = code
    for (h, k) in slots {
      beta[h][k] = cur % m
      cur = cur / m
    }
    let d = w.coboundary(beta)
    if !seen.contains(d) {
      seen.push(d)
    }
  }
  let b3 = seen.length()
  (zs.length(), b3, if b3 == 0 { 0 } else { zs.length() / b3 })
}
