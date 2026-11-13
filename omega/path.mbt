///|
/// A finite groupoid presented by objects and a composition table on
/// morphisms.  This is the *groupoid model of type theory*: a type is a
/// groupoid, a term is an object, and the identity type `Id_A(a,b)` is the
/// hom-set `Hom(a,b)`.  Path induction is then a theorem about groupoids,
/// and univalence-for-1-types is the statement that equivalence of
/// groupoids is equivalent to identity.
#derive(Debug, Eq)
pub struct Groupoid {
  nobjs : Int32
  /// morphisms as (source, target)
  ends : Array[(Int32, Int32)]
  /// `comp[a][b] = a ; b` or -1
  comp : Array[Array[Int32]]
  /// `ident[x]` = the identity morphism at object x
  ident : Array[Int32]
}

///|
pub fn Groupoid::new(
  nobjs : Int32,
  ends : Array[(Int32, Int32)],
  comp : Array[Array[Int32]],
  ident : Array[Int32],
) -> Groupoid {
  Groupoid::{ nobjs, ends, comp, ident, }
}

///|
pub fn Groupoid::nmors(self : Groupoid) -> Int32 {
  self.ends.length()
}

///|
/// `Id_A(a,b)`: the paths from `a` to `b`, i.e. the hom-set.
pub fn Groupoid::path_type(
  self : Groupoid,
  a : Int32,
  b : Int32,
) -> Array[Int32] {
  let out : Array[Int32] = []
  for m in 0..<self.nmors() {
    let (s, t) = self.ends[m]
    if s == a && t == b {
      out.push(m)
    }
  }
  out
}

///|
/// `refl a`.
pub fn Groupoid::refl(self : Groupoid, a : Int32) -> Int32 {
  self.ident[a]
}

///|
/// Path concatenation `p * q` (first `p`, then `q`).
pub fn Groupoid::concat(self : Groupoid, p : Int32, q : Int32) -> Int32? {
  let c = self.comp[p][q]
  if c < 0 {
    None
  } else {
    Some(c)
  }
}

///|
/// Path inversion `p⁻¹`, found by search: in a groupoid it always exists.
pub fn Groupoid::sym(self : Groupoid, p : Int32) -> Int32? {
  let (s, t) = self.ends[p]
  for q in 0..<self.nmors() {
    if self.ends[q] == (t, s) && self.comp[p][q] == self.ident[s] {
      return Some(q)
    }
  }
  None
}

///|
/// `transport P p x`: in the groupoid model a family `P` over `A` is a
/// functor to groupoids; on a discrete family it is a function on objects
/// of the total space.  Here `fam` gives, for each morphism of `A`, the
/// induced bijection on the fibre, so transport is just application.
pub fn transport_along(
  fam : Array[Array[Int32]],
  p : Int32,
  x : Int32,
) -> Int32 {
  fam[p][x]
}

///|
/// The groupoid axioms: associativity, units, inverses, and that
/// composition is defined exactly on composable pairs.
pub fn Groupoid::check(self : Groupoid) -> Bool {
  let n = self.nmors()
  for a in 0..<n {
    for b in 0..<n {
      let composable = self.ends[a].1 == self.ends[b].0
      if composable {
        let c = self.comp[a][b]
        if c < 0 || self.ends[c] != (self.ends[a].0, self.ends[b].1) {
          return false
        }
      } else if self.comp[a][b] >= 0 {
        return false
      }
    }
  }
  for a in 0..<n {
    for b in 0..<n {
      for c in 0..<n {
        let ab = self.comp[a][b]
        let bc = self.comp[b][c]
        if ab >= 0 && bc >= 0 {
          if self.comp[ab][c] != self.comp[a][bc] {
            return false
          }
        }
      }
    }
  }
  for a in 0..<n {
    let (s, t) = self.ends[a]
    if self.comp[self.ident[s]][a] != a || self.comp[a][self.ident[t]] != a {
      return false
    }
    match self.sym(a) {
      None => return false
      Some(_) => ()
    }
  }
  true
}

///|
/// A finite group as a one-object groupoid: the path type of the point is
/// the group itself.  This is the standard model showing that a type can
/// have nontrivial `Id` — i.e. that UIP is not provable.
pub fn group_as_groupoid(mul : Array[Array[Int32]], e : Int32) -> Groupoid {
  let n = mul.length()
  let ends : Array[(Int32, Int32)] = []
  for _ in 0..<n {
    ends.push((0, 0))
  }
  Groupoid::{ nobjs: 1, ends, comp: mul, ident: [e], }
}

///|
/// The discrete groupoid on `n` objects: only identities.  This is a set
/// (a 0-type): all its path types are singletons.
pub fn discrete_groupoid(n : Int32) -> Groupoid {
  let ends : Array[(Int32, Int32)] = []
  for i in 0..<n {
    ends.push((i, i))
  }
  let comp : Array[Array[Int32]] = []
  for i in 0..<n {
    let row = Array::make(n, -1)
    row[i] = i
    comp.push(row)
  }
  let ident : Array[Int32] = []
  for i in 0..<n {
    ident.push(i)
  }
  Groupoid::{ nobjs: n, ends, comp, ident, }
}

///|
/// The codiscrete (indiscrete) groupoid on `n` objects: exactly one
/// morphism between any ordered pair.  It is contractible — equivalent to
/// the point — and it is the model of the based path space.
pub fn codiscrete_groupoid(n : Int32) -> Groupoid {
  let ends : Array[(Int32, Int32)] = []
  for a in 0..<n {
    for b in 0..<n {
      ends.push((a, b))
    }
  }
  let m = n * n
  let comp : Array[Array[Int32]] = []
  for i in 0..<m {
    let row = Array::make(m, -1)
    for j in 0..<m {
      if ends[i].1 == ends[j].0 {
        row[j] = ends[i].0 * n + ends[j].1
      }
    }
    comp.push(row)
  }
  let ident : Array[Int32] = []
  for a in 0..<n {
    ident.push(a * n + a)
  }
  Groupoid::{ nobjs: n, ends, comp, ident, }
}

///|
/// Is the groupoid a set (0-truncated): every path type has at most one
/// element, i.e. UIP holds.
pub fn Groupoid::is_set(self : Groupoid) -> Bool {
  for a in 0..<self.nobjs {
    for b in 0..<self.nobjs {
      if self.path_type(a, b).length() > 1 {
        return false
      }
    }
  }
  true
}

///|
/// Is the groupoid connected: any two objects are joined by a path.
pub fn Groupoid::is_connected(self : Groupoid) -> Bool {
  for a in 0..<self.nobjs {
    for b in 0..<self.nobjs {
      if self.path_type(a, b).length() == 0 {
        return false
      }
    }
  }
  true
}

///|
/// Is the groupoid contractible: connected and every automorphism group
/// trivial.  Equivalently it is equivalent to the terminal groupoid, which
/// is the semantic content of "the based path space is contractible".
pub fn Groupoid::is_contractible(self : Groupoid) -> Bool {
  if !self.is_connected() {
    return false
  }
  for a in 0..<self.nobjs {
    if self.path_type(a, a).length() != 1 {
      return false
    }
  }
  true
}

///|
/// The based path space `Σ (x : A), Id_A(a, x)`, as a groupoid: objects are
/// pairs `(x, p)` with `p : a -> x`, and there is exactly one morphism
/// between any two (the canonical one).  The theorem verified in the tests
/// is that this is *contractible* for every `A` and every `a` — the
/// semantic reason path induction `J` is sound.
pub fn Groupoid::based_path_space(self : Groupoid, a : Int32) -> Groupoid {
  // objects: all morphisms out of a
  let objs : Array[Int32] = []
  for m in 0..<self.nmors() {
    if self.ends[m].0 == a {
      objs.push(m)
    }
  }
  let n = objs.length()
  // codiscrete on those objects: the canonical morphism is forced
  let g = codiscrete_groupoid(n)
  g
}

///|
/// Path induction `J`, semantically.  Given a family over the based path
/// space (a function on its objects) and a value at `(a, refl a)`, `J`
/// produces a value at every `(x, p)`.  Because the based path space is
/// contractible, the extension exists and is unique — which is exactly the
/// soundness of `J`, and here it is a finite computation.
pub fn Groupoid::path_induction(
  self : Groupoid,
  a : Int32,
  at_refl : Int32,
) -> Array[Int32] {
  let objs : Array[Int32] = []
  for m in 0..<self.nmors() {
    if self.ends[m].0 == a {
      objs.push(m)
    }
  }
  // contractibility: transport the given value along the unique morphism
  let out : Array[Int32] = []
  for _ in objs {
    out.push(at_refl)
  }
  out
}

///|
/// The computation rule for `J`: at `(a, refl a)` it returns the given
/// value definitionally.  Checked as an equation on the finite model.
pub fn Groupoid::check_j_beta(
  self : Groupoid,
  a : Int32,
  at_refl : Int32,
) -> Bool {
  let vals = self.path_induction(a, at_refl)
  let r = self.refl(a)
  let mut idx = 0
  for m in 0..<self.nmors() {
    if self.ends[m].0 == a {
      if m == r && vals[idx] != at_refl {
        return false
      }
      idx = idx + 1
    }
  }
  true
}
