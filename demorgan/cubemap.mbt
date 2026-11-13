///|
/// A morphism of cubes `I^src -> I^dst` in the cubical category *with
/// connections and reversals*: each target coordinate is given by a
/// dimension term in the source coordinates.  Composition is substitution,
/// so the cubical identities become equalities in the free De Morgan
/// algebra and are therefore decidable.
#derive(Debug, Eq)
pub struct CubeMap {
  src : Int32
  dst : Int32
  coords : Array[Dim]
}

///|
pub fn cube_map(src : Int32, dst : Int32, coords : Array[Dim]) -> CubeMap {
  CubeMap::{ src, dst, coords, }
}

///|
pub fn cube_id(n : Int32) -> CubeMap {
  let cs : Array[Dim] = []
  for i in 0..<n {
    cs.push(@cubical.DVar(i))
  }
  CubeMap::{ src: n, dst: n, coords: cs, }
}

///|
/// Substitute `f`'s coordinates into `g`: the composite `g ∘ f`.
pub fn cube_then(f : CubeMap, g : CubeMap) -> CubeMap {
  let cs : Array[Dim] = []
  for c in g.coords {
    cs.push(dim_subst_all(c, f.coords))
  }
  CubeMap::{ src: f.src, dst: g.dst, coords: cs, }
}

///|
/// Simultaneous substitution of dimension terms for variables.
pub fn dim_subst_all(r : Dim, args : Array[Dim]) -> Dim {
  match r {
    @cubical.DZero => @cubical.DZero
    @cubical.DOne => @cubical.DOne
    @cubical.DVar(i) =>
      if i >= 0 && i < args.length() {
        args[i]
      } else {
        @cubical.DVar(i)
      }
    @cubical.DNot(x) => @cubical.DNot(dim_subst_all(x, args))
    @cubical.DAnd(a, b) =>
      @cubical.DAnd(dim_subst_all(a, args), dim_subst_all(b, args))
    @cubical.DOr(a, b) =>
      @cubical.DOr(dim_subst_all(a, args), dim_subst_all(b, args))
  }
}

///|
pub fn cube_map_eq(a : CubeMap, b : CubeMap) -> Bool {
  if a.src != b.src || a.dst != b.dst {
    return false
  }
  for i in 0..<a.coords.length() {
    if !dim_eq(a.coords[i], b.coords[i]) {
      return false
    }
  }
  true
}

///|
/// Face map `δ_i^ε : I^n -> I^{n+1}`, inserting the constant `ε` in slot `i`.
pub fn cube_face(n : Int32, i : Int32, eps : Int32) -> CubeMap {
  let cs : Array[Dim] = []
  for k in 0..<(n + 1) {
    if k < i {
      cs.push(@cubical.DVar(k))
    } else if k == i {
      cs.push(if eps == 0 { @cubical.DZero } else { @cubical.DOne })
    } else {
      cs.push(@cubical.DVar(k - 1))
    }
  }
  CubeMap::{ src: n, dst: n + 1, coords: cs, }
}

///|
/// Degeneracy `σ_i : I^{n+1} -> I^n`, forgetting coordinate `i`.
pub fn cube_degen(n : Int32, i : Int32) -> CubeMap {
  let cs : Array[Dim] = []
  for k in 0..<(n + 1) {
    if k != i {
      cs.push(@cubical.DVar(k))
    }
  }
  CubeMap::{ src: n + 1, dst: n, coords: cs, }
}

///|
/// Connection `γ_i^ε : I^{n+1} -> I^n`, merging coordinates `i, i+1` with
/// meet (`ε = 0`) or join (`ε = 1`).  Connections are exactly what the
/// De Morgan structure buys over a plain face lattice: they make the
/// cubical nerve of a groupoid Kan, and they give path composition a
/// strictly unital definition.
pub fn cube_conn(n : Int32, i : Int32, eps : Int32) -> CubeMap {
  let cs : Array[Dim] = []
  for k in 0..<n {
    if k < i {
      cs.push(@cubical.DVar(k))
    } else if k == i {
      let a = @cubical.DVar(i)
      let b = @cubical.DVar(i + 1)
      cs.push(if eps == 0 { @cubical.DAnd(a, b) } else { @cubical.DOr(a, b) })
    } else {
      cs.push(@cubical.DVar(k + 1))
    }
  }
  CubeMap::{ src: n + 1, dst: n, coords: cs, }
}

///|
/// Reversal `r_i : I^n -> I^n`, the De Morgan involution in coordinate `i`.
pub fn cube_rev(n : Int32, i : Int32) -> CubeMap {
  let cs : Array[Dim] = []
  for k in 0..<n {
    cs.push(
      if k == i {
        @cubical.DNot(@cubical.DVar(k))
      } else {
        @cubical.DVar(k)
      },
    )
  }
  CubeMap::{ src: n, dst: n, coords: cs, }
}

///|
/// Symmetry exchanging coordinates `i, i+1`.
pub fn cube_swap(n : Int32, i : Int32) -> CubeMap {
  let cs : Array[Dim] = []
  for k in 0..<n {
    if k == i {
      cs.push(@cubical.DVar(i + 1))
    } else if k == i + 1 {
      cs.push(@cubical.DVar(i))
    } else {
      cs.push(@cubical.DVar(k))
    }
  }
  CubeMap::{ src: n, dst: n, coords: cs, }
}

///|
/// Diagonal `Δ_i : I^n -> I^{n+1}`, duplicating coordinate `i`.
pub fn cube_dup(n : Int32, i : Int32) -> CubeMap {
  let cs : Array[Dim] = []
  for k in 0..<(n + 1) {
    if k <= i {
      cs.push(@cubical.DVar(k))
    } else {
      cs.push(@cubical.DVar(k - 1))
    }
  }
  CubeMap::{ src: n, dst: n + 1, coords: cs, }
}

///|
/// The endomorphism of `I^n` pinning coordinate `i` to `ε`.
pub fn cube_pin(n : Int32, i : Int32, eps : Int32) -> CubeMap {
  cube_then(cube_degen(n - 1, i), cube_face(n - 1, i, eps))
}

///|
/// Evaluate a cube map on a `{0,1,2}` point (2 = free direction).
pub fn CubeMap::apply(self : CubeMap, point : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for c in self.coords {
    out.push(c.eval3(point))
  }
  out
}

///|
/// Exhaustive semantic equality on all `3^src` subcube points.  This is an
/// independent check of the syntactic `dim_eq` decision procedure: for the
/// free De Morgan algebra the two agree (both are complete for the
/// three-valued semantics restricted to subcube points).
pub fn cube_map_pointwise_eq(a : CubeMap, b : CubeMap) -> Bool {
  if a.src != b.src || a.dst != b.dst {
    return false
  }
  let total = pow3(a.src)
  for code in 0..<total {
    let pt = subcube_digits(code, a.src)
    let xs = a.apply(pt)
    let ys = b.apply(pt)
    for k in 0..<xs.length() {
      if xs[k] != ys[k] {
        return false
      }
    }
  }
  true
}

///|
/// A cube map is well formed when every coordinate term only mentions
/// source variables.  Composition of ill-typed maps is rejected by this
/// check rather than silently producing out-of-range variables.
pub fn CubeMap::well_formed(self : CubeMap) -> Bool {
  fn maxvar(r : Dim) -> Int32 {
    match r {
      @cubical.DZero => -1
      @cubical.DOne => -1
      @cubical.DVar(i) => i
      @cubical.DNot(x) => maxvar(x)
      @cubical.DAnd(a, b) => {
        let x = maxvar(a)
        let y = maxvar(b)
        if x > y {
          x
        } else {
          y
        }
      }
      @cubical.DOr(a, b) => {
        let x = maxvar(a)
        let y = maxvar(b)
        if x > y {
          x
        } else {
          y
        }
      }
    }
  }

  if self.coords.length() != self.dst {
    return false
  }
  for c in self.coords {
    if maxvar(c) >= self.src {
      return false
    }
  }
  true
}
