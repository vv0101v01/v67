///|
/// A tower of `n` nested Σ-types over `Fin 2`, with `Fin 2` at the bottom.
fn sigma_tower(n : Int32, leaf : Val) -> Val {
  let mut t = leaf
  for _i in 0..<n {
    // snapshot: capturing the mutable cell itself would make every level
    // point at the finished tower, i.e. a cyclic value
    let cur = t
    t = VSig(VFin(2), Clo::{ f: fn(_) { cur }, })
  }
  t
}

///|
test "unbounded: conversion separates values that differ only past depth 14" {
  // The old check printed both sides to depth 14 and compared strings, so
  // these two types were *equal* to it.  They are not equal.
  let a = sigma_tower(20, VFin(2))
  let b = sigma_tower(20, VFin(3))
  assert_false(val_conv(a, b))
  // and the truncated renderings really do still coincide, which is what
  // made the old check unsound rather than merely incomplete
  assert_eq(quote_norm(a, 14), quote_norm(b, 14))
  // identical towers are still equal, at any depth
  assert_true(val_conv(a, sigma_tower(20, VFin(2))))
  assert_true(val_conv(sigma_tower(60, VNat), sigma_tower(60, VNat)))
  assert_false(val_conv(sigma_tower(60, VNat), sigma_tower(59, VNat)))
}

///|
test "unbounded: function conversion probes under arbitrarily many binders" {
  // λx₀ … λx₁₉. x₀  versus  λx₀ … λx₁₉. x₁ : differ only at the leaf.
  fn tower(pick_first : Bool) -> Val {
    let mut body = if pick_first { VNe(0) } else { VNe(1) }
    for _i in 0..<20 {
      let b = body
      body = VLam(Clo::{ f: fn(_) { b }, })
    }
    body
  }
  assert_false(val_conv(tower(true), tower(false)))
  assert_true(val_conv(tower(true), tower(true)))
}

///|
test "unbounded: η is decided structurally, not by rendering" {
  let f = fin_fun([1, 0])
  // η-expansion of a non-lambda is convertible to it
  let eta = VLam(Clo::{ f: fn(x) { vapp(f, x) }, })
  assert_true(val_conv(f, eta))
  assert_true(val_conv(eta, f))
  // and a genuinely different function is not
  assert_false(val_conv(f, fin_fun([0, 1])))
}

///|
test "neutral-complete: a finite function is a case split, not its argument" {
  let neg = fin_fun([1, 0])
  let x = VNe(fresh_dim())
  let applied = vapp(neg, x)
  // the old table lookup returned `x` here, identifying neg with the
  // identity on every neutral.  It must be a stuck split instead.
  assert_false(val_conv(applied, x))
  match applied {
    VSplit(n, brs, sc) => {
      assert_eq(n, 2)
      assert_true(val_conv(sc, x))
      assert_true(val_conv(brs[0], VLit(1)))
      assert_true(val_conv(brs[1], VLit(0)))
    }
    _ => abort("expected a stuck split")
  }
  // neg ∘ neg is still not definitionally the identity on a neutral —
  // that needs Fin induction — but it *is* on every literal
  let twice = VLam(Clo::{ f: fn(z) { vapp(neg, vapp(neg, z)) }, })
  assert_false(val_conv(twice, VLam(Clo::{ f: fn(z) { z }, })))
  for k in 0..<2 {
    assert_true(val_conv(vapp(twice, VLit(k)), VLit(k)))
  }
}

///|
test "neutral-complete: splits survive composition in a function type" {
  // transport in `Fin 2 → Fin 2` along a ua path, applied to a neutral,
  // must still be a function that splits — the kernel never needs to
  // enumerate the 2^2 = 4 elements, let alone the 2^(10^6) of a Cantor type
  let neg = fin_fun([1, 0])
  let ty = VPi(VFin(2), Clo::{ f: fn(_) { VFin(2) }, })
  let conj = Equiv::new(
    ty,
    ty,
    VLam(Clo::{
      f: fn(g) { VLam(Clo::{ f: fn(x) { vapp(neg, vapp(g, x)) }, }) },
    }),
    VLam(Clo::{
      f: fn(g) { VLam(Clo::{ f: fn(x) { vapp(neg, vapp(g, x)) }, }) },
    }),
  )
  let h = transport(ua(conj), neg)
  let x = VNe(fresh_dim())
  // neg ∘ neg, transported: still computes on literals
  assert_true(val_conv(vapp(h, VLit(0)), VLit(0)))
  assert_true(val_conv(vapp(h, VLit(1)), VLit(1)))
  // and stays a split on a neutral
  match vapp(h, x) {
    VSplit(_, _, _) => ()
    _ => abort("expected a stuck split under the binder")
  }
}

///|
test "Nat: recursion computes, and is stuck exactly on neutrals" {
  // addition by recursion on the first argument
  let add = VLam(Clo::{
    f: fn(m) {
      VLam(Clo::{
        f: fn(n) { vnatiter(n, Clo::{ f: fn(rec) { VSuc(rec) }, }, m) },
      })
    },
  })
  let three = nat_lit(3)
  let four = nat_lit(4)
  assert_true(val_conv(vapp(vapp(add, three), four), nat_lit(7)))
  assert_true(val_conv(vapp(vapp(add, VZero), four), four))
  // on a neutral successor it still takes one step: add (suc m) n = suc (add m n)
  let m = VNe(fresh_dim())
  let stepped = vapp(vapp(add, VSuc(m)), four)
  match stepped {
    VSuc(inner) =>
      assert_true(
        val_conv(inner, vnatiter(four, Clo::{ f: fn(r) { VSuc(r) }, }, m)),
      )
    _ => abort("expected a successor")
  }
  // on a bare neutral it is stuck, and reads back as a recursor
  let stuck = vapp(vapp(add, m), four)
  match stuck {
    VNatRec(_, _, _) => ()
    _ => abort("expected a stuck recursor")
  }
}

///|
test "equivalences: with_contr installs a contraction that is checked" {
  // Build the same isomorphism twice: once with the closed-form
  // contraction, once by installing it explicitly.  They must agree as
  // equivalences (the contraction inhabits a proposition).
  let e = perm_equiv(3, [2, 0, 1])
  let explicit = Equiv::with_contr(
    e.src,
    e.tgt,
    e.fwd,
    e.bwd,
    e.alpha,
    e.beta,
    contr_iso(e.bwd),
  )
  assert_true(e == explicit)
  assert_false(explicit.strict.get())
  let pts = fin_points(3)
  assert_true(explicit.check(pts, pts))
  for a in pts {
    let t = vapp(e.bwd, a)
    assert_true(explicit.check_contr(a, t, refl(a)))
  }
}

///|
test "faces: the normal form is exposed and minimal" {
  // a conjunction is one face
  let f = @cubical.cof_faces(
    @cubical.CAnd(@cubical.face_cof(0, 1), @cubical.face_cof(1, 0)),
  )
  assert_eq(f.length(), 1)
  assert_eq(f[0].length(), 2)
  // a contradictory conjunction has no faces at all
  assert_eq(
    @cubical.cof_faces(
      @cubical.CAnd(@cubical.face_cof(0, 0), @cubical.face_cof(0, 1)),
    ).length(),
    0,
  )
  // (i ∧ j = 0) is two faces, and absorption removes the redundant one
  let g = @cubical.cof_faces(
    @cubical.COr(
      @cubical.CEq(@cubical.DAnd(@cubical.DVar(0), @cubical.DVar(1)), 0),
      @cubical.face_cof(0, 0),
    ),
  )
  assert_eq(g.length(), 2)
}
