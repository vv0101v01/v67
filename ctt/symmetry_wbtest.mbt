///|
test "symmetry: reversal is an involution on dimensions and cofibrations" {
  let i = @cubical.DVar(fresh_dim())
  let j = @cubical.DVar(fresh_dim())
  // ~~r = r, including on compound terms
  for
    r in [
      i,
      dim_not(i),
      dim_and(i, j),
      @cubical.dim_or(i, dim_not(j)),
      dim_not(dim_and(i, dim_not(j))),
    ] {
    assert_true(@cubical.dim_eq(dim_not(dim_not(r)), r))
  }
  // De Morgan
  assert_true(
    @cubical.dim_eq(
      dim_not(dim_and(i, j)),
      @cubical.dim_or(dim_not(i), dim_not(j)),
    ),
  )
  assert_true(
    @cubical.dim_eq(
      dim_not(@cubical.dim_or(i, j)),
      dim_and(dim_not(i), dim_not(j)),
    ),
  )
  // the cofibration relabelling is a lattice automorphism
  let phi = @cubical.COr(
    @cubical.CAnd(@cubical.CEq(i, 0), @cubical.CEq(j, 1)),
    @cubical.CEq(i, 1),
  )
  assert_true(@cubical.cof_same(cof_rev(cof_rev(phi)), phi))
  assert_true(@cubical.cof_same(cof_rev(@cubical.CTop), @cubical.CTop))
  assert_true(@cubical.cof_same(cof_rev(@cubical.CBot), @cubical.CBot))
  // and it preserves entailment, which is what "automorphism" means.
  // The boundary of i contains both disjuncts of phi; the single face
  // (i=1) does not, since (i=0 ∧ j=1) is below phi but not below it.
  let boundary = @cubical.COr(@cubical.CEq(i, 0), @cubical.CEq(i, 1))
  assert_true(@cubical.cof_leq(phi, boundary))
  assert_true(@cubical.cof_leq(cof_rev(phi), cof_rev(boundary)))
  assert_false(@cubical.cof_leq(phi, @cubical.CEq(i, 1)))
  // the boundary is a fixed point of the relabelling
  assert_true(@cubical.cof_same(cof_rev(boundary), boundary))
}

///|
test "symmetry: the two derivations of reversed composition agree" {
  // comp^{1→0} (reindex along ~i) versus comp of the reversed family with
  // reversed walls.  Their agreement is equivariance of the Kan structure
  // for the involution — the content of "internally symmetric".
  for t in perms(4) {
    let e = perm_equiv(4, t)
    let fam = path_fam(ua(e))
    let j = fresh_dim()
    let tube = Tube::empty().add(@cubical.CEq(@cubical.DVar(j), 0), DClo::{
      f: fn(_) { VLit(1) },
    })
    for k in 0..<4 {
      let cap = VLit(k)
      let by_between = comp_rev(fam, tube, cap)
      let by_sym = comp_sym(fam, tube, cap)
      assert_true(val_conv(by_between, by_sym))
    }
  }
}

///|
test "symmetry: reversed composition is the backward coercion" {
  let e = perm_equiv(5, [2, 3, 4, 0, 1])
  let fam = path_fam(ua(e))
  for k in 0..<5 {
    let a = VLit(k)
    assert_true(val_conv(comp_rev(fam, Tube::empty(), a), coe_back(fam, 0, a)))
    assert_true(val_conv(comp_sym(fam, Tube::empty(), a), coe_back(fam, 0, a)))
    assert_true(val_conv(comp_rev(fam, Tube::empty(), a), VLit((k + 3) % 5)))
  }
}

///|
test "symmetry: reversing a family twice is the family" {
  let e = perm_equiv(4, [1, 2, 3, 0])
  let fam = path_fam(ua(e))
  let rr = fam.rev().rev()
  for r in [@cubical.DZero, @cubical.DOne, @cubical.DVar(fresh_dim())] {
    assert_true(val_conv(fam.at(r), rr.at(r)))
  }
  // and reversing a tube twice is the tube
  let j = fresh_dim()
  let tube = Tube::empty().add(@cubical.CEq(@cubical.DVar(j), 0), DClo::{
    f: fn(r) { VLit(if r == @cubical.DOne { 2 } else { 0 }) },
  })
  let tt = tube.rev().rev()
  assert_eq(tt.branches.length(), tube.branches.length())
  for b in 0..<tube.branches.length() {
    assert_true(@cubical.cof_same(tt.branches[b].cof, tube.branches[b].cof))
    for r in [@cubical.DZero, @cubical.DOne] {
      assert_true(val_conv(tt.branches[b].tm.at(r), tube.branches[b].tm.at(r)))
    }
  }
}

///|
test "symmetry: path reversal is a strict involution" {
  let e = perm_equiv(3, [1, 2, 0])
  let p = ua(e)
  let pp = path_sym(path_sym(p))
  // definitional, because ~~i folds to i
  for r in [@cubical.DZero, @cubical.DOne, @cubical.DVar(fresh_dim())] {
    assert_true(val_conv(vpapp(p, r), vpapp(pp, r)))
  }
  // as an equivalence, sym is its own inverse
  let a = VFin(3)
  let x = VLit(0)
  let y = VLit(1)
  let se = sym_equiv(a, x, y)
  let inv = equiv_inv(se)
  assert_true(val_conv(se.fwd, inv.fwd))
  assert_true(val_conv(se.src, inv.tgt))
  assert_true(val_conv(se.tgt, inv.src))
  // and it really reverses a path
  let q = refl(VLit(0))
  let sq = vapp(se.fwd, q)
  assert_true(val_conv(vpapp(sq, @cubical.DZero), vpapp(q, @cubical.DOne)))
  assert_true(val_conv(vpapp(sq, @cubical.DOne), vpapp(q, @cubical.DZero)))
}

///|
test "symmetry: equivalences form an involutive groupoid" {
  for t in perms(4) {
    let e = perm_equiv(4, t)
    let ee = equiv_inv(equiv_inv(e))
    assert_true(val_conv(e.fwd, ee.fwd))
    assert_true(val_conv(e.bwd, ee.bwd))
    assert_true(val_conv(e.src, ee.src))
    assert_true(val_conv(e.tgt, ee.tgt))
  }
}

///|
test "symmetry of univalence: ua(e⁻¹) and sym(ua e) transport alike" {
  // The two Glue lines are built from different data — different base,
  // different branch equivalence — so this is a theorem, not a folding.
  for t in perms(4) {
    let e = perm_equiv(4, t)
    let (lhs, rhs) = ua_sym(e)
    // same endpoints
    assert_true(
      val_conv(vpapp(lhs, @cubical.DZero), vpapp(rhs, @cubical.DZero)),
    )
    assert_true(val_conv(vpapp(lhs, @cubical.DOne), vpapp(rhs, @cubical.DOne)))
    assert_true(val_conv(vpapp(lhs, @cubical.DZero), VFin(4)))
    assert_true(val_conv(vpapp(lhs, @cubical.DOne), VFin(4)))
    // same transport, on every point
    for k in 0..<4 {
      let b = VLit(k)
      assert_true(val_conv(transport(lhs, b), transport(rhs, b)))
    }
    // they are NOT definitionally the same line: the branch data differs
    let mid = @cubical.DVar(fresh_dim())
    assert_false(val_conv(vpapp(lhs, mid), vpapp(rhs, mid)))
  }
}

///|
test "symmetry: transport along a reversed path is backward coercion" {
  let e = perm_equiv(6, [1, 2, 3, 4, 5, 0])
  let p = ua(e)
  for k in 0..<6 {
    let b = VLit(k)
    let via_sym = transport(path_sym(p), b)
    let via_rev = transport_sym(p, b)
    let via_bwd = coe_back(path_fam(p), 0, b)
    assert_true(val_conv(via_sym, via_rev))
    assert_true(val_conv(via_rev, via_bwd))
    assert_true(val_conv(via_bwd, VLit((k + 5) % 6)))
  }
}

///|
test "symmetry: reversed filling agrees with filling the reversed family" {
  let e = perm_equiv(4, [3, 0, 1, 2])
  let fam = path_fam(ua(e))
  let a = VLit(2)
  let f1 = fill_rev(fam, Tube::empty(), a)
  let f2 = fill(fam.rev(), fresh_dim(), Tube::empty(), a)
  for r in [@cubical.DZero, @cubical.DOne] {
    assert_true(val_conv(f1.at(r), f2.at(r)))
  }
  assert_true(val_conv(f1.at(@cubical.DZero), a))
  assert_true(val_conv(f1.at(@cubical.DOne), VLit(3)))
}

///|
test "symmetry meets univalence: the round trip along ua and its reverse" {
  // ua(e) · sym(ua(e)) transports as the identity — symmetry composed
  // with the bidirectional structure, on every permutation of Fin 4.
  for t in perms(4) {
    let e = perm_equiv(4, t)
    let p = ua(e)
    let roundtrip = path_concat(VU, p, path_sym(p))
    for k in 0..<4 {
      assert_true(val_conv(transport(roundtrip, VLit(k)), VLit(k)))
    }
    // and the other order
    let roundtrip2 = path_concat(VU, path_sym(p), p)
    for k in 0..<4 {
      assert_true(val_conv(transport(roundtrip2, VLit(k)), VLit(k)))
    }
  }
}
