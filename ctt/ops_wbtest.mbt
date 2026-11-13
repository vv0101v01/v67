///|
test "bidirectional: the interpolation line has the right endpoints" {
  let r = @cubical.DVar(fresh_dim())
  let s = @cubical.DVar(fresh_dim())
  let i = @cubical.DVar(fresh_dim())
  assert_true(@cubical.dim_eq(interp(r, s, @cubical.DZero), r))
  assert_true(@cubical.dim_eq(interp(r, s, @cubical.DOne), s))
  // the two directed specialisations fold on the nose
  assert_true(@cubical.dim_eq(interp(@cubical.DZero, @cubical.DOne, i), i))
  assert_true(
    @cubical.dim_eq(interp(@cubical.DOne, @cubical.DZero, i), dim_not(i)),
  )
  // and the De Morgan interval does NOT collapse the diagonal
  assert_false(@cubical.dim_eq(interp(r, r, i), r))
}

///|
test "bidirectional: coe between stages generalises coe and coe_back" {
  let e = perm_equiv(5, [1, 2, 3, 4, 0])
  let fam = path_fam(ua(e))
  for k in 0..<5 {
    let a = VLit(k)
    let fwd = coe_between(fam, @cubical.DZero, @cubical.DOne, a)
    assert_true(val_conv(fwd, coe(fam, 0, a)))
    assert_true(val_conv(fwd, VLit((k + 1) % 5)))
    let bwd = coe_between(fam, @cubical.DOne, @cubical.DZero, a)
    assert_true(val_conv(bwd, coe_back(fam, 0, a)))
    assert_true(val_conv(bwd, VLit((k + 4) % 5)))
  }
}

///|
test "bidirectional: regularity on the diagonal is strict" {
  let e = perm_equiv(4, [3, 0, 1, 2])
  let fam = path_fam(ua(e))
  // equal endpoints: the identity, definitionally, at every stage
  for r in [@cubical.DZero, @cubical.DOne, @cubical.DVar(fresh_dim())] {
    for k in 0..<4 {
      assert_true(val_conv(coe_between(fam, r, r, VLit(k)), VLit(k)))
    }
  }
  // and for a compound stage, where dim_eq has to normalise first
  let j = @cubical.DVar(fresh_dim())
  assert_true(
    val_conv(coe_between(fam, dim_not(j), dim_not(j), VLit(2)), VLit(2)),
  )
  assert_true(
    val_conv(coe_between(fam, dim_not(dim_not(j)), j, VLit(2)), VLit(2)),
  )
}

///|
test "bidirectional: coercion between interior stages computes" {
  // A ua line is a Glue: at an interior stage it is genuinely glued, and
  // coercing from one interior stage to another must still work.
  let e = perm_equiv(4, [1, 2, 3, 0])
  let fam = path_fam(ua(e))
  let j = @cubical.DVar(fresh_dim())
  // from 0 to ~j, then ~j to 1, agrees with 0 to 1 on every point
  for k in 0..<4 {
    let a = VLit(k)
    let mid = coe_between(fam, @cubical.DZero, dim_not(j), a)
    let end = coe_between(fam, dim_not(j), @cubical.DOne, mid)
    let direct = coe_between(fam, @cubical.DZero, @cubical.DOne, a)
    assert_true(val_conv(end, direct))
  }
}

///|
test "bidirectional: a round trip returns the point" {
  for t in perms(4) {
    let e = perm_equiv(4, t)
    let fam = path_fam(ua(e))
    for k in 0..<4 {
      let a = VLit(k)
      let there = coe_between(fam, @cubical.DZero, @cubical.DOne, a)
      let back = coe_between(fam, @cubical.DOne, @cubical.DZero, there)
      assert_true(val_conv(back, a))
    }
  }
}

///|
test "transp: the cofibration side condition is a wall" {
  let e = perm_equiv(4, [1, 2, 3, 0])
  let fam = path_fam(ua(e))
  let a = VLit(2)
  // phi = top: the tube is total, so transport does nothing at all
  assert_true(val_conv(transp(fam, 0, @cubical.CTop, a), a))
  // phi = bot: transport is coercion
  assert_true(val_conv(transp(fam, 0, @cubical.CBot, a), coe(fam, 0, a)))
  assert_true(val_conv(transp(fam, 0, @cubical.CBot, a), VLit(3)))
  // A genuine face is only allowed where the *family* is constant on it:
  // the wall `a` must inhabit A(i) for every i on φ.  A ua line is not
  // constant on any nonempty face, so `transp` along it with φ = (j=0)
  // would be ill typed — the side condition is real, not decorative.
  let j = fresh_dim()
  let phi = @cubical.CEq(@cubical.DVar(j), 0)
  let flat = fam_const(VFin(4))
  assert_true(val_conv(transp(flat, 0, phi, a), a))
}

///|
test "transp: regularity for a constant line, at any cofibration" {
  let fam = fam_const(VFin(7))
  for
    phi in [
      @cubical.CTop,
      @cubical.CBot,
      @cubical.CEq(@cubical.DVar(fresh_dim()), 1),
    ] {
    assert_true(val_conv(transp(fam, 0, phi, VLit(5)), VLit(5)))
  }
  // and between arbitrary stages
  let j = @cubical.DVar(fresh_dim())
  assert_true(
    val_conv(
      transp_between(fam, j, dim_not(j), @cubical.CTop, VLit(5)),
      VLit(5),
    ),
  )
}

///|
test "filling: the filler has the cap, the lid and the walls" {
  let e = perm_equiv(4, [2, 3, 0, 1])
  let fam = path_fam(ua(e))
  let a = VLit(1)
  let f = fill_between(fam, @cubical.DZero, @cubical.DOne, Tube::empty(), a)
  assert_true(val_conv(f.at(@cubical.DZero), a))
  assert_true(
    val_conv(
      f.at(@cubical.DOne),
      coe_between(fam, @cubical.DZero, @cubical.DOne, a),
    ),
  )
  // reversed filling swaps the roles of the ends
  let g = fill_between(fam, @cubical.DOne, @cubical.DZero, Tube::empty(), a)
  assert_true(val_conv(g.at(@cubical.DZero), a))
  assert_true(
    val_conv(
      g.at(@cubical.DOne),
      coe_between(fam, @cubical.DOne, @cubical.DZero, a),
    ),
  )
}

///|
test "transport as a dependent path: endpoints and ap" {
  let e = perm_equiv(6, [1, 2, 3, 4, 5, 0])
  let fam = path_fam(ua(e))
  let a = VLit(4)
  let p = transp_path(fam, @cubical.DZero, @cubical.DOne, a)
  assert_true(val_conv(vpapp(p, @cubical.DZero), a))
  assert_true(val_conv(vpapp(p, @cubical.DOne), VLit(5)))
  // it is a path, so path_sym applies and reverses it
  let q = path_sym(p)
  assert_true(val_conv(vpapp(q, @cubical.DZero), VLit(5)))
  assert_true(val_conv(vpapp(q, @cubical.DOne), a))
}

///|
test "heterogeneous versus homogeneous composition" {
  // With a constant family the heterogeneous operation must agree with
  // the homogeneous one, and both with the directed kernel.
  let j = fresh_dim()
  let tube = Tube::empty().add(@cubical.CEq(@cubical.DVar(j), 0), DClo::{
    f: fn(r) { VLit(if r == @cubical.DOne { 2 } else { 0 }) },
  })
  let h1 = hcomp_const(VFin(3), tube, VLit(0))
  let h2 = comp_between(
    fam_const(VFin(3)),
    @cubical.DZero,
    @cubical.DOne,
    tube,
    VLit(0),
  )
  let h3 = comp(fam_const(VFin(3)), 0, tube, VLit(0))
  assert_true(val_conv(h1, h2))
  assert_true(val_conv(h2, h3))
  // A wall on a proper face forces the lid only *on that face*; off it the
  // lid is not determined, and the kernel is free to return the cap.  With
  // a total tube the lid is forced everywhere.
  let total = Tube::empty().add(@cubical.CTop, DClo::{
    f: fn(r) { VLit(if r == @cubical.DOne { 2 } else { 0 }) },
  })
  assert_true(val_conv(hcomp_const(VFin(3), total, VLit(0)), VLit(2)))
  // filling agrees too
  let f1 = hfill_const(VFin(3), tube, VLit(0))
  assert_true(val_conv(f1.at(@cubical.DZero), VLit(0)))
  assert_true(val_conv(f1.at(@cubical.DOne), h1))
}

///|
test "heterogeneous composition genuinely moves the type" {
  // Along a ua line the walls live in different types at the two ends;
  // this is what "heterogeneous" buys, and a homogeneous operation cannot
  // express it.
  let e = perm_equiv(5, [4, 0, 1, 2, 3])
  let fam = path_fam(ua(e))
  let j = fresh_dim()
  let tube = Tube::empty().add(@cubical.CEq(@cubical.DVar(j), 0), DClo::{
    f: fn(_) { VLit(1) },
  })
  let lid = comp_between(fam, @cubical.DZero, @cubical.DOne, tube, VLit(1))
  assert_true(val_conv(lid, VLit(0)))
  // reversed, it goes back
  let back = comp_between(fam, @cubical.DOne, @cubical.DZero, tube, VLit(0))
  assert_true(val_conv(back, VLit(1)))
}
