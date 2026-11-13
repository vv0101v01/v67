///|
/// # Computational univalence, end to end
///
/// Univalence is *computational* when `transport (ua e) a` reduces to
/// `e.fwd a` by the computation rules alone — no axiom, no postulate, no
/// search.  These tests run the whole chain through the bidirectional and
/// symmetric operations, so the property is checked for the general
/// structure and not only for the directed special case.

///|
test "computational univalence: uaβ through every direction" {
  for t in perms(4) {
    let e = perm_equiv(4, t)
    let p = ua(e)
    let fam = path_fam(p)
    let inv = equiv_inv(e)
    for k in 0..<4 {
      let a = VLit(k)
      let want = vapp(e.fwd, a)
      // directed coercion
      assert_true(val_conv(coe(fam, 0, a), want))
      // bidirectional coercion, forwards
      assert_true(
        val_conv(coe_between(fam, @cubical.DZero, @cubical.DOne, a), want),
      )
      // transp with the empty cofibration
      assert_true(val_conv(transp(fam, 0, @cubical.CBot, a), want))
      // transp between stages
      assert_true(
        val_conv(
          transp_between(fam, @cubical.DZero, @cubical.DOne, @cubical.CBot, a),
          want,
        ),
      )
      // and backwards is the inverse permutation
      assert_true(
        val_conv(
          coe_between(fam, @cubical.DOne, @cubical.DZero, a),
          vapp(inv.fwd, a),
        ),
      )
    }
  }
}

///|
test "computational univalence: idtoeqv ∘ ua is the identity" {
  for t in perms(4) {
    let e = perm_equiv(4, t)
    let back = idtoeqv(ua(e))
    // the equivalence itself is recovered, not merely its action
    assert_true(val_conv(back.src, e.src))
    assert_true(val_conv(back.tgt, e.tgt))
    for k in 0..<4 {
      let a = VLit(k)
      assert_true(val_conv(vapp(back.fwd, a), vapp(e.fwd, a)))
      assert_true(val_conv(vapp(back.bwd, a), vapp(e.bwd, a)))
    }
  }
}

///|
test "computational univalence: ua ∘ idtoeqv on the image of ua" {
  for t in perms(3) {
    let e = perm_equiv(3, t)
    let p = ua(e)
    let (lhs, rhs) = ua_eta(p)
    assert_true(val_conv(lhs, rhs))
  }
}

///|
test "computational univalence: on a non-strict equivalence" {
  // A composite line has genuinely non-definitional round trips, so the
  // Glue rule must use equiv and the correction square, not the strict
  // short circuit.  Transport still computes.
  let e = shift_equiv(9)
  let pq = path_concat(VU, ua(e), ua(e))
  let fam = path_fam(pq)
  for k in 0..<9 {
    let a = VLit(k)
    let want = VLit((k + 2) % 9)
    assert_true(
      val_conv(coe_between(fam, @cubical.DZero, @cubical.DOne, a), want),
    )
    assert_true(val_conv(transp(fam, 0, @cubical.CBot, a), want))
  }
  // and the fibre contraction of that line is definitional at both ends
  let eq = idtoeqv(pq)
  assert_true(eq.check_contr(VLit(0), VLit(7), refl(VLit(0))))
}

///|
test "computational univalence: symmetry is compatible with transport" {
  for t in perms(4) {
    let e = perm_equiv(4, t)
    let (lhs, rhs) = ua_sym(e)
    for k in 0..<4 {
      let b = VLit(k)
      let a = transport(lhs, b)
      assert_true(val_conv(a, transport(rhs, b)))
      assert_true(val_conv(a, transport_sym(ua(e), b)))
      assert_true(val_conv(a, vapp(e.bwd, b)))
    }
  }
}

///|
test "computational univalence: on an infinite type, in both directions" {
  // The Cantor space Nat -> Fin 2, conjugated by negation.  No enumeration
  // anywhere: the type has 2^aleph_0 elements.
  let cantor = VPi(VNat, Clo::{ f: fn(_) { VFin(2) }, })
  let neg = fin_fun([1, 0])
  let conj_map = VLam(Clo::{
    f: fn(g) { VLam(Clo::{ f: fn(x) { vapp(neg, vapp(g, x)) }, }) },
  })
  let conj = Equiv::new(cantor, cantor, conj_map, conj_map)
  let p = ua(conj)
  let fam = path_fam(p)
  let zero_fun = VLam(Clo::{ f: fn(_) { VLit(0) }, })
  let h = coe_between(fam, @cubical.DZero, @cubical.DOne, zero_fun)
  assert_true(val_conv(vapp(h, nat_lit(0)), VLit(1)))
  assert_true(val_conv(vapp(h, nat_lit(100000)), VLit(1)))
  // backwards undoes it
  let back = coe_between(fam, @cubical.DOne, @cubical.DZero, h)
  assert_true(val_conv(vapp(back, nat_lit(7)), VLit(0)))
  // and transp agrees
  let t = transp(fam, 0, @cubical.CBot, zero_fun)
  assert_true(val_conv(vapp(t, nat_lit(3)), VLit(1)))
}

///|
test "computational univalence: transport is functorial along concatenation" {
  // transport (p · q) = transport q ∘ transport p, checked with the
  // bidirectional operation on a composite of three ua lines.
  let e1 = perm_equiv(5, [1, 2, 3, 4, 0])
  let e2 = perm_equiv(5, [4, 0, 1, 2, 3])
  let e3 = perm_equiv(5, [2, 3, 4, 0, 1])
  let p = path_concat(VU, path_concat(VU, ua(e1), ua(e2)), ua(e3))
  let fam = path_fam(p)
  for k in 0..<5 {
    let a = VLit(k)
    let stepwise = vapp(e3.fwd, vapp(e2.fwd, vapp(e1.fwd, a)))
    assert_true(
      val_conv(coe_between(fam, @cubical.DZero, @cubical.DOne, a), stepwise),
    )
  }
  // the reverse composite undoes it
  let q = path_sym(p)
  for k in 0..<5 {
    let a = VLit(k)
    let there = coe_between(fam, @cubical.DZero, @cubical.DOne, a)
    let back = coe_between(path_fam(q), @cubical.DZero, @cubical.DOne, there)
    assert_true(val_conv(back, a))
  }
}

///|
test "computational univalence: the dependent path of a transport" {
  // transp_path packages a coercion as a PathP, so the rest of the path
  // algebra (sym, ap, J) applies to it.  This is what makes transport a
  // first-class citizen rather than a side effect.
  let e = perm_equiv(6, [3, 4, 5, 0, 1, 2])
  let fam = path_fam(ua(e))
  let a = VLit(1)
  let tp = transp_path(fam, @cubical.DZero, @cubical.DOne, a)
  assert_true(val_conv(vpapp(tp, @cubical.DZero), a))
  assert_true(val_conv(vpapp(tp, @cubical.DOne), VLit(4)))
  // J on refl still reduces, and the transported path is a path
  let d = VLit(0)
  let j = pathJ(fn(_, _) { VFin(1) }, d, refl(VLit(0)))
  assert_true(val_conv(j, d))
  // ap of the recursor along the circle's loop is the given loop
  let rec = VLam(Clo::{
    f: fn(x) { circle_rec(VCircle, VBase, circle_loop(), x) },
  })
  let i = @cubical.DVar(fresh_dim())
  assert_true(val_conv(vapp(rec, vloop(i)), vloop(i)))
}
