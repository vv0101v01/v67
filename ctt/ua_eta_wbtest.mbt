///|
test "uaη: the base case is a Glue square with identical branch data" {
  let a = VFin(3)
  let d = ua_eta_base(a)
  // at j=0 the extra face is empty, leaving ua of the identity
  assert_true(val_conv(vpapp(d, @cubical.DZero), ua(equiv_id(a))))
  assert_true(val_conv(vpapp(d, @cubical.DZero), ua(idtoeqv(refl(a)))))
  // at j=1 that face is total, so the Glue collapses and the line is refl
  assert_true(val_conv(vpapp(d, @cubical.DOne), refl(a)))
  // both ends of every line in the square are A, as a loop must be
  let j = @cubical.DVar(fresh_dim())
  let line = vpapp(d, j)
  assert_true(val_conv(vpapp(line, @cubical.DZero), a))
  assert_true(val_conv(vpapp(line, @cubical.DOne), a))
  // and this is NOT Glue regularity: ua(id) is not refl
  assert_false(val_conv(ua(equiv_id(a)), refl(a)))
}

///|
test "uaη: refl is outside the image of ua, and the witness still works" {
  // For p = refl A the two ends of the witness are genuinely different
  // types-as-lines, so this is the case the definitional uaη never covered.
  let a = VFin(4)
  let p = refl(a)
  let lhs = ua(idtoeqv(p))
  assert_false(val_conv(lhs, p))
  let w = ua_eta_general(p)
  // endpoints hold definitionally: composition in a path type puts them in
  // the tube, and a total tube returns the wall
  assert_true(val_conv(vpapp(w, @cubical.DZero), lhs))
  assert_true(val_conv(vpapp(w, @cubical.DOne), p))
  // the witness is a path of lines, so every line in it runs from A to A
  let j = @cubical.DVar(fresh_dim())
  let mid = vpapp(w, j)
  assert_true(val_conv(vpapp(mid, @cubical.DZero), a))
  assert_true(val_conv(vpapp(mid, @cubical.DOne), a))
}

///|
test "uaη: on a composite line, which is not a ua image" {
  let e = shift_equiv(5)
  let pq = path_concat(VU, ua(e), ua(e))
  let lhs = ua(idtoeqv(pq))
  // a composite of two ua lines is not itself syntactically a ua line
  assert_false(val_conv(lhs, pq))
  let w = ua_eta_general(pq)
  assert_true(val_conv(vpapp(w, @cubical.DZero), lhs))
  assert_true(val_conv(vpapp(w, @cubical.DOne), pq))
  // every line in the witness has the right endpoints as types
  let j = @cubical.DVar(fresh_dim())
  let mid = vpapp(w, j)
  assert_true(val_conv(vpapp(mid, @cubical.DZero), VFin(5)))
  assert_true(val_conv(vpapp(mid, @cubical.DOne), VFin(5)))
}

///|
test "uaη: on a reversed line" {
  let e = perm_equiv(4, [1, 2, 3, 0])
  let p = path_sym(ua(e))
  let w = ua_eta_general(p)
  assert_true(val_conv(vpapp(w, @cubical.DZero), ua(idtoeqv(p))))
  assert_true(val_conv(vpapp(w, @cubical.DOne), p))
  // and the ends of the witness are lines from B back to A
  let j = @cubical.DVar(fresh_dim())
  let mid = vpapp(w, j)
  assert_true(val_conv(vpapp(mid, @cubical.DZero), VFin(4)))
  assert_true(val_conv(vpapp(mid, @cubical.DOne), VFin(4)))
  // transport along it is the inverse permutation
  assert_true(val_conv(transport(p, VLit(0)), VLit(3)))
}

///|
test "uaη: on every permutation, where it degenerates to the definitional law" {
  for t in perms(4) {
    let e = perm_equiv(4, t)
    let p = ua(e)
    let w = ua_eta_general(p)
    assert_true(val_conv(vpapp(w, @cubical.DZero), ua(idtoeqv(p))))
    assert_true(val_conv(vpapp(w, @cubical.DOne), p))
    // on the image of ua the two ends already coincide definitionally
    assert_true(val_conv(ua(idtoeqv(p)), p))
  }
}

///|
test "uaη: the witness is a path, so the path algebra applies to it" {
  let a = VFin(3)
  let p = refl(a)
  let w = ua_eta_general(p)
  // reversing it swaps the ends
  let rw = path_sym(w)
  assert_true(val_conv(vpapp(rw, @cubical.DZero), p))
  assert_true(val_conv(vpapp(rw, @cubical.DOne), ua(idtoeqv(p))))
  // concatenating it with its reverse gives a loop at ua(idtoeqv p)
  let cyc = path_concat(path_ty(VU, a, a), w, path_sym(w))
  assert_true(val_conv(vpapp(cyc, @cubical.DZero), ua(idtoeqv(p))))
  assert_true(val_conv(vpapp(cyc, @cubical.DOne), ua(idtoeqv(p))))
  // The two ends of the witness induce the same transport.  This is
  // checked at the ends, where it is definitional; the interior of the
  // witness is a computed coercion, and agreement there is propositional.
  let e = perm_equiv(3, [1, 2, 0])
  let q = ua(e)
  let wq = ua_eta_general(q)
  let near = vpapp(wq, @cubical.DZero)
  let far = vpapp(wq, @cubical.DOne)
  for k in 0..<3 {
    let want = vapp(e.fwd, VLit(k))
    assert_true(val_conv(transport(near, VLit(k)), want))
    assert_true(val_conv(transport(far, VLit(k)), want))
  }
  // and the interior lines are still lines from A to B
  let j = @cubical.DVar(fresh_dim())
  let mid = vpapp(wq, j)
  assert_true(val_conv(vpapp(mid, @cubical.DZero), VFin(3)))
  assert_true(val_conv(vpapp(mid, @cubical.DOne), VFin(3)))
}

///|
test "univalence is an equivalence: uaβ and uaη together" {
  // uaβ : transport (ua e) = e.fwd, definitionally.
  // uaη : ua (idtoeqv p) ~ p, by a constructed witness, for every p.
  // Together they say ua and idtoeqv are mutually inverse — univalence.
  for t in perms(3) {
    let e = perm_equiv(3, t)
    // one triangle: idtoeqv ∘ ua = id, on the nose
    let back = idtoeqv(ua(e))
    for k in 0..<3 {
      assert_true(val_conv(vapp(back.fwd, VLit(k)), vapp(e.fwd, VLit(k))))
      assert_true(val_conv(vapp(back.bwd, VLit(k)), vapp(e.bwd, VLit(k))))
    }
    // the other triangle: ua ∘ idtoeqv = id, by the witness
    let p = ua(e)
    let w = ua_eta_general(p)
    assert_true(val_conv(vpapp(w, @cubical.DZero), ua(idtoeqv(p))))
    assert_true(val_conv(vpapp(w, @cubical.DOne), p))
  }
  // and the second triangle is not vacuous: it has content off the image
  let a = VFin(3)
  assert_false(val_conv(ua(idtoeqv(refl(a))), refl(a)))
  let w = ua_eta_general(refl(a))
  assert_true(val_conv(vpapp(w, @cubical.DOne), refl(a)))
}

///|
test "uaη: on an infinite type" {
  // The Cantor space again: no enumeration, and the witness is built by
  // the same J regardless of the size of the type.
  let cantor = VPi(VNat, Clo::{ f: fn(_) { VFin(2) }, })
  let p = refl(cantor)
  let w = ua_eta_general(p)
  assert_true(val_conv(vpapp(w, @cubical.DZero), ua(idtoeqv(p))))
  assert_true(val_conv(vpapp(w, @cubical.DOne), p))
  let j = @cubical.DVar(fresh_dim())
  let mid = vpapp(w, j)
  assert_true(val_conv(vpapp(mid, @cubical.DZero), cantor))
  assert_true(val_conv(vpapp(mid, @cubical.DOne), cantor))
}
