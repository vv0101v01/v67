///|
test "general equiv: the fibre contraction of a strict isomorphism" {
  let e = perm_equiv(4, [1, 2, 3, 0])
  let pts = fin_points(4)
  assert_true(e.check(pts, pts))
  // for every a and every (t, p) in the fibre, contr has the right ends
  for a in pts {
    for t in pts {
      let p = refl(vapp(e.fwd, t))
      if vapp(e.fwd, t) == a {
        assert_true(e.check_contr(a, t, p))
      }
    }
  }
}

///|
test "general equiv: equiv extends a partial element of the fibre" {
  let e = perm_equiv(3, [1, 2, 0])
  let a = VLit(2)
  let t = VLit(1) // e(1) = 2 = a
  let p = refl(VLit(2))
  // on the total extent the result must be exactly (t, p)
  let (t1, alpha) = equiv(e, a, [(@cubical.CTop, t, p)])
  assert_eq(quote_norm(t1, 8), "#1")
  assert_eq(quote_norm(alpha, 8), quote_norm(refl(VLit(2)), 8))
  // with no constraint it returns the centre
  let (t0, _) = equiv(e, a, [])
  assert_eq(quote_norm(t0, 8), quote_norm(vapp(e.bwd, a), 8))
}

///|
test "general equiv: idtoeqv of a composite line is NOT strict" {
  // p · q has genuinely non-definitional round trips, so this exercises
  // the Glue rule with an equivalence whose β is a real path.
  let e = shift_equiv(9)
  let pq = path_concat(VU, ua(e), ua(e))
  let eq = idtoeqv(pq)
  let y = VLit(0)
  let beta_y = eq.beta.at(y)
  // β y : Path (fwd (bwd y)) y — a path, computed by J, not refl-by-fiat
  assert_eq(quote_norm(vpapp(beta_y, @cubical.DZero), 8), quote_norm(y, 8))
  assert_eq(quote_norm(vpapp(beta_y, @cubical.DOne), 8), quote_norm(y, 8))
  // and the fibre contraction really contracts, on the composite line
  assert_true(eq.check_contr(y, VLit(7), refl(VLit(0))))
  let simple = idtoeqv(ua(shift_equiv(9)))
  assert_true(simple.check_contr(VLit(0), VLit(8), refl(VLit(0))))
}

///|
test "general equiv: ua of a non-strict equivalence transports correctly" {
  let e = shift_equiv(9)
  let pq = path_concat(VU, ua(e), ua(e))
  let eq = idtoeqv(pq)
  // ua(eq) is a Glue line built from a non-strict equivalence; the
  // correction step (dragging the base along α) is what makes it compute
  let line = ua(eq)
  for k in 0..<9 {
    let got = transport(line, VLit(k))
    assert_eq(quote_norm(got, 8), "#\{(k + 2) % 9}")
  }
}

///|
test "infinite: Nat is a discrete type of the kernel" {
  let n = nat_lit(41)
  assert_eq(quote_norm(coe(fam_const(VNat), 0, n), 8), quote_norm(n, 8))
  let tube = Tube::empty().add(@cubical.CEq(@cubical.DVar(2), 0), DClo::{
    f: fn(_) { n },
  })
  assert_eq(quote_norm(comp(fam_const(VNat), 0, tube, n), 8), quote_norm(n, 8))
}

///|
test "infinite: univalence on the Cantor space (Nat -> Bool)" {
  // `Nat -> Fin 2` has 2^aleph_0 elements.  Conjugating by negation on
  // Bool is a strict isomorphism of it, and transport along its ua acts
  // pointwise — computed in constant time, with no enumeration anywhere.
  let cantor = VPi(VNat, Clo::{ f: fn(_) { VFin(2) }, })
  let neg = fin_fun([1, 0])
  let conj = Equiv::new(
    cantor,
    cantor,
    VLam(Clo::{
      f: fn(g) { VLam(Clo::{ f: fn(x) { vapp(neg, vapp(g, x)) }, }) },
    }),
    VLam(Clo::{
      f: fn(g) { VLam(Clo::{ f: fn(x) { vapp(neg, vapp(g, x)) }, }) },
    }),
  )
  let p = ua(conj)
  // the constantly-zero predicate
  let zero_fun = VLam(Clo::{ f: fn(_) { VLit(0) }, })
  let h = transport(p, zero_fun)
  assert_eq(quote_norm(vapp(h, nat_lit(0)), 6), "#1")
  assert_eq(quote_norm(vapp(h, nat_lit(1000)), 6), "#1")
  // and it is an involution
  let h2 = transport(p, h)
  assert_eq(quote_norm(vapp(h2, nat_lit(7)), 6), "#0")
}

///|
test "infinite: case splits are natural in neutrals" {
  let neg = fin_fun([1, 0])
  // under a binder the split stays, and reads back with a named scrutinee
  assert_eq(quote_norm(neg, 8), "λx0. case[x0 : Fin(2) | #1 | #0]")
  // applying it to a literal still computes
  assert_eq(quote_norm(vapp(neg, VLit(0)), 6), "#1")
  // and the composite neg ∘ neg is the identity *as a term*, by reading
  // back both branches of the stuck split
  let twice = VLam(Clo::{ f: fn(x) { vapp(neg, vapp(neg, x)) }, })
  assert_eq(quote_norm(vapp(twice, VLit(1)), 6), "#1")
}

///|
test "h-levels: a contractible type has contractible path spaces" {
  let a = VFin(1)
  let ctr = fin1_contr()
  let x = VLit(0)
  let y = VLit(0)
  let cp = contr_path_contr(a, ctr, x, y)
  let center = vfst(cp)
  let h = vsnd(cp)
  let p = refl(VLit(0))
  let sq = vapp(h, p)
  // the square's four faces: j=0 is the centre, j=1 is p, i=0 is x, i=1 is y
  assert_eq(quote_norm(vpapp(sq, @cubical.DZero), 8), quote_norm(center, 8))
  assert_eq(quote_norm(vpapp(sq, @cubical.DOne), 8), quote_norm(p, 8))
  assert_eq(
    quote_norm(vpapp(vpapp(sq, @cubical.DVar(5)), @cubical.DZero), 8),
    "#0",
  )
  assert_eq(
    quote_norm(vpapp(vpapp(sq, @cubical.DVar(5)), @cubical.DOne), 8),
    "#0",
  )
}

///|
test "h-levels: isProp A gives isSet A" {
  let a = VFin(1)
  let f = contr_to_prop(a, fin1_contr())
  let set = is_prop_to_set(a, f)
  let x = VLit(0)
  let y = VLit(0)
  let prop_path = vapp(vapp(set, x), y)
  let p = refl(VLit(0))
  let q = refl(VLit(0))
  let sq = vapp(vapp(prop_path, p), q)
  // a path between the two paths, with the right endpoints
  assert_eq(quote_norm(vpapp(sq, @cubical.DZero), 8), quote_norm(p, 8))
  assert_eq(quote_norm(vpapp(sq, @cubical.DOne), 8), quote_norm(q, 8))
}

///|
test "path algebra: ua(e) followed by ua(e⁻¹) transports as the identity" {
  for t in perms(4) {
    let e = perm_equiv(4, t)
    let p = path_concat(VU, ua(e), ua(equiv_inv(e)))
    for k in 0..<4 {
      assert_eq(quote_norm(transport(p, VLit(k)), 8), "#\{k}")
    }
  }
}

///|
test "regression: composition in a dependent path type moves its endpoints" {
  // The endpoints of `Path (B i) (a i) (b i)` vary with the family.  A
  // composition that freezes them at the generic stage leaves the
  // composition direction free in the lid, which showed up as a fibre
  // contraction whose first component was a `glue` wrapper instead of a
  // literal.  Here the family is a *composite* ua line, so the endpoints
  // genuinely move.
  let e = shift_equiv(9)
  let pq = path_concat(VU, ua(e), ua(e))
  let eq = idtoeqv(pq)
  // the contraction is now definitional at both ends, on the nose
  assert_true(eq.check_contr(VLit(0), VLit(7), refl(VLit(0))))
  for k in 0..<9 {
    let y = VLit(k)
    let x = VLit((k + 7) % 9)
    assert_true(eq.check_contr(y, x, refl(y)))
  }
  // and no free dimension survives in the readback
  let c = (eq.contr.f)(VLit(0), VLit(7), refl(VLit(0)))
  assert_eq(quote_norm(vpapp(c, @cubical.DOne), 8), "(#7, <x0> #0)")
  assert_eq(quote_norm(vpapp(c, @cubical.DZero), 8), "(#7, <x0> #0)")
}
