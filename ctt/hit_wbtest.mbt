///|
test "HIT: the circle's constructors and the endpoints of loop" {
  let l = circle_loop()
  assert_true(val_conv(vpapp(l, @cubical.DZero), VBase))
  assert_true(val_conv(vpapp(l, @cubical.DOne), VBase))
  // in the interior it is a genuine path constructor, not base
  let r = @cubical.DVar(fresh_dim())
  assert_false(val_conv(vpapp(l, r), VBase))
  assert_eq(quote_norm(vpapp(l, r), 6), "loop(x0)")
  // loop is not refl: that is the whole point of S¹
  assert_false(val_conv(l, refl(VBase)))
}

///|
test "HIT: S¹-recursion has its β-rule on the path constructor" {
  // Recurse into the circle itself, sending base ↦ base and loop ↦ loop.
  let rec = VLam(Clo::{
    f: fn(x) { circle_rec(VCircle, VBase, circle_loop(), x) },
  })
  assert_true(val_conv(vapp(rec, VBase), VBase))
  let r = @cubical.DVar(fresh_dim())
  // ap rec loop = loop, on the nose
  assert_true(val_conv(vpapp(circle_loop(), r), vapp(rec, vloop(r))))
  // and into a *discrete* target, where every loop must be refl: the
  // recursor is forced to send loop to refl, and it does
  let into_fin = VLam(Clo::{
    f: fn(x) { circle_rec(VFin(3), VLit(2), refl(VLit(2)), x) },
  })
  assert_true(val_conv(vapp(into_fin, VBase), VLit(2)))
  assert_true(val_conv(vapp(into_fin, vloop(r)), VLit(2)))
}

///|
test "HIT: composition in the circle produces a formal composite" {
  // A box in S¹ with a wall that moves along loop has no constructor lid.
  let i = fresh_dim()
  let j = fresh_dim()
  let tube = Tube::empty().add(@cubical.CEq(@cubical.DVar(j), 0), DClo::{
    f: fn(r) { vloop(r) },
  })
  let lid = comp(fam_const(VCircle), i, tube, VBase)
  match lid {
    VHComp(ty, _, _) => assert_true(val_conv(ty, VCircle))
    _ => abort("expected a formal composite")
  }
  // regularity still holds: a constant box is filled by its cap
  let const_box = Tube::empty().add(@cubical.CEq(@cubical.DVar(j), 0), DClo::{
    f: fn(_) { VBase },
  })
  assert_true(val_conv(comp(fam_const(VCircle), i, const_box, VBase), VBase))
  // and coercion along a constant line is the identity
  assert_true(val_conv(coe(fam_const(VCircle), i, VBase), VBase))
}

///|
test "HIT: the recursor preserves formal composition" {
  // The formal-composite clause is not optional: without it the recursor
  // would be undefined on the lid above.  Recursing into a discrete type
  // must collapse the composite, because every wall's image is the same.
  let i = fresh_dim()
  let j = fresh_dim()
  let tube = Tube::empty().add(@cubical.CEq(@cubical.DVar(j), 0), DClo::{
    f: fn(r) { vloop(r) },
  })
  let lid = comp(fam_const(VCircle), i, tube, VBase)
  let img = circle_rec(VFin(3), VLit(2), refl(VLit(2)), lid)
  assert_true(val_conv(img, VLit(2)))
}

///|
test "HIT: truncation is a proposition" {
  let a = VFin(4)
  let ty = VTrunc(a)
  let prop = trunc_is_prop(ty)
  let x = VInc(VLit(1))
  let y = VInc(VLit(3))
  let p = vapp(vapp(prop, x), y)
  assert_true(val_conv(vpapp(p, @cubical.DZero), x))
  assert_true(val_conv(vpapp(p, @cubical.DOne), y))
  // and between two *neutral* points, which is what makes it a proposition
  // rather than merely a connected-on-points type
  let u = VNe(fresh_dim())
  let v = VNe(fresh_dim())
  let q = vapp(vapp(prop, u), v)
  assert_true(val_conv(vpapp(q, @cubical.DZero), u))
  assert_true(val_conv(vpapp(q, @cubical.DOne), v))
  // the type code renders
  assert_eq(quote_norm(ty, 6), "∥Fin(4)∥")
}

///|
test "HIT: truncation recursion into a proposition, with its β-rules" {
  // ∥Fin 4∥ → Fin 1: the target is a proposition, so the constant map
  // extends, and the sq clause is forced to be refl.
  let a = VFin(4)
  let ty = VTrunc(a)
  let target = VFin(1)
  let f = VLam(Clo::{ f: fn(_) { VLit(0) }, })
  let prop = contr_to_prop(target, fin1_contr())
  let rec = VLam(Clo::{ f: fn(x) { trunc_rec(target, f, prop, x) }, })
  // β on the point constructor
  assert_true(val_conv(vapp(rec, VInc(VLit(2))), VLit(0)))
  // β on the path constructor: sq goes to the path prop supplies
  let r = @cubical.DVar(fresh_dim())
  let sq = trunc_sq(ty, VInc(VLit(1)), VInc(VLit(3)))
  assert_true(val_conv(vapp(rec, vpapp(sq, r)), VLit(0)))
  // and on a neutral it is stuck, not silently evaluated
  let u = VNe(fresh_dim())
  match vapp(rec, u) {
    VTruncRec(_, _, _, _) => ()
    _ => abort("expected a stuck truncation recursor")
  }
}

///|
test "HIT: an inhabited proposition is contractible — ∥S¹∥" {
  let ctr = circle_trunc_contr()
  let pt = vfst(ctr)
  let h = vsnd(ctr)
  assert_true(val_conv(pt, VInc(VBase)))
  // the contraction connects the centre to any point, including neutrals
  let u = VNe(fresh_dim())
  let p = vapp(h, u)
  assert_true(val_conv(vpapp(p, @cubical.DZero), VInc(VBase)))
  assert_true(val_conv(vpapp(p, @cubical.DOne), u))
  // so ∥S¹∥ is a proposition, hence a set, by the Hedberg step
  let ty = VTrunc(VCircle)
  let prop = contr_to_prop(ty, ctr)
  let set = is_prop_to_set(ty, prop)
  let sq = vapp(vapp(vapp(vapp(set, pt), pt), vapp(h, pt)), refl(pt))
  assert_true(val_conv(vpapp(sq, @cubical.DZero), vapp(h, pt)))
  assert_true(val_conv(vpapp(sq, @cubical.DOne), refl(pt)))
}

///|
test "HIT: suspension has two poles and a meridian per point" {
  let a = VFin(2)
  let ty = VSusp(a)
  let m0 = susp_merid(a, VLit(0))
  let m1 = susp_merid(a, VLit(1))
  assert_true(val_conv(vpapp(m0, @cubical.DZero), VNorth))
  assert_true(val_conv(vpapp(m0, @cubical.DOne), VSouth))
  assert_false(val_conv(m0, m1))
  assert_false(val_conv(VNorth, VSouth))
  // Susp-rec into a discrete type: both poles and every meridian collapse
  let rec = VLam(Clo::{
    f: fn(x) {
      susp_rec(
        VFin(1),
        VLit(0),
        VLit(0),
        VLam(Clo::{ f: fn(_) { refl(VLit(0)) }, }),
        x,
      )
    },
  })
  let r = @cubical.DVar(fresh_dim())
  assert_true(val_conv(vapp(rec, VNorth), VLit(0)))
  assert_true(val_conv(vapp(rec, VSouth), VLit(0)))
  assert_true(val_conv(vapp(rec, vpapp(m0, r)), VLit(0)))
  assert_eq(quote_norm(ty, 6), "Susp(Fin(2))")
  // composition is again formal
  let i = fresh_dim()
  let tube = Tube::empty().add(@cubical.CEq(@cubical.DVar(i), 0), DClo::{
    f: fn(s) { vpapp(m0, s) },
  })
  match comp(fam_const(ty), i, tube, VNorth) {
    VHComp(t, _, _) => assert_true(val_conv(t, ty))
    _ => abort("expected a formal composite")
  }
}

///|
test "HIT: the circle is not a set-level type — loop survives conversion" {
  // A set would have all its loops equal.  The kernel must not identify
  // loop with refl, nor two formal composites with different walls.
  assert_false(val_conv(circle_loop(), refl(VBase)))
  let i = fresh_dim()
  let t1 = Tube::empty().add(@cubical.CEq(@cubical.DVar(i), 0), DClo::{
    f: fn(r) { vloop(r) },
  })
  let t2 = Tube::empty().add(@cubical.CEq(@cubical.DVar(i), 0), DClo::{
    f: fn(_) { VBase },
  })
  let c1 = comp(fam_const(VCircle), i, t1, VBase)
  let c2 = comp(fam_const(VCircle), i, t2, VBase)
  assert_false(val_conv(c1, c2))
  // and the recursor into S¹ itself keeps them apart
  let rec = VLam(Clo::{
    f: fn(x) { circle_rec(VCircle, VBase, circle_loop(), x) },
  })
  assert_false(val_conv(vapp(rec, c1), vapp(rec, c2)))
}

///|
test "HIT: the coequalizer adds a path without identifying the points" {
  let b = VFin(2)
  let id = fin_fun([0, 1])
  let neg = fin_fun([1, 0])
  let ty = VCoeq(b, id, neg)
  let r0 = coeq_rel(id, neg, VLit(0))
  // rel 0 goes from cinc #0 to cinc #1
  assert_true(val_conv(vpapp(r0, @cubical.DZero), VCoeqInc(VLit(0))))
  assert_true(val_conv(vpapp(r0, @cubical.DOne), VCoeqInc(VLit(1))))
  // but the two points are NOT definitionally equal: a coequalizer is not
  // a set-truncation, and collapsing them here would be unsound
  assert_false(val_conv(VCoeqInc(VLit(0)), VCoeqInc(VLit(1))))
  let i = @cubical.DVar(fresh_dim())
  assert_false(val_conv(vpapp(r0, i), VCoeqInc(VLit(0))))
  assert_eq(quote_norm(ty, 6), "Coeq(Fin(2))")
}

///|
test "HIT: coequalizer recursion, with its β-rule on the path constructor" {
  let id = fin_fun([0, 1])
  let neg = fin_fun([1, 0])
  // into Fin 1, a proposition: the constant map equalises anything
  let target = VFin(1)
  let h = VLam(Clo::{ f: fn(_) { VLit(0) }, })
  let p = VLam(Clo::{ f: fn(_) { refl(VLit(0)) }, })
  let rec = VLam(Clo::{ f: fn(x) { coeq_rec(target, h, p, x) }, })
  assert_true(val_conv(vapp(rec, VCoeqInc(VLit(0))), VLit(0)))
  assert_true(val_conv(vapp(rec, VCoeqInc(VLit(1))), VLit(0)))
  let i = @cubical.DVar(fresh_dim())
  assert_true(
    val_conv(vapp(rec, vpapp(coeq_rel(id, neg, VLit(0)), i)), VLit(0)),
  )
  // on a neutral it is stuck
  match vapp(rec, VNe(fresh_dim())) {
    VCoeqRec(_, _, _, _) => ()
    _ => abort("expected a stuck coequalizer recursor")
  }
}

///|
test "HIT: Coeq f f keeps a loop — it does not collapse to B" {
  let b = VFin(2)
  let id = fin_fun([0, 1])
  let loop0 = coeq_rel(id, id, VLit(0))
  // both endpoints are the same point, yet the path is a constructor, not
  // refl: Coeq f f is B with a loop at each f a.
  assert_true(val_conv(vpapp(loop0, @cubical.DZero), VCoeqInc(VLit(0))))
  assert_true(val_conv(vpapp(loop0, @cubical.DOne), VCoeqInc(VLit(0))))
  assert_false(val_conv(loop0, refl(VCoeqInc(VLit(0)))))
  // a recursor into Fin 1 must still send that loop to refl, and does
  let target = VFin(1)
  let h = VLam(Clo::{ f: fn(_) { VLit(0) }, })
  let p = VLam(Clo::{ f: fn(_) { refl(VLit(0)) }, })
  let i = @cubical.DVar(fresh_dim())
  assert_true(val_conv(coeq_rec(target, h, p, vpapp(loop0, i)), VLit(0)))
  // composition in a coequalizer is again formal
  let j = fresh_dim()
  let k = fresh_dim()
  let tube = Tube::empty().add(@cubical.CEq(@cubical.DVar(k), 0), DClo::{
    f: fn(s) { vpapp(coeq_rel(id, id, VLit(0)), s) },
  })
  match comp(fam_const(VCoeq(b, id, id)), j, tube, VCoeqInc(VLit(0))) {
    VHComp(_, _, _) => ()
    _ => abort("expected a formal composite")
  }
}
