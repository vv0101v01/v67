///|
test "kan: a discrete type has unique composition" {
  // Fin 3, tube on (j=0), cap #1.  The lid is the cap: no search.
  let box = Tube::{
    branches: [tube_const(@cubical.CEq(@cubical.DVar(1), 0), VLit(1))],
  }
  let lid = comp(fam_const(VFin(3)), 0, box, VLit(1))
  assert_eq(quote_norm(lid, 6), "#1")
}

///|
test "kan: a total tube forces the lid strictly" {
  let tube = Tube::empty().add(@cubical.CTop, DClo::{
    f: fn(r) { VLit(if r == @cubical.DOne { 2 } else { 0 }) },
  })
  let lid = comp(fam_const(VFin(3)), 0, tube, VLit(0))
  assert_eq(quote_norm(lid, 6), "#2")
}

///|
test "kan: filler boundaries hold by construction" {
  let tube = Tube::empty().add(@cubical.CEq(@cubical.DVar(1), 0), DClo::{
    f: fn(_) { VLit(1) },
  })
  let f = fill(fam_const(VFin(3)), 0, tube, VLit(1))
  assert_eq(quote_norm(f.at(@cubical.DZero), 6), "#1")
  assert_eq(
    quote_norm(f.at(@cubical.DOne), 6),
    quote_norm(comp(fam_const(VFin(3)), 0, tube, VLit(1)), 6),
  )
}

///|
test "kan: regularity is a computation rule" {
  // A constant family, any cap: coercion is the identity, untouched.
  let a = VPair(VLit(0), VLit(2))
  assert_eq(quote_norm(coe(fam_const(VFin(4)), 0, a), 6), "(#0, #2)")
  // and the normality law for a constant box
  let tube = Tube::empty().add(@cubical.CEq(@cubical.DVar(5), 0), DClo::{
    f: fn(_) { VLit(2) },
  })
  assert_eq(quote_norm(comp(fam_const(VFin(4)), 0, tube, VLit(2)), 6), "#2")
}

///|
test "kan: composition of paths adds the endpoints to the tube" {
  let a = VPath(dclo_const(VFin(3)), VLit(0), VLit(2))
  let p = VPLam(DClo::{
    f: fn(r) {
      match r {
        @cubical.DZero => VLit(0)
        @cubical.DOne => VLit(2)
        _ => VNe(7)
      }
    },
  })
  let lid = comp(fam_const(a), 0, Tube::empty(), p)
  // the endpoints of the computed path are forced by the tube
  assert_eq(quote_norm(vpapp(lid, @cubical.DZero), 6), "#0")
  assert_eq(quote_norm(vpapp(lid, @cubical.DOne), 6), "#2")
}

///|
test "kan: composition in Sigma is a pair over the filler" {
  let ty = VSig(VFin(3), Clo::{ f: fn(_) { VFin(3) }, })
  let tube = Tube::empty().add(@cubical.CEq(@cubical.DVar(1), 0), DClo::{
    f: fn(_) { VPair(VLit(1), VLit(2)) },
  })
  let lid = comp(fam_const(ty), 0, tube, VPair(VLit(1), VLit(2)))
  assert_eq(quote_norm(lid, 6), "(#1, #2)")
}

///|
test "kan: composition in Pi is a lambda" {
  let ty = VPi(VFin(2), Clo::{ f: fn(_) { VFin(3) }, })
  let w = VLam(Clo::{ f: fn(x) { x }, })
  let tube = Tube::empty().add(@cubical.CEq(@cubical.DVar(1), 0), DClo::{
    f: fn(_) { w },
  })
  let lid = comp(fam_const(ty), 0, tube, w)
  assert_eq(quote_norm(vapp(lid, VLit(1)), 6), "#1")
  assert_eq(quote_norm(vapp(lid, VLit(0)), 6), "#0")
}

///|
test "kan: composition in the universe is a Glue type" {
  // comp^i U [(j=0) ↦ ua(e)(i)] A  =  Glue [(j=0) ↦ (B, e⁻¹)] A
  let e = Equiv::new(VFin(2), VFin(2), fin_fun([1, 0]), fin_fun([1, 0]))
  let p = ua(e)
  let tube = Tube::empty().add(@cubical.CEq(@cubical.DVar(1), 0), DClo::{
    f: fn(r) { vpapp(p, r) },
  })
  let lid = comp(fam_const(VU), 0, tube, VFin(2))
  match lid {
    VGlue(base, brs) => {
      assert_eq(quote_norm(base, 6), "Fin(2)")
      assert_eq(brs.length(), 1)
      assert_eq(quote_norm(brs[0].ty, 6), "Fin(2)")
      // the equivalence is the backward coercion, i.e. the swap again
      assert_eq(quote_norm(vapp(brs[0].eq.fwd, VLit(0)), 6), "#1")
    }
    _ => abort("comp in U must produce a Glue type")
  }
}
