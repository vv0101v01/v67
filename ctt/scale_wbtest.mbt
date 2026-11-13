///|
/// The cyclic shift on `Fin n`, defined arithmetically rather than by a
/// table, so `n` may be huge.  Both round trips are definitionally the
/// identity on closed elements, so it is a strict isomorphism.
fn shift_equiv(n : Int32) -> Equiv {
  Equiv::new(
    VFin(n),
    VFin(n),
    VLam(Clo::{
      f: fn(x) {
        match x {
          VLit(k) => VLit((k + 1) % n)
          _ => x
        }
      },
    }),
    VLam(Clo::{
      f: fn(x) {
        match x {
          VLit(k) => VLit((k + n - 1) % n)
          _ => x
        }
      },
    }),
  )
}

///|
test "scale: univalence on Fin 1000000, where enumeration is impossible" {
  // The finite-presheaf `cubical.comp` inspects every element of the
  // generic fibre.  Here the fibre has a million elements and the lid is
  // produced in constant time, because the algorithm recurses on the
  // *type*, which has three nodes.
  let n = 1000000
  let e = shift_equiv(n)
  let p = ua(e)
  assert_eq(quote_norm(transport(p, VLit(0)), 6), "#1")
  assert_eq(quote_norm(transport(p, VLit(999999)), 6), "#0")
  assert_eq(quote_norm(transport(p, VLit(500000)), 6), "#500001")
  assert_eq(quote_norm(coe_back(path_fam(p), 0, VLit(0)), 6), "#999999")
}

///|
test "scale: composition in a function space with 1000^1000 elements" {
  let big = VPi(VFin(1000), Clo::{ f: fn(_) { VFin(1000) }, })
  let w = VLam(Clo::{
    f: fn(x) {
      match x {
        VLit(k) => VLit(k * 3 % 1000)
        _ => x
      }
    },
  })
  let tube = Tube::empty().add(@cubical.CEq(@cubical.DVar(3), 0), DClo::{
    f: fn(_) { w },
  })
  let lid = comp(fam_const(big), 0, tube, w)
  assert_eq(quote_norm(vapp(lid, VLit(7)), 6), "#21")
  assert_eq(quote_norm(vapp(lid, VLit(999)), 6), "#997")
}

///|
test "scale: univalence on a million-element function space" {
  // transport along ua of the induced conjugation equivalence on
  // (Fin 10^6 → Fin 10^6): a type with (10^6)^(10^6) elements.
  let n = 1000000
  let e = shift_equiv(n)
  let conj = Equiv::new(
    VPi(VFin(n), Clo::{ f: fn(_) { VFin(n) }, }),
    VPi(VFin(n), Clo::{ f: fn(_) { VFin(n) }, }),
    VLam(Clo::{
      f: fn(g) {
        VLam(Clo::{ f: fn(x) { vapp(e.fwd, vapp(g, vapp(e.bwd, x))) }, })
      },
    }),
    VLam(Clo::{
      f: fn(g) {
        VLam(Clo::{ f: fn(x) { vapp(e.bwd, vapp(g, vapp(e.fwd, x))) }, })
      },
    }),
  )
  let h = transport(ua(conj), e.fwd)
  // conjugating the shift by itself gives the shift back
  assert_eq(quote_norm(vapp(h, VLit(0)), 6), "#1")
  assert_eq(quote_norm(vapp(h, VLit(999998)), 6), "#999999")
}

///|
test "scale: filling a Glue box has the right boundaries" {
  let e = shift_equiv(7)
  let p = ua(e)
  let fam = path_fam(p)
  let f = fill(fam, 0, Tube::empty(), VLit(3))
  assert_eq(quote_norm(f.at(@cubical.DZero), 6), "#3")
  assert_eq(quote_norm(f.at(@cubical.DOne), 6), "#4")
}

///|
test "scale: transport along a composite path is the composite transport" {
  let e = shift_equiv(9)
  let f = shift_equiv(9)
  let p = ua(e)
  let q = ua(f)
  let pq = path_concat(VU, p, q)
  for k in 0..<9 {
    let via = transport(pq, VLit(k))
    let step = transport(q, transport(p, VLit(k)))
    assert_eq(quote_norm(via, 8), quote_norm(step, 8))
  }
}

///|
test "scale: ua respects composition and inversion of equivalences" {
  let e = shift_equiv(5)
  let g = perm_equiv(5, [4, 3, 2, 1, 0])
  let comp_eq = equiv_comp(e, g)
  let pts = fin_points(5)
  assert_true(comp_eq.check(pts, pts))
  assert_true(equiv_inv(e).check(pts, pts))
  // transport along ua(g ∘ e) = g ∘ e
  for k in 0..<5 {
    let want = vapp(g.fwd, vapp(e.fwd, VLit(k)))
    assert_eq(
      quote_norm(transport(ua(comp_eq), VLit(k)), 8),
      quote_norm(want, 8),
    )
  }
  // transport along ua(e⁻¹) = e⁻¹
  for k in 0..<5 {
    assert_eq(
      quote_norm(transport(ua(equiv_inv(e)), VLit(k)), 8),
      quote_norm(vapp(e.bwd, VLit(k)), 8),
    )
  }
}
