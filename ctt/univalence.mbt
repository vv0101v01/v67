///|
/// # Univalence, computationally
///
/// `ua` turns an equivalence into a *path in the universe*, and the path
/// is a `Glue` type — so transporting along it runs the `Glue` clause of
/// `comp`, which contracts a fibre and returns the map applied to the
/// element.  Univalence is not an axiom here: it is a program with a
/// reduction rule.

///|
/// `ua(e) : Path U A B`, defined as
/// `<i> Glue [(i=0) ↦ (A, e), (i=1) ↦ (B, id)] B`.
///
/// The endpoints are *strict*: at `i = 0` the first branch is total and
/// the smart constructor returns `A` on the nose; at `i = 1` the second
/// is total and it returns `B`.
pub fn ua(e : Equiv) -> Val {
  VPLam(DClo::{
    f: fn(r) {
      let c0 = cof_subst(@cubical.CEq(@cubical.DVar(0), 0), 0, r)
      let c1 = cof_subst(@cubical.CEq(@cubical.DVar(0), 1), 0, r)
      mk_glue_ty(
        [
          GlueBr::{ cof: c0, ty: e.src, eq: e, },
          GlueBr::{ cof: c1, ty: e.tgt, eq: equiv_id(e.tgt), },
        ],
        e.tgt,
      )
    },
  })
}

///|
/// The dimension family of a path in the universe.
pub fn path_fam(p : Val) -> Fam {
  Fam::{ f: fn(r) { vpapp(p, r) }, }
}

///|
/// Transport along a path of types: `transport p a = coe^{0→1} p a`.
pub fn transport(p : Val, a : Val) -> Val {
  coe(path_fam(p), 0, a)
}

///|
/// `idtoeqv(p)`: transport forward and backward along a path of types.
///
/// The forward and backward round trips are **not** definitional for a
/// general `p`, so this is a genuinely non-strict equivalence.  Its fibre
/// contraction is constructed by **path induction** (see
/// `transport_contr`), not assumed — which is what lets `ua` be applied
/// to an arbitrary line of types rather than only to strict isomorphisms.
pub fn idtoeqv(p : Val) -> Equiv {
  let fam = path_fam(p)
  let a = fam.at(@cubical.DZero)
  let b = fam.at(@cubical.DOne)
  let fwd = VLam(Clo::{ f: fn(x) { coe(fam, 0, x) }, })
  // `bwd` and `beta` are the two components of the *same* transported
  // centre, so they agree with the centre used by `contr` definitionally.
  let bwd = VLam(Clo::{ f: fn(x) { vfst(transport_center(p, x)) }, })
  Equiv::{
    src: a,
    tgt: b,
    fwd,
    bwd,
    alpha: lazy_clo(fn() {
      Clo::{ f: fn(x) { vapp(roundtrip_fun(p, false), x) }, }
    }),
    beta: lazy_clo(fn() { Clo::{ f: fn(y) { vsnd(transport_center(p, y)) }, } }),
    contr: lazy_contr(fn() { transport_contr(p) }),
    strict: lazy_false(),
  }
}

///|
/// **uaβ.**  `transport (ua e) a` reduces to `e a`.
pub fn ua_beta(e : Equiv, a : Val) -> Val {
  transport(ua(e), a)
}

///|
/// **uaη.**  `ua (idtoeqv p)` versus `p`.  On the image of `ua` the two are
/// convertible; for a general line they are only propositionally equal,
/// and `ua_eta_path` constructs that path.
pub fn ua_eta(p : Val) -> (Val, Val) {
  (ua(idtoeqv(p)), p)
}

// --------------------------------------------------------------------
// Path algebra.
// --------------------------------------------------------------------

///|
pub fn refl(a : Val) -> Val {
  VPLam(DClo::{ f: fn(_) { a }, })
}

///|
pub fn path_sym(p : Val) -> Val {
  VPLam(DClo::{ f: fn(r) { vpapp(p, dim_not(r)) }, })
}

///|
/// Concatenation, by homogeneous composition:
/// `p · q = <i> comp^k A [(i=0) ↦ p(0), (i=1) ↦ q(k)] (p(i))`.
pub fn path_concat(a : Val, p : Val, q : Val) -> Val {
  VPLam(DClo::{
    f: fn(r) {
      let k = fresh_dim()
      let i = 0
      let tube = Tube::{
        branches: [
          TubeBr::{
            cof: cof_subst(@cubical.CEq(@cubical.DVar(i), 0), i, r),
            tm: DClo::{ f: fn(_) { vpapp(p, @cubical.DZero) }, },
          },
          TubeBr::{
            cof: cof_subst(@cubical.CEq(@cubical.DVar(i), 1), i, r),
            tm: DClo::{ f: fn(m) { vpapp(q, m) }, },
          },
        ],
      }
      comp(fam_const(a), k, tube, vpapp(p, r))
    },
  })
}

///|
/// Application of a map to a path: `ap f p = <i> f (p i)`.
pub fn ap(f : Val, p : Val) -> Val {
  VPLam(DClo::{ f: fn(r) { vapp(f, vpapp(p, r)) }, })
}

///|
/// **Function extensionality**: `funext h = <i> λx. h(x)(i)`.
pub fn funext(h : Clo) -> Val {
  VPLam(DClo::{ f: fn(r) { VLam(Clo::{ f: fn(x) { vpapp(h.at(x), r) }, }) }, })
}

///|
/// **The singleton contraction**:
/// `η(a,p)(j) = (p(j), <i> p(i ∧ j)) : (a, refl a) ⟶ (b, p)`
/// in `Σ(x:A). Path A a x`.
pub fn singleton_contract(p : Val) -> Val {
  VPLam(DClo::{
    f: fn(r) {
      VPair(vpapp(p, r), VPLam(DClo::{ f: fn(s) { vpapp(p, dim_and(s, r)) }, }))
    },
  })
}

///|
/// **Path induction (J)** with its computation rule.  When `p` is `refl a`
/// the singleton line is constant, regularity fires, and the result is
/// `d` on the nose.
pub fn pathJ(mot : (Val, Val) -> Val, d : Val, p : Val) -> Val {
  let eta = singleton_contract(p)
  let fam = Fam::{
    f: fn(r) {
      let pr = vpapp(eta, r)
      mot(vfst(pr), vsnd(pr))
    },
  }
  coe(fam, 0, d)
}

// --------------------------------------------------------------------
// Homotopy levels.
// --------------------------------------------------------------------

///|
pub fn dclo_const(a : Val) -> DClo {
  DClo::{ f: fn(_) { a }, }
}

///|
/// `Path A x y` as a type.
pub fn path_ty(a : Val, x : Val, y : Val) -> Val {
  VPath(dclo_const(a), x, y)
}

///|
/// `isContr A = Σ(x:A). Π(y:A). Path A x y`.
pub fn is_contr(a : Val) -> Val {
  VSig(a, Clo::{ f: fn(x) { VPi(a, Clo::{ f: fn(y) { path_ty(a, x, y) }, }) }, })
}

///|
/// `isProp A = Π(x y:A). Path A x y`.
pub fn is_prop(a : Val) -> Val {
  VPi(a, Clo::{ f: fn(x) { VPi(a, Clo::{ f: fn(y) { path_ty(a, x, y) }, }) }, })
}

///|
/// `isSet A = Π(x y:A). isProp (Path A x y)`.
pub fn is_set(a : Val) -> Val {
  VPi(a, Clo::{
    f: fn(x) { VPi(a, Clo::{ f: fn(y) { is_prop(path_ty(a, x, y)) }, }) },
  })
}

///|
/// A contractible type is a proposition: `λx y. (h x)⁻¹ · (h y)`.
pub fn contr_to_prop(a : Val, ctr : Val) -> Val {
  let h = vsnd(ctr)
  VLam(Clo::{
    f: fn(x) {
      VLam(Clo::{
        f: fn(y) { path_concat(a, path_sym(vapp(h, x)), vapp(h, y)) },
      })
    },
  })
}

///|
/// `Fin 1` is contractible.
pub fn fin1_contr() -> Val {
  VPair(VLit(0), VLam(Clo::{ f: fn(_) { refl(VLit(0)) }, }))
}

///|
/// Every element of `Fin n`, as values.
pub fn fin_points(n : Int32) -> Array[Val] {
  let out : Array[Val] = []
  for k in 0..<n {
    out.push(VLit(k))
  }
  out
}
