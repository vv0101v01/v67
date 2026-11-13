///|
/// # `uaη` on an arbitrary path
///
/// `uaη(p) : Path (Path U A B) (ua (idtoeqv p)) p` for **every** line
/// `p : Path U A B`, not only those in the image of `ua`.
///
/// ## The base case is a Glue square with identical branch data
///
/// Path induction on `p` (with `A` fixed) leaves `B = A`, `p = refl A`.
/// There `idtoeqv (refl A)` has both maps the identity — regularity makes
/// `coe` along a constant line the identity on the nose — so the goal is
///
/// ```text
/// ua (id_A)  ~  refl A
/// ```
///
/// and that has a one-line witness.  Put
///
/// ```text
/// D(j,i) = Glue [ (i=0) ↦ (A, id), (i=1) ↦ (A, id), (j=1) ↦ (A, id) ] A
/// ```
///
/// **Every branch carries the same type and the same equivalence**, so the
/// compatibility condition on overlaps is automatic — this is the whole
/// trick, and it is why the base case needs no coherence data.
///
/// * `j = 1`: that face is total, so the `Glue` collapses to `A`; the line
///   is constant, i.e. `refl A`.
/// * `j = 0`: that face is empty, leaving
///   `Glue [(i=0) ↦ (A,id), (i=1) ↦ (A,id)] A = ua (id_A)`.
/// * `i = 0` and `i = 1`: total, so both ends are `A`, as a loop must be.
///
/// Note this is *not* regularity for `Glue`: `Glue [φ ↦ (A,id)] A` is not
/// definitionally `A`, and we do not pretend it is.  The square is a
/// genuine path between two distinct types that happens to be easy to
/// write down because all its faces agree.
///
/// ## The inductive step
///
/// `J` with motive `P(B,q) = Path (Path U A B) (ua (idtoeqv q)) q` carries
/// `D` to every line.  `J` is `coe` along the singleton contraction, so
/// the witness is *computed*, and because composition in a path type puts
/// the endpoints in the tube, the two ends of the result are the required
/// lines **definitionally** — a total tube fires and returns the wall.
pub fn ua_eta_base(a : Val) -> Val {
  let e = equiv_id(a)
  VPLam(DClo::{
    f: fn(rj) {
      VPLam(DClo::{
        f: fn(ri) {
          mk_glue_ty(
            [
              GlueBr::{ cof: @cubical.CEq(ri, 0), ty: a, eq: e, },
              GlueBr::{ cof: @cubical.CEq(ri, 1), ty: a, eq: e, },
              GlueBr::{ cof: @cubical.CEq(rj, 1), ty: a, eq: e, },
            ],
            a,
          )
        },
      })
    },
  })
}

///|
/// The `uaη` witness for an arbitrary line `p` with near endpoint `a`.
pub fn ua_eta_path(a : Val, p : Val) -> Val {
  let mot = fn(b : Val, q : Val) -> Val {
    path_ty(path_ty(VU, a, b), ua(idtoeqv(q)), q)
  }
  pathJ(mot, ua_eta_base(a), p)
}

///|
/// The same witness, with the near endpoint read off `p`.
pub fn ua_eta_general(p : Val) -> Val {
  ua_eta_path(vpapp(p, @cubical.DZero), p)
}
