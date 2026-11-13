///|
/// # Contractible types have contractible path spaces
///
/// This is the step that makes `isProp → isSet` go through, and it is a
/// genuinely two-dimensional argument: the tube of the composition below
/// lives in *two* directions at once.
///
/// Let `(c, h)` contract `A`, and let `x y : A`.
///
/// **Centre.** `ctr = <i> comp^k A [(i=0) ↦ h x k, (i=1) ↦ h y k] c`,
/// a path from `x` to `y` (at `i=0` the tube is total and gives `h x 1 = x`).
///
/// **Contraction.** Given `p : Path A x y`, two squares over `(i,k)` share
/// three faces:
///
/// ```text
///   S i k = h (p i) k        S i 0 = c   S i 1 = p i    S 0 k = h x k   S 1 k = h y k
///   F i k = fill^k A [(i=0) ↦ h x k, (i=1) ↦ h y k] c
///                            F i 0 = c   F i 1 = ctr i  (same sides)
/// ```
///
/// `S` is a filler whose top face is `p`; `F` is the canonical filler whose
/// top face is `ctr`.  Composing in `k` with *both* squares in the tube,
///
/// ```text
/// Q j i = comp^k A [ (i=0) ↦ h x k, (i=1) ↦ h y k,
///                    (j=0) ↦ F i k, (j=1) ↦ S i k ] c
/// ```
///
/// gives `Q 0 = ctr`, `Q 1 = p`, `Q j 0 = x`, `Q j 1 = y` — a path of paths.
/// The box is well formed because all four branches equal `c` at `k = 0`.
pub fn contr_path_contr(a : Val, ctr : Val, x : Val, y : Val) -> Val {
  let c = vfst(ctr)
  let h = vsnd(ctr)
  let hx = vapp(h, x)
  let hy = vapp(h, y)
  // the two side branches, shared by the centre and by the contraction
  let sides = fn(ri : Dim) -> Array[TubeBr] {
    [
      TubeBr::{
        cof: @cubical.CEq(ri, 0),
        tm: DClo::{ f: fn(r) { vpapp(hx, r) }, },
      },
      TubeBr::{
        cof: @cubical.CEq(ri, 1),
        tm: DClo::{ f: fn(r) { vpapp(hy, r) }, },
      },
    ]
  }
  let center_path = VPLam(DClo::{
    f: fn(ri) {
      let k = fresh_dim()
      comp(fam_const(a), k, Tube::{ branches: sides(ri), }, c)
    },
  })
  let contraction = VLam(Clo::{
    f: fn(p) {
      VPLam(DClo::{
        f: fn(rj) {
          VPLam(DClo::{
            f: fn(ri) {
              let k = fresh_dim()
              // F: the canonical filler, top face is the centre path
              let fk = fill(
                fam_const(a),
                fresh_dim(),
                Tube::{ branches: sides(ri), },
                c,
              )
              let brs = sides(ri)
              brs.push(TubeBr::{
                cof: @cubical.CEq(rj, 0),
                tm: DClo::{ f: fn(r) { fk.at(r) }, },
              })
              brs.push(TubeBr::{
                cof: @cubical.CEq(rj, 1),
                tm: DClo::{ f: fn(r) { vpapp(vapp(h, vpapp(p, ri)), r) }, },
              })
              comp(fam_const(a), k, Tube::{ branches: brs, }, c)
            },
          })
        },
      })
    },
  })
  VPair(center_path, contraction)
}

///|
/// A pointed proposition is contractible.
pub fn prop_to_contr(f : Val, x : Val) -> Val {
  VPair(x, VLam(Clo::{ f: fn(z) { vapp(vapp(f, x), z) }, }))
}

///|
/// # `isProp A → isSet A`
///
/// `A` a proposition and `x : A` gives `isContr A`; that gives
/// `isContr (Path A x y)` by the construction above; and a contractible
/// type is a proposition.  Composing the three is the whole proof, and
/// every step is a program.
pub fn is_prop_to_set(a : Val, f : Val) -> Val {
  VLam(Clo::{
    f: fn(x) {
      VLam(Clo::{
        f: fn(y) {
          let ctr = prop_to_contr(f, x)
          let cp = contr_path_contr(a, ctr, x, y)
          contr_to_prop(path_ty(a, x, y), cp)
        },
      })
    },
  })
}
