///|
/// # Transport is an equivalence — proved, not assumed
///
/// For a line of types `p : Path U A B`, the two round trips
/// `coe p (coe⁻¹ p y) = y` and `coe⁻¹ p (coe p x) = x` are **not**
/// definitional.  They are theorems, and the cubical proof is path
/// induction: at `p = refl` both sides are literally `y`, and `J`
/// transports that along the singleton contraction.
///
/// The same induction produces the **fibre contraction** that CCHM's
/// `Equiv` requires.  So `idtoeqv p` is a full equivalence for *every*
/// line `p`, with no strictness hypothesis anywhere.

///|
/// # The round trip, by one composition
///
/// Let `A(i)` be the line and `y : A(1)`.  Put
///
/// ```text
/// u(i) = coe^{1→i} A y      u(1) = y,          u(0) = bwd y
/// v(i) = coe^{0→i} A (u 0)  v(0) = u(0),       v(1) = fwd (bwd y)
/// ```
///
/// The two lines agree at `i = 0`, so
///
/// ```text
/// β y j = comp^i A [(j=0) ↦ v(i), (j=1) ↦ u(i)] (u 0)
/// ```
///
/// is a well-formed box whose lid at `j = 0` is `v(1) = fwd (bwd y)` and at
/// `j = 1` is `u(1) = y`.  That is the retraction homotopy, in **one**
/// composition — no path induction, no nested motive.
///
/// The other round trip is the same construction in the reversed line:
/// `α x = β_{A(~i)} x`.  An earlier version used `J` for both, whose motive
/// mentions `isContr` of a fibre; forcing it recursed through every Glue
/// layer and overflowed the stack on a composite line.
pub fn transport_beta(fam : Fam, y : Val) -> Val {
  let u = coe_back_to(fam, 0, y)
  let u0 = u.at(@cubical.DZero)
  let v = coe_to(fam, 0, u0)
  VPLam(DClo::{
    f: fn(rj) {
      let tube = Tube::{
        branches: [
          TubeBr::{ cof: @cubical.CEq(rj, 0), tm: v, },
          TubeBr::{ cof: @cubical.CEq(rj, 1), tm: u, },
        ],
      }
      comp(fam, 0, tube, u0)
    },
  })
}

///|
/// The round-trip homotopy.  `forward_first` selects `fwd ∘ bwd = id`
/// (over the far end) or `bwd ∘ fwd = id` (over the near end).
pub fn transport_roundtrip(p : Val, y : Val, forward_first : Bool) -> Val {
  let fam = path_fam(p)
  if forward_first {
    transport_beta(fam, y)
  } else {
    transport_beta(fam.rev(), y)
  }
}

///|
/// The round-trip homotopy as a function.
pub fn roundtrip_fun(p : Val, forward_first : Bool) -> Val {
  VLam(Clo::{ f: fn(y) { transport_roundtrip(p, y, forward_first) }, })
}

///|
/// # The fibre of a transport is a transported co-singleton
///
/// ```text
/// B(i) = Σ(z : A(i)). Path (A(1)) (coe^{i→1} A z) y
/// ```
///
/// * At `i = 1` the inner coercion is the identity, so `B(1)` is the
///   co-singleton `Σ(z:A(1)). Path z y`: centre `(y, refl y)`, contraction
///   the closed form `j ↦ (q(~j), <k> q(~j ∨ k))`.
/// * At `i = 0` it is exactly `fib (coe A) y`.
///
/// Coercing that structure backwards along `B` therefore *is* the centre,
/// the section homotopy and the contraction of the fibre of `coe A` — one
/// composition instead of path induction over an `isContr` motive.
///
/// `coe^{i→1}` needs no new primitive: `s ↦ A(i ∨ s)` is a line from
/// `A(i)` to `A(1)`, so the join connection expresses it.
fn fiber_line(fam : Fam, y : Val) -> Fam {
  let far = fam.at(@cubical.DOne)
  memo_fam(Fam::{
    f: fn(r) {
      VSig(fam.at(r), Clo::{
        f: fn(z) {
          let up = Fam::{ f: fn(t) { fam.at(@cubical.dim_or(r, t)) }, }
          path_ty(far, coe(up, 0, z), y)
        },
      })
    },
  })
}

///|
/// The centre of `fib (coe p) y` together with its section homotopy,
/// obtained by dragging `(y, refl y)` back along `B`.
pub fn transport_center(p : Val, y : Val) -> Val {
  coe_back(fiber_line(path_fam(p), y), 0, VPair(y, refl(y)))
}

///|
/// # The contraction of the fibre of a transport
///
/// Drag the co-singleton's contraction back along `B`, the fibre line.
///
/// Fix `z = (x, q)` in `fib (coe p) y = B(0)`.  Two lines in `B`:
///
/// ```text
/// ctr(i) = coe^{1→i} B (y, refl y)     ctr(1) = (y, refl y),  ctr(0) = centre
/// zz(i)  = coe^{0→i} B z               zz(0)  = z,            zz(1)  = z₁
/// ```
///
/// At `i = 1` the fibre is the co-singleton, so the closed form gives
/// `h₁ : Path (B 1) (ctr 1) z₁`.  Coercing `h₁` back along the **path-type**
/// family `i ↦ Path (B i) (ctr i) (zz i)` lands in
/// `Path (B 0) centre z` — the contraction, at `z`.
///
/// Coercing a *path* family rather than the Π-family
/// `i ↦ Π(w : B i). Path (ctr i) w` matters: composition in a path type is
/// pointwise, so the endpoints stay instantiated.  The Π version forced
/// `comp_pi` to probe a filler under a binder and the composition
/// direction leaked into the result.
pub fn transport_contr(p : Val) -> Contr {
  let fam = path_fam(p)
  let base_id = VLam(Clo::{ f: fn(z) { z }, })
  Contr::{
    f: fn(y, x, q) {
      let b = fiber_line(fam, y)
      let z = VPair(x, q)
      let ctr = coe_back_to(b, 0, VPair(y, refl(y)))
      let zz = coe_to(b, 0, z)
      let z1 = zz.at(@cubical.DOne)
      let h1 = (contr_iso(base_id).f)(y, vfst(z1), vsnd(z1))
      let pf = Fam::{ f: fn(r) { path_ty(b.at(r), ctr.at(r), zz.at(r)) }, }
      coe_back(pf, 0, h1)
    },
  }
}
