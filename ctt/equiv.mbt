///|
/// # Equivalences, as CCHM defines them
///
/// ```text
/// Equiv T A  :=  Σ(f : T → A). Π(a : A). isContr (fib f a)
/// fib f a    :=  Σ(t : T). Path A (f t) a
/// ```
///
/// The contraction of the fibre is **data**, not a property to be
/// discovered.  That is the whole reason CCHM's `Glue` rule can be
/// written at all: on the face where the glued type appears only at the
/// far end, the algorithm must produce a `T`-element over a given
/// `A`-element, and it does so by *contracting the fibre*.
///
/// An earlier version of this kernel stored only `fwd` and `bwd` and
/// therefore had to assume both round trips were definitionally the
/// identity.  That assumption is gone: `contr` is a field, `equiv` uses
/// it, and any equivalence — strict or not — can be glued.
pub(all) struct Contr {
  /// `(a, t, p) ↦` a path in `fib f a` from the centre `(bwd a, β a)`
  ///| to `(t, p)`.
  f : (Val, Val, Val) -> Val
}

///|
pub(all) struct Equiv {
  src : Val
  tgt : Val
  fwd : Val
  bwd : Val
  /// `α t : Path T (bwd (fwd t)) t`
  alpha : Clo
  /// `β a : Path A (fwd (bwd a)) a`
  beta : Clo
  /// contractibility of every fibre — the actual CCHM datum
  contr : Contr
  /// Both round trips are definitionally the identity.  When this holds
  ///| the centre of every fibre already extends the partial data the
  ///| `Glue` rule produces, so `equiv` can return it without touching
  ///| `contr`.  A flag, not a readback: testing convertibility inside the
  ///| kernel is re-entrant and its cost explodes on nested `Glue`s.
  strict : LazyBool
}

///|
/// The fibre `Σ(t:T). Path A (f t) a`, as a type of the kernel.
pub fn Equiv::fiber(self : Equiv, a : Val) -> Val {
  VSig(self.src, Clo::{
    f: fn(t) { VPath(dclo_const(self.tgt), vapp(self.fwd, t), a) },
  })
}

///|
/// The centre of the fibre over `a`: `(bwd a, β a)`.
pub fn Equiv::center(self : Equiv, a : Val) -> Val {
  VPair(vapp(self.bwd, a), self.beta.at(a))
}

///|
/// # `equiv`: extending a partial element of a fibre
///
/// ```text
/// equiv e [ψ ↦ (t, p)] a  :  fib e a,   equal to (t, p) on ψ
/// ```
///
/// Implemented by **composition in the fibre type**:
///
/// ```text
/// equiv e [ψ ↦ (t,p)] a  =  comp^k (fib e a) [ψ ↦ contr(a,t,p)(k)] (bwd a, β a)
/// ```
///
/// The box is well formed because `contr(a,t,p)(0)` *is* the centre, and
/// the lid agrees with `contr(a,t,p)(1) = (t,p)` on `ψ`.  So contractibility
/// of the fibre turns directly into the extension property the `Glue`
/// rule needs.  No search, no strictness assumption.
pub fn equiv(
  e : Equiv,
  a : Val,
  partial : Array[(Cof, Val, Val)],
) -> (Val, Val) {
  // Nothing to extend: the centre already is the answer.  Returning here
  // avoids forcing the contraction at all, which for a J-built
  // contraction is the difference between constant time and a deep
  // recursion through every Glue layer of the line.
  let mut any = false
  for (psi, _, _) in partial {
    if !@cubical.cof_is_false(psi) {
      any = true
    }
  }
  let ctr = e.center(a)
  let ct = vfst(ctr)
  let cp = vsnd(ctr)
  if !any {
    return (ct, cp)
  }
  // A strict isomorphism: the centre extends the partial data, because
  // `bwd (fwd t) ≡ t` and `β ≡ refl` hold definitionally.
  if e.strict.get() {
    return (ct, cp)
  }
  let k = fresh_dim()
  let brs : Array[TubeBr] = []
  for (psi, t, p) in partial {
    if @cubical.cof_is_false(psi) {
      continue
    }
    brs.push(TubeBr::{
      cof: psi,
      tm: DClo::{ f: fn(r) { vpapp((e.contr.f)(a, t, p), r) }, },
    })
  }
  let res = comp(fam_const(e.fiber(a)), k, Tube::{ branches: brs, }, ctr)
  (vfst(res), vsnd(res))
}

///|
/// The contraction for a **strict isomorphism**, in closed form:
///
/// ```text
/// contr(a,t,p)(j) = ( bwd (p (~j)) , <k> p (k ∨ ~j) )
/// ```
///
/// At `j = 0` this is `(bwd a, refl a)`, the centre; at `j = 1` it is
/// `(bwd (f t), p) = (t, p)` by the strict retraction.  The second
/// component is a path from `f (bwd (p (~j))) = p (~j)` to `a`, which is
/// exactly what `k ↦ p (k ∨ ~j)` gives.  Only `~` and `∨` are used.
pub fn contr_iso(e_fwd_bwd : Val) -> Contr {
  Contr::{
    f: fn(_a, t, p) {
      let _ = t
      VPLam(DClo::{
        f: fn(r) {
          VPair(
            vapp(e_fwd_bwd, vpapp(p, dim_not(r))),
            VPLam(DClo::{
              f: fn(s) { vpapp(p, @cubical.dim_or(s, dim_not(r))) },
            }),
          )
        },
      })
    },
  }
}

///|
/// Build a strict isomorphism: both round trips are definitional, so the
/// homotopies are `refl` and the contraction is `contr_iso`.
pub fn Equiv::new(src : Val, tgt : Val, fwd : Val, bwd : Val) -> Equiv {
  Equiv::{
    src,
    tgt,
    fwd,
    bwd,
    alpha: strict_hom(),
    beta: strict_hom(),
    contr: contr_iso(bwd),
    strict: lazy_true(),
  }
}

///|
/// Build an equivalence from a map, a quasi-inverse, two homotopies and
/// **a supplied fibre contraction**.  Nothing here is required to be
/// definitional: this is the general CCHM constructor.
pub fn Equiv::with_contr(
  src : Val,
  tgt : Val,
  fwd : Val,
  bwd : Val,
  alpha : Clo,
  beta : Clo,
  contr : Contr,
) -> Equiv {
  Equiv::{ src, tgt, fwd, bwd, alpha, beta, contr, strict: lazy_false(), }
}

///|
fn strict_hom() -> Clo {
  Clo::{ f: fn(x) { refl(x) }, }
}

///|
/// The identity equivalence.  Its fibre is the singleton, and the closed
/// form above is exactly the singleton contraction.
pub fn equiv_id(a : Val) -> Equiv {
  let f = VLam(Clo::{ f: fn(x) { x }, })
  Equiv::{
    src: a,
    tgt: a,
    fwd: f,
    bwd: f,
    alpha: strict_hom(),
    beta: strict_hom(),
    contr: contr_iso(f),
    strict: lazy_true(),
  }
}

///|
/// Composition of equivalences.  For strict isomorphisms the composite is
/// again strict, so `contr_iso` applies; the general case is
/// `Equiv::with_contr`.
pub fn equiv_comp(f : Equiv, g : Equiv) -> Equiv {
  let fwd = VLam(Clo::{ f: fn(x) { vapp(g.fwd, vapp(f.fwd, x)) }, })
  let bwd = VLam(Clo::{ f: fn(x) { vapp(f.bwd, vapp(g.bwd, x)) }, })
  Equiv::{
    src: f.src,
    tgt: g.tgt,
    fwd,
    bwd,
    alpha: strict_hom(),
    beta: strict_hom(),
    contr: contr_iso(bwd),
    strict: lazy_true(),
  }
}

///|
pub fn equiv_inv(e : Equiv) -> Equiv {
  Equiv::{
    src: e.tgt,
    tgt: e.src,
    fwd: e.bwd,
    bwd: e.fwd,
    alpha: e.beta,
    beta: e.alpha,
    contr: contr_iso(e.fwd),
    strict: e.strict,
  }
}

///|
/// Verify the two triangle identities by readback on probes.
pub fn Equiv::check(
  self : Equiv,
  probes : Array[Val],
  back : Array[Val],
) -> Bool {
  for x in probes {
    if quote_norm(vapp(self.bwd, vapp(self.fwd, x)), 10) != quote_norm(x, 10) {
      return false
    }
  }
  for y in back {
    if quote_norm(vapp(self.fwd, vapp(self.bwd, y)), 10) != quote_norm(y, 10) {
      return false
    }
  }
  true
}

///|
/// Verify that `contr` really is a fibre contraction: its two ends are the
/// centre and the given point, and its second component really is a path
/// from `f` of the first to `a`.  Checked on concrete probes.
pub fn Equiv::check_contr(self : Equiv, a : Val, t : Val, p : Val) -> Bool {
  let c = (self.contr.f)(a, t, p)
  let at0 = vpapp(c, @cubical.DZero)
  let at1 = vpapp(c, @cubical.DOne)
  quote_norm(at0, 10) == quote_norm(self.center(a), 10) &&
  quote_norm(at1, 10) == quote_norm(VPair(t, p), 10) &&
  quote_norm(vpapp(vsnd(at1), @cubical.DZero), 10) ==
  quote_norm(vapp(self.fwd, t), 10) &&
  quote_norm(vpapp(vsnd(at1), @cubical.DOne), 10) == quote_norm(a, 10)
}

///|
/// A memo cell for a lazily built contraction.
///
/// `comp` in the universe produces an equivalence whose contraction is
/// obtained by `J`.  Building it runs a coercion, which can itself reach a
/// `Glue` and ask for another contraction — so it must be built at most
/// once per branch and then shared.  Without this cell the same `J` was
/// re-run on every application and the cost exploded.
priv struct ContrCell {
  mut cached : Contr?
}

///|
pub fn lazy_contr(mk : () -> Contr) -> Contr {
  let cell = ContrCell::{ cached: None, }
  Contr::{
    f: fn(y, x, q) {
      let c = match cell.cached {
        Some(c) => c
        None => {
          let built = mk()
          cell.cached = Some(built)
          built
        }
      }
      (c.f)(y, x, q)
    },
  }
}

///|
/// A memo cell for a lazily built term-valued function.
priv struct CloCell {
  mut cached : Clo?
}

///|
pub fn lazy_clo(mk : () -> Clo) -> Clo {
  let cell = CloCell::{ cached: None, }
  Clo::{
    f: fn(x) {
      let c = match cell.cached {
        Some(c) => c
        None => {
          let built = mk()
          cell.cached = Some(built)
          built
        }
      }
      c.at(x)
    },
  }
}

///|
/// A memoised, lazily forced Boolean.
struct BoolCell {
  mut cached : Bool?
  mk : () -> Bool
}

///|
pub struct LazyBool {
  cell : BoolCell
}

///|
pub fn LazyBool::get(self : LazyBool) -> Bool {
  match self.cell.cached {
    Some(b) => b
    None => {
      let b = (self.cell.mk)()
      self.cell.cached = Some(b)
      b
    }
  }
}

///|
pub fn lazy_bool(mk : () -> Bool) -> LazyBool {
  LazyBool::{ cell: BoolCell::{ cached: None, mk, }, }
}

///|
pub fn lazy_true() -> LazyBool {
  lazy_bool(fn() { true })
}

///|
pub fn lazy_false() -> LazyBool {
  lazy_bool(fn() { false })
}
