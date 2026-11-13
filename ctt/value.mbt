///|
using @cubical {type Dim, type Cof, dim_and, dim_not, cof_and, cof_subst}

///|
/// # A computational cubical type theory
///
/// This package is a *kernel*, not a finite model.  Types are codes,
/// terms are values, and the Kan operations — composition, filling and
/// coercion — are **algorithms defined by structural recursion on the
/// type**, following Cohen–Coquand–Huber–Mörtberg.  Nothing searches a
/// space of elements: the lid of a box is *computed*.
///
/// The contrast with `cubical/` is deliberate.  There, a type is a finite
/// presheaf and `comp` enumerates its elements looking for a filler; that
/// is a decision procedure for a finite model.  Here, `comp` on `Π` is a
/// lambda, on `Σ` a pair, on `Path` a dimension abstraction, on `Glue` the
/// glue of a composed base, and on the universe a `Glue` type.  Those are
/// the defining equations of the Kan structure, and they run in time
/// proportional to the *type*, not to the number of its elements.
///
/// ## Binders
///
/// Term abstraction is `Clo`, dimension abstraction is `DClo`; both are
/// host closures.  A type *family* in a dimension is therefore a function
/// `Dim -> Val`, and every place the classical presentation writes a
/// substitution `A[i := r]` this kernel simply *re-applies the family*.
/// That is why no substitution operation on values is needed at all: the
/// only syntactic substitution is on dimensions and cofibrations, which
/// live in `cubical/interval.mbt`.
pub(all) enum Val {
  /// the universe
  VU
  /// a discrete finite type with `n` elements
  VFin(Int32)
  /// the natural numbers: a discrete type with infinitely many elements
  VNat
  /// dependent function space
  VPi(Val, Clo)
  /// dependent pair space
  VSig(Val, Clo)
  /// `Path (i.A) a b`, with `i` bound in the family
  VPath(DClo, Val, Val)
  /// `Glue [ψ ↦ (T, e)] A`
  VGlue(Val, Array[GlueBr])
  /// an element of `VFin n`
  VLit(Int32)
  /// `zero : Nat`
  VZero
  /// `suc n : Nat`
  VSuc(Val)
  /// a stuck case split on `Fin n`.  Keeping the scrutinee makes the term
  /// *natural in neutrals*, which a host-level pattern match is not.
  VSplit(Int32, Array[Val], Val)
  /// a stuck recursion on `Nat`: zero case, step, scrutinee
  VNatRec(Val, Clo, Val)
  /// the circle `S¹`, a HIT
  VCircle
  /// its point constructor
  VBase
  /// its path constructor `loop : Path base base`, at a stage
  VLoop(Dim)
  /// suspension of a type
  VSusp(Val)
  /// the two poles
  VNorth
  VSouth
  /// `merid a : Path north south`, at a stage
  VMerid(Val, Val, Dim)
  /// propositional truncation `∥A∥`
  VTrunc(Val)
  /// `inc : A → ∥A∥`
  VInc(Val)
  /// `sq : Π x y. Path x y`, at a stage
  VSq(Val, Val, Val, Dim)
  /// formal composition: the lid of a box in a HIT
  VHComp(Val, Tube, Val)
  /// a stuck circle recursion (target, point, loop, scrutinee)
  VCircRec(Val, Val, Val, Val)
  /// a stuck truncation recursion (target, map, prop witness, scrutinee)
  VTruncRec(Val, Val, Val, Val)
  /// a stuck suspension recursion (target, north, south, merid, scrutinee)
  VSuspRec(Val, Val, Val, Val, Val)
  /// coequalizer of `f, g : A → B`, carrying `B`, `f`, `g`
  VCoeq(Val, Val, Val)
  /// its point constructor `inc : B → Coeq f g`
  VCoeqInc(Val)
  /// its path constructor `rel a : Path (inc (f a)) (inc (g a))`, at a stage
  VCoeqRel(Val, Dim)
  /// a stuck coequalizer recursion (target, point map, path map, scrutinee)
  VCoeqRec(Val, Val, Val, Val)
  VLam(Clo)
  VPair(Val, Val)
  /// dimension abstraction `<i> v`
  VPLam(DClo)
  /// `glue [ψ ↦ t] a`
  VGlued(Array[GlueTm], Val)
  /// a neutral, used as a generic point when probing a family
  VNe(Int32)
}

///|
/// Term closure.
pub(all) struct Clo {
  f : (Val) -> Val
}

///|
/// Dimension closure: a value depending on one dimension.
pub(all) struct DClo {
  f : (Dim) -> Val
}

///|
/// One branch of a `Glue` type: on `ψ` the type is `T`, and `e : T ≃ A`.
///
/// The *whole* equivalence is stored, not just its forward map: the
/// composition algorithm needs `e⁻¹` on the face where `ψ` holds at the
/// far end but not at the near end.  This is the part of CCHM's Glue rule
/// that a forward-map-only implementation cannot express.
pub(all) struct GlueBr {
  cof : Cof
  ty : Val
  eq : Equiv
}

///|
/// One branch of a `glue` term: on `ψ` the element is `tm`.
pub(all) struct GlueTm {
  cof : Cof
  mut tm : Val
}

///|
/// A type family in the composition direction.
pub(all) struct Fam {
  f : (Dim) -> Val
}

///|
/// A tube: on each cofibration, a term depending on the composition
/// direction.  This is the `φ ↦ u` part of an open box.
pub(all) struct Tube {
  branches : Array[TubeBr]
}

///|
pub(all) struct TubeBr {
  cof : Cof
  tm : DClo
}

///|
pub fn Clo::new(f : (Val) -> Val) -> Clo {
  Clo::{ f, }
}

///|
pub fn DClo::new(f : (Dim) -> Val) -> DClo {
  DClo::{ f, }
}

///|
pub fn Fam::new(f : (Dim) -> Val) -> Fam {
  Fam::{ f, }
}

///|
/// The constant family at a type.
pub fn fam_const(ty : Val) -> Fam {
  Fam::{ f: fn(_) { ty }, }
}

///|
/// Reverse a family: `rev(A)(i) = A(~i)`.  Coercion from 1 to 0 is
/// coercion from 0 to 1 in the reversed family.
pub fn Fam::rev(self : Fam) -> Fam {
  Fam::{ f: fn(r) { self.at(dim_not(r)) }, }
}

///|
pub fn Tube::empty() -> Tube {
  Tube::{ branches: [], }
}

///|
pub fn Tube::add(self : Tube, cof : Cof, tm : DClo) -> Tube {
  let brs = self.branches[:].to_owned()
  brs.push(TubeBr::{ cof, tm, })
  Tube::{ branches: brs, }
}

///|
/// A tube branch that is constant in the composition direction.
pub fn tube_const(cof : Cof, v : Val) -> TubeBr {
  TubeBr::{ cof, tm: DClo::{ f: fn(_) { v }, }, }
}

///|
/// Apply a tube pointwise to an argument (used by `Π`).
pub fn Tube::app(self : Tube, x : DClo) -> Tube {
  let brs : Array[TubeBr] = []
  for b in self.branches {
    brs.push(TubeBr::{
      cof: b.cof,
      tm: DClo::{ f: fn(r) { vapp(b.tm.at(r), x.at(r)) }, },
    })
  }
  Tube::{ branches: brs, }
}

///|
/// Take the first component of every branch (used by `Σ`).
pub fn Tube::fst(self : Tube) -> Tube {
  let brs : Array[TubeBr] = []
  for b in self.branches {
    brs.push(TubeBr::{
      cof: b.cof,
      tm: DClo::{ f: fn(r) { vfst(b.tm.at(r)) }, },
    })
  }
  Tube::{ branches: brs, }
}

///|
pub fn Tube::snd(self : Tube) -> Tube {
  let brs : Array[TubeBr] = []
  for b in self.branches {
    brs.push(TubeBr::{
      cof: b.cof,
      tm: DClo::{ f: fn(r) { vsnd(b.tm.at(r)) }, },
    })
  }
  Tube::{ branches: brs, }
}

///|
/// Apply every branch at a dimension (used by `Path`).
pub fn Tube::at_dim(self : Tube, j : Dim) -> Tube {
  let brs : Array[TubeBr] = []
  for b in self.branches {
    brs.push(TubeBr::{
      cof: b.cof,
      tm: DClo::{ f: fn(r) { vpapp(b.tm.at(r), j) }, },
    })
  }
  Tube::{ branches: brs, }
}

///|
/// Unglue every branch (used by `Glue`).
pub fn Tube::unglue(self : Tube) -> Tube {
  let brs : Array[TubeBr] = []
  for b in self.branches {
    brs.push(TubeBr::{
      cof: b.cof,
      tm: DClo::{ f: fn(r) { unglue(b.tm.at(r)) }, },
    })
  }
  Tube::{ branches: brs, }
}

///|
/// Restrict a tube to a cofibration.
pub fn Tube::restrict(self : Tube, psi : Cof) -> Tube {
  let brs : Array[TubeBr] = []
  for b in self.branches {
    let c = cof_and(b.cof, psi)
    if !@cubical.cof_is_false(c) {
      brs.push(TubeBr::{ cof: c, tm: b.tm, })
    }
  }
  Tube::{ branches: brs, }
}

// --------------------------------------------------------------------
// Eliminators.  These are the strict computation rules of the theory.
// --------------------------------------------------------------------

///|

///|
/// Case split on `Fin n`.  On a literal it selects a branch; on anything
/// else it stays as a neutral split, so the term is natural in the
/// scrutinee and reads back correctly under a binder.
pub fn vsplit(n : Int32, branches : Array[Val], scrut : Val) -> Val {
  match scrut {
    VLit(k) =>
      if k >= 0 && k < n {
        branches[k]
      } else {
        abort("vsplit: range")
      }
    _ => VSplit(n, branches, scrut)
  }
}

///|
/// Recursion on `Nat`: `natrec z s zero = z`, `natrec z s (suc n) = s n`.
pub fn vnatrec(z : Val, s : Clo, scrut : Val) -> Val {
  // The computation rules are
  //   natrec z s zero    = z
  //   natrec z s (suc n) = s n (natrec z s n)
  // so the step sees both the predecessor and the recursive result.
  //
  // The constructor chain is walked *iteratively*: recursing in MoonBit
  // would put a stack-depth ceiling on the size of a numeral, which is
  // exactly the kind of hidden bound this kernel is meant not to have.
  let preds : Array[Val] = []
  let mut cur = scrut
  let mut acc = z
  let mut stuck = false
  while !stuck {
    match cur {
      VZero => break
      VSuc(n) => {
        preds.push(n)
        cur = n
      }
      _ => {
        acc = VNatRec(z, s, cur)
        stuck = true
      }
    }
  }
  let mut i = preds.length() - 1
  while i >= 0 {
    acc = vapp(s.at(preds[i]), acc)
    i = i - 1
  }
  acc
}

///|
/// The iterator: `natiter z f zero = z`, `natiter z f (suc n) = f (natiter z f n)`.
/// The recursor with the predecessor ignored.
pub fn vnatiter(z : Val, f : Clo, scrut : Val) -> Val {
  vnatrec(z, Clo::{ f: fn(_) { VLam(f) }, }, scrut)
}

///|
pub fn nat_lit(k : Int32) -> Val {
  let mut v = VZero
  for _ in 0..<k {
    v = VSuc(v)
  }
  v
}

///|
pub fn vapp(f : Val, a : Val) -> Val {
  match f {
    VLam(c) => c.at(a)
    VNe(_) => f
    _ => abort("vapp: not a function")
  }
}

///|
pub fn vfst(p : Val) -> Val {
  match p {
    VPair(a, _) => a
    VNe(_) => p
    _ => abort("vfst: not a pair")
  }
}

///|
pub fn vsnd(p : Val) -> Val {
  match p {
    VPair(_, b) => b
    VNe(_) => p
    _ => abort("vsnd: not a pair")
  }
}

///|
pub fn vpapp(p : Val, r : Dim) -> Val {
  match p {
    VPLam(c) => c.at(r)
    VNe(_) => p
    _ => abort("vpapp: not a path")
  }
}

///|
/// `unglue (glue [ψ ↦ t] a) = a`, strictly.  On a branch that is already
/// total the smart constructor has erased the glue, so this is only ever
/// the base component.
pub fn unglue(v : Val) -> Val {
  match v {
    VGlued(_, a) => a
    _ => v
  }
}

///|
/// **Smart constructor for `glue`.**  If a branch is total (`ψ = ⊤`) the
/// glued element *is* that branch's term, strictly.  This single rule is
/// what makes the endpoints of `ua` compute on the nose: at `i = 0` the
/// branch `(i = 0)` becomes `⊤`, so `ua(e)(0)` is literally `A`.
pub fn mk_glue(brs : Array[GlueTm], base : Val) -> Val {
  for b in brs {
    if @cubical.cof_is_true(b.cof) {
      return b.tm
    }
  }
  let live : Array[GlueTm] = []
  for b in brs {
    if !@cubical.cof_is_false(b.cof) {
      live.push(b)
    }
  }
  if live.length() == 0 {
    base
  } else {
    VGlued(live, base)
  }
}

///|
/// **Smart constructor for `Glue`.**  A total branch makes the type equal
/// to the glued type, strictly; this is the face rule of `Glue`.
pub fn mk_glue_ty(branches : Array[GlueBr], base : Val) -> Val {
  for b in branches {
    if @cubical.cof_is_true(b.cof) {
      return b.ty
    }
  }
  let live : Array[GlueBr] = []
  for b in branches {
    if !@cubical.cof_is_false(b.cof) {
      live.push(b)
    }
  }
  if live.length() == 0 {
    base
  } else {
    VGlue(base, live)
  }
}

///|
/// The `T`-part of an element of a `Glue` type on a branch.  On `ψ` the
/// element is literally the branch term; a `VGlued` whose branches do not
/// cover `ψ` cannot occur in a well-typed box.
pub fn glue_part(v : Val, psi : Cof) -> Val? {
  match v {
    VGlued(brs, _) => {
      for b in brs {
        if cof_entails(psi, b.cof) {
          return Some(b.tm)
        }
      }
      None
    }
    // a bare value: the glue was erased because the branch was total
    _ => Some(v)
  }
}

///|
/// Entailment of cofibrations, decided on the face lattice.  `n` is the
/// Decided structurally, by disjunctive normal form and join-primeness of
/// faces (`@cubical.cof_leq`).  There is **no bound on the number of
/// dimensions in scope**: an earlier version enumerated all `3^n` subcubes,
/// which capped the whole kernel at a handful of directions.
pub fn cof_entails(phi : Cof, psi : Cof) -> Bool {
  @cubical.cof_leq(phi, psi)
}

// --------------------------------------------------------------------
// Fresh dimensions.  The kernel allocates a fresh composition direction
// for every filler; a global counter keeps them apart.
// --------------------------------------------------------------------

///|
priv struct Fresh {
  mut next : Int32
}

///|
let fresh_dims : Fresh = Fresh::{ next: 100, }

///|
pub fn fresh_dim() -> Int32 {
  let i = fresh_dims.next
  fresh_dims.next = i + 1
  i
}

///|
/// Does a value mention the dimension `i`?  Closures are probed at a
/// fresh generic point, so this is a *sound* test for dependence: it may
/// report dependence that later cancels, which only costs us an
/// application of the regularity law, never correctness.
pub fn Val::mentions_dim(self : Val, i : Int32) -> Bool {
  mentions_bounded(self, i, 10)
}

///|
/// Bounded occurrence check.  Probing a closure *evaluates* it, so an
/// unbounded traversal of a deeply dependent type re-enters `comp` once per
/// binder and the cost multiplies at every level.  Past the bound the
/// answer is conservatively `true` ("may depend"), which only disables the
/// regularity shortcut — it never changes a result, because the shortcut
/// is an optimisation and the structural recursion is always sound.
fn mentions_bounded(v : Val, i : Int32, fuel : Int32) -> Bool {
  if fuel <= 0 {
    return true
  }
  let depth = fuel - 1
  match v {
    VU | VFin(_) | VNat | VLit(_) | VZero | VNe(_) => false
    VCircle | VBase | VNorth | VSouth => false
    VLoop(r) | VMerid(_, _, r) => r.mentions(i)
    VSq(_, x, y, r) =>
      r.mentions(i) ||
      mentions_bounded(x, i, depth) ||
      mentions_bounded(y, i, depth)
    VSusp(a) | VTrunc(a) | VInc(a) | VCoeqInc(a) =>
      mentions_bounded(a, i, depth)
    VCoeq(b, f, g) =>
      mentions_bounded(b, i, depth) ||
      mentions_bounded(f, i, depth) ||
      mentions_bounded(g, i, depth)
    VCoeqRel(a, r) => r.mentions(i) || mentions_bounded(a, i, depth)
    VCoeqRec(t, h, p, x) =>
      mentions_bounded(t, i, depth) ||
      mentions_bounded(h, i, depth) ||
      mentions_bounded(p, i, depth) ||
      mentions_bounded(x, i, depth)
    VHComp(ty, tube, cap) =>
      mentions_bounded(ty, i, depth) ||
      mentions_bounded(cap, i, depth) ||
      tube.mentions_dim(i, depth)
    VCircRec(t, b, l, x) =>
      mentions_bounded(t, i, depth) ||
      mentions_bounded(b, i, depth) ||
      mentions_bounded(l, i, depth) ||
      mentions_bounded(x, i, depth)
    VTruncRec(t, f, pr, x) =>
      mentions_bounded(t, i, depth) ||
      mentions_bounded(f, i, depth) ||
      mentions_bounded(pr, i, depth) ||
      mentions_bounded(x, i, depth)
    VSuspRec(t, n, st, m, x) =>
      mentions_bounded(t, i, depth) ||
      mentions_bounded(n, i, depth) ||
      mentions_bounded(st, i, depth) ||
      mentions_bounded(m, i, depth) ||
      mentions_bounded(x, i, depth)
    VSuc(n) => mentions_bounded(n, i, depth)
    VSplit(_, brs, sc) => {
      if mentions_bounded(sc, i, depth) {
        return true
      }
      for b in brs {
        if mentions_bounded(b, i, depth) {
          return true
        }
      }
      false
    }
    VNatRec(z, step, sc) =>
      mentions_bounded(z, i, depth) ||
      mentions_bounded(sc, i, depth) ||
      mentions_bounded(step.at(VNe(fresh_dim())), i, depth)
    VPi(a, c) | VSig(a, c) =>
      mentions_bounded(a, i, depth) ||
      mentions_bounded(c.at(VNe(fresh_dim())), i, depth)
    VPath(fam, a, b) =>
      mentions_bounded(fam.at(@cubical.DVar(fresh_dim())), i, depth) ||
      mentions_bounded(a, i, depth) ||
      mentions_bounded(b, i, depth)
    VGlue(a, brs) => {
      if mentions_bounded(a, i, depth) {
        return true
      }
      for b in brs {
        if b.cof.mentions(i) ||
          mentions_bounded(b.ty, i, depth) ||
          mentions_bounded(vapp(b.eq.fwd, VNe(fresh_dim())), i, depth) {
          return true
        }
      }
      false
    }
    VLam(c) => mentions_bounded(c.at(VNe(fresh_dim())), i, depth)
    VPair(a, b) =>
      mentions_bounded(a, i, depth) || mentions_bounded(b, i, depth)
    VPLam(c) => mentions_bounded(c.at(@cubical.DVar(fresh_dim())), i, depth)
    VGlued(brs, a) => {
      if mentions_bounded(a, i, depth) {
        return true
      }
      for b in brs {
        if b.cof.mentions(i) || mentions_bounded(b.tm, i, depth) {
          return true
        }
      }
      false
    }
  }
}

///|
/// Is a family constant in the direction `i`?  This is the hypothesis of
/// the **regularity** law `coe^{r→r'} (i.A) a = a` for constant `A`, and
/// deciding it is what lets the kernel return the cap untouched instead
/// of rebuilding it.
pub fn Fam::is_constant(self : Fam, i : Int32) -> Bool {
  // Probe at the direction *itself*: instantiating at a fresh variable
  // would substitute away the very dependence being tested.
  !mentions_bounded(self.at(@cubical.DVar(i)), i, 10)
}

///|
/// Apply a term closure.
pub fn Clo::at(self : Clo, v : Val) -> Val {
  (self.f)(v)
}

///|
/// Apply a dimension closure.
pub fn DClo::at(self : DClo, r : Dim) -> Val {
  (self.f)(r)
}

///|
/// Apply a type family at a stage.
pub fn Fam::at(self : Fam, r : Dim) -> Val {
  (self.f)(r)
}

///|
/// # Memoisation of dimension closures
///
/// A `DClo` built by `coe_to` / `fill` *recomputes an entire composition*
/// every time it is applied.  The kernel probes closures at a handful of
/// dimensions — `0`, `1`, and the current direction — and the `Glue` rule
/// probes the same filler at the same dimension once per branch, per
/// level.  Without sharing, the cost multiplies at every Glue layer and a
/// composite path exhausts memory.
///
/// This cell caches the result per dimension.  It is pure memoisation of a
/// deterministic function: it changes no normal form, only the number of
/// times one is computed.
priv struct DCloCell {
  slots : Map[String, Val]
  f : (Dim) -> Val
}

///|
pub fn memo_dclo(d : DClo) -> DClo {
  let cell = DCloCell::{ slots: Map([]), f: d.f, }
  DClo::{
    f: fn(r) {
      let k = dim_render(r)
      match cell.slots.get(k) {
        Some(v) => v
        None => {
          let v = (cell.f)(r)
          cell.slots[k] = v
          v
        }
      }
    },
  }
}

///|
pub fn memo_fam(fam : Fam) -> Fam {
  let d = memo_dclo(DClo::{ f: fam.f, })
  Fam::{ f: fn(r) { d.at(r) }, }
}

///|
/// # The discrete function space `Fin n → A`
///
/// A function out of a finite type is its table, but the table must be
/// *natural in neutrals*: applied to a variable it has to become a stuck
/// case split, not the variable itself.  An earlier version returned the
/// scrutinee on any non-literal, which silently identified every function
/// `Fin n → Fin n` with the identity as soon as the argument was neutral —
/// so `neg ∘ neg` and `id` compared equal for the wrong reason, and any
/// theorem proved under a binder was vacuous.
///
/// With `vsplit` the split stays, reads back with its scrutinee named, and
/// still computes on literals.  This is what makes `fin_fun` usable inside
/// the kernel rather than only in tests.
pub fn fin_fun_vals(vals : Array[Val]) -> Val {
  let n = vals.length()
  VLam(Clo::{ f: fn(x) { vsplit(n, vals, x) }, })
}

///|
/// The table of a function `Fin n → Fin m`, as literal values.
pub fn fin_fun(table : Array[Int32]) -> Val {
  let vals : Array[Val] = []
  for v in table {
    vals.push(VLit(v))
  }
  fin_fun_vals(vals)
}

///|
/// Does a tube mention a direction?  Used by the occurrence check on a
/// formal composition, whose walls are dimension closures.
fn Tube::mentions_dim(self : Tube, i : Int32, fuel : Int32) -> Bool {
  for br in self.branches {
    if br.cof.mentions(i) ||
      mentions_bounded(br.tm.at(@cubical.DVar(fresh_dim())), i, fuel) {
      return true
    }
  }
  false
}
