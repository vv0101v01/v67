///|
/// # Internally symmetric cubical structure
///
/// A cubical set is *symmetric* when the interval carries an involution
/// and the whole structure is closed under it.  The involution is already
/// present as `~` on dimensions; what makes it **internal** is that every
/// level of the kernel is closed under it and the closure is an
/// *operation*, not a metatheoretic remark:
///
/// | level | reversal | law |
/// |---|---|---|
/// | dimension | `dim_not` | `~~r = r`, `~(r∧s) = ~r ∨ ~s` |
/// | cofibration | `cof_rev` | `(r=e)` ↦ `(r=1-e)`, a lattice automorphism |
/// | family | `Fam::rev` | `A(~~i) = A(i)` |
/// | tube | `Tube::rev` | walls reversed, faces reversed |
/// | composition | `comp_rev` | lid of the reversed box |
/// | path | `path_sym` | `sym (sym p) = p` |
/// | equivalence | `equiv_inv` | `(e⁻¹)⁻¹ = e` |
/// | univalence | `ua_sym` | `ua(e⁻¹)` and `sym (ua e)` have the same transport |
///
/// The last row is the one with content.  `ua(e)` is
/// `Glue [(i=0) ↦ (A,e), (i=1) ↦ (B,id)] B`; reversing it swaps which end
/// carries `e`, while `ua(e⁻¹)` is
/// `Glue [(i=0) ↦ (B,e⁻¹), (i=1) ↦ (A,id)] A`.  The two are **not**
/// definitionally equal — different base, different branch data — but they
/// are the same path up to homotopy, and in particular they induce the
/// same transport.  Symmetry of univalence is therefore a theorem about
/// the construction, not a definitional accident.
///
/// ## Why reversal is not free
///
/// In a *De Morgan* interval `~i ∨ i ≠ 1` and `~i ∧ i ≠ 0`: the boundary of
/// the interval is not the whole interval, and a point is not forced to be
/// an endpoint.  So `interp(r,r,i) = (r ∧ ~i) ∨ (r ∧ i)` does not fold to
/// `r`, and reversal alone cannot give regularity on the diagonal.  The
/// symmetric structure and the bidirectional structure are genuinely
/// independent: symmetry reverses, it does not interpolate.

///|
/// Reverse a cofibration: the lattice automorphism induced by `~`.
///
/// `(r = e)` becomes `(r = 1-e)`; `∧` and `∨` are preserved because `~` is
/// a De Morgan involution, so this is exactly relabelling the endpoints.
pub fn cof_rev(phi : Cof) -> Cof {
  match phi {
    @cubical.CTop => @cubical.CTop
    @cubical.CBot => @cubical.CBot
    @cubical.CEq(r, e) => @cubical.CEq(r, 1 - e)
    @cubical.CAnd(a, b) => @cubical.CAnd(cof_rev(a), cof_rev(b))
    @cubical.COr(a, b) => @cubical.COr(cof_rev(a), cof_rev(b))
  }
}

///|
/// Reverse a tube: each wall runs backwards, and each face is relabelled.
pub fn Tube::rev(self : Tube) -> Tube {
  let brs : Array[TubeBr] = []
  for b in self.branches {
    let tm = b.tm
    brs.push(TubeBr::{
      cof: cof_rev(b.cof),
      tm: memo_dclo(DClo::{ f: fn(i) { tm.at(dim_not(i)) }, }),
    })
  }
  Tube::{ branches: brs, }
}

///|
/// # Composition in the reversed direction
///
/// `comp_rev A [φ ↦ u] a₀` composes from `1` to `0`.  Two derivations must
/// agree, and the tests check that they do:
///
/// 1. bidirectional: `comp^{1→0}`, i.e. reindex along `interp(1,0,i) = ~i`;
/// 2. symmetric: reverse the family, the tube and the faces, compose
///    forwards, and read the result — `comp^i (A ∘ ~) [~φ ↦ u ∘ ~] a₀`.
///
/// Their agreement is the statement that the Kan structure is *equivariant*
/// for the involution, which is what "internally symmetric" means.
pub fn comp_rev(fam : Fam, tube : Tube, cap : Val) -> Val {
  comp_between(fam, @cubical.DOne, @cubical.DZero, tube, cap)
}

///|
/// The same lid, computed by reversing everything and composing forwards.
pub fn comp_sym(fam : Fam, tube : Tube, cap : Val) -> Val {
  comp(fam.rev(), fresh_dim(), tube.rev(), cap)
}

///|
/// Filling in the reversed direction.
pub fn fill_rev(fam : Fam, tube : Tube, cap : Val) -> DClo {
  fill_between(fam, @cubical.DOne, @cubical.DZero, tube, cap)
}

///|
/// # The involution on paths, as an equivalence
///
/// `sym : Path A x y ≃ Path A y x`.  It is a *strict* involution: the
/// forward and backward maps are the same program, and both round trips
/// are the identity on the nose, because `~~i` folds to `i`.
pub fn sym_equiv(a : Val, x : Val, y : Val) -> Equiv {
  let src = path_ty(a, x, y)
  let tgt = path_ty(a, y, x)
  let f = VLam(Clo::{ f: fn(p) { path_sym(p) }, })
  Equiv::new(src, tgt, f, f)
}

///|
/// # Symmetry of univalence
///
/// `ua(e⁻¹)` and `sym (ua e)` are both paths `B → A`.  This returns the
/// pair; the theorem checked in the tests is that they have the same
/// endpoints and the same transport, for every element of `B`.
pub fn ua_sym(e : Equiv) -> (Val, Val) {
  (ua(equiv_inv(e)), path_sym(ua(e)))
}

///|
/// Transport along a reversed path is the backward coercion of the
/// original — the compatibility of symmetry with 投遞.
pub fn transport_sym(p : Val, b : Val) -> Val {
  coe_between(path_fam(p), @cubical.DOne, @cubical.DZero, b)
}
