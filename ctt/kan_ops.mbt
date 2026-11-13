///|
/// # The Kan operations, bidirectional
///
/// `comp`, `fill` and `coe` in `kan.mbt` run from stage `0` to stage `1`.
/// That is enough to state univalence, but it is not the structure a
/// cubical set actually has: the interval is an *interval object*, and
/// every operation is defined between **any two stages** `r` and `r'`, in
/// either direction, naturally in both.
///
/// This file gives those operations, derived from the directed ones by a
/// single device — the interpolation line.
///
/// ## The interpolation line
///
/// ```text
/// interp(r, r', i) = (r ∧ ~i) ∨ (r' ∧ i)
/// ```
///
/// At `i = 0` it is `(r ∧ 1) ∨ (r' ∧ 0) = r`; at `i = 1` it is
/// `(r ∧ 0) ∨ (r' ∧ 1) = r'`.  So it is a dimension term whose endpoints
/// are `r` and `r'`, built from the two connections and the reversal.
/// Reindexing a family along it turns "from `r` to `r'`" into "from `0` to
/// `1`", which the directed kernel already handles:
///
/// ```text
/// coe^{r→r'} A a = comp^i (i ↦ A(interp(r,r',i))) [] a
/// ```
///
/// Specialising recovers exactly the directed operations, *definitionally*:
///
/// * `interp(0,1,i) = (0 ∧ ~i) ∨ (1 ∧ i) = i`, so `coe^{0→1} = coe`;
/// * `interp(1,0,i) = (1 ∧ ~i) ∨ (0 ∧ i) = ~i`, so `coe^{1→0} = coe_back`.
///
/// The constant-folding in `dim_and` / `dim_or` is what makes those two
/// equalities hold on the nose rather than up to a path.
///
/// ## Regularity on the diagonal
///
/// `coe^{r→r} A a = a` is required *strictly*.  Note that the interpolation
/// line alone does **not** give it: `interp(r,r,i) = (r ∧ ~i) ∨ (r ∧ i)` is
/// not `r` in a free De Morgan algebra, because `~i ∨ i ≠ 1`.  This is the
/// precise point where a De Morgan interval differs from a Cartesian one:
/// a Cartesian cubical set has the *diagonal* cofibration `r = s`, and
/// regularity is obtained by putting the constant wall on it.  Here the
/// cofibration lattice has only endpoint faces, so the diagonal is decided
/// **before** composing, by `dim_eq`.  That gives strict regularity for
/// equal endpoints; on a diagonal *face* between two distinct variables
/// regularity is propositional, not definitional.  §14 of `docs/ctt.md`
/// records the distinction.

///|
/// The interpolation line from `r` to `r'`, at stage `i`.
pub fn interp(r : Dim, s : Dim, i : Dim) -> Dim {
  @cubical.dim_or(dim_and(r, dim_not(i)), dim_and(s, i))
}

///|
/// Reindex a family along the interpolation line.
pub fn fam_between(fam : Fam, r : Dim, s : Dim) -> Fam {
  memo_fam(Fam::{ f: fn(i) { fam.at(interp(r, s, i)) }, })
}

///|
/// Reindex a tube along the interpolation line.  The cofibrations are
/// untouched — they constrain the *other* directions, not this one.
pub fn Tube::between(self : Tube, r : Dim, s : Dim) -> Tube {
  let brs : Array[TubeBr] = []
  for b in self.branches {
    let tm = b.tm
    brs.push(TubeBr::{
      cof: b.cof,
      tm: memo_dclo(DClo::{ f: fn(i) { tm.at(interp(r, s, i)) }, }),
    })
  }
  Tube::{ branches: brs, }
}

///|
/// # `coe^{r→r'}` — 投遞
///
/// Deliver an element of `A(r)` to `A(r)`, for any two stages.
/// Strictly the identity when the stages are equal.
pub fn coe_between(fam : Fam, r : Dim, s : Dim, a : Val) -> Val {
  if @cubical.dim_eq(r, s) {
    return a
  }
  comp(fam_between(fam, r, s), fresh_dim(), Tube::empty(), a)
}

///|
/// # `comp^{r→r'}` — 異質合體
///
/// Heterogeneous composition: the type varies along the direction, the
/// walls live in it, and the lid lands in `A(r')`.  "Heterogeneous" is the
/// point — a homogeneous composition is the special case of a constant
/// family, and `hcomp_const` below is that special case.
pub fn comp_between(fam : Fam, r : Dim, s : Dim, tube : Tube, cap : Val) -> Val {
  if @cubical.dim_eq(r, s) {
    // On the diagonal the box is degenerate: every wall is the cap.
    return cap
  }
  comp(fam_between(fam, r, s), fresh_dim(), tube.between(r, s), cap)
}

///|
/// # `fill^{r→r'}` — 填充
///
/// The filler, as a line in the interpolation parameter: at `0` the cap,
/// at `1` the lid, and on each wall the given tube.  Filling is *derived*
/// from composition, not a second primitive.
pub fn fill_between(
  fam : Fam,
  r : Dim,
  s : Dim,
  tube : Tube,
  cap : Val,
) -> DClo {
  if @cubical.dim_eq(r, s) {
    return DClo::{ f: fn(_) { cap }, }
  }
  fill(fam_between(fam, r, s), fresh_dim(), tube.between(r, s), cap)
}

///|
/// # `transp` — 傳輸
///
/// CCHM's transport with a cofibration: `transp^i A φ a` coerces `a` along
/// `A` and is **required to be constant on `φ`**.  That side condition is
/// what makes univalence compute in cubical Agda, and here it is a wall:
///
/// The wall is the constant line `i ↦ a`, so it is well typed exactly when
/// `A` is constant on `φ` — `φ ⊢ A(i) = A(0)`.  This is a *typing*
/// requirement, not a runtime check: along a `ua` line, which is constant
/// on no nonempty face, only `φ = ⊥` is admissible.  The tests exercise a
/// proper face on a family that is constant there.
///
/// ```text
/// transp^i A φ a = comp^i A [φ ↦ a] a
/// ```
///
/// Two consequences are immediate and definitional:
///
/// * `φ = ⊤` gives a total tube, so the result is `a` — transport along a
///   line that is constrained everywhere does nothing;
/// * `φ = ⊥` gives the empty tube, so `transp` is `coe`.
pub fn transp(fam : Fam, i : Int32, phi : Cof, a : Val) -> Val {
  if @cubical.cof_is_false(phi) {
    return coe(fam, i, a)
  }
  comp(fam, i, Tube::empty().add(phi, DClo::{ f: fn(_) { a }, }), a)
}

///|
/// Transport between arbitrary stages, constant on `φ`.
pub fn transp_between(fam : Fam, r : Dim, s : Dim, phi : Cof, a : Val) -> Val {
  if @cubical.dim_eq(r, s) {
    return a
  }
  comp(
    fam_between(fam, r, s),
    fresh_dim(),
    Tube::empty().add(phi, DClo::{ f: fn(_) { a }, }),
    a,
  )
}

///|
/// # Transport as a dependent path
///
/// `transp_path A r r' a : PathP (i ↦ A(interp(r,r',i))) a (coe^{r→r'} a)`.
///
/// This is the operation that turns a coercion into something `ap` and
/// `pathJ` can consume.  It is the filler, packaged as a path value.
pub fn transp_path(fam : Fam, r : Dim, s : Dim, a : Val) -> Val {
  let line = fill_between(fam, r, s, Tube::empty(), a)
  VPLam(line)
}

///|
/// Homogeneous composition: the family is constant, so walls and lid all
/// live in one type.  Provided as the named special case, and checked
/// against `comp_between` in the tests.
pub fn hcomp_const(ty : Val, tube : Tube, cap : Val) -> Val {
  comp_between(fam_const(ty), @cubical.DZero, @cubical.DOne, tube, cap)
}

///|
/// Homogeneous filling.
pub fn hfill_const(ty : Val, tube : Tube, cap : Val) -> DClo {
  fill_between(fam_const(ty), @cubical.DZero, @cubical.DOne, tube, cap)
}
