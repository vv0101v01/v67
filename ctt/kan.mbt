///|
/// Re-index a tube along the connection `i ↦ r ∧ k`.  This is the only
/// place the algorithm needs the *connections* of the interval, and it is
/// exactly what turns composition into filling.
pub fn Tube::connect(self : Tube, i : Int32, r : Dim, k : Int32) -> Tube {
  let brs : Array[TubeBr] = []
  for b in self.branches {
    let c = cof_subst(b.cof, i, dim_and(r, @cubical.DVar(k)))
    if !@cubical.cof_is_false(c) {
      brs.push(TubeBr::{
        cof: c,
        tm: DClo::{ f: fn(m) { b.tm.at(dim_and(r, m)) }, },
      })
    }
  }
  Tube::{ branches: brs, }
}

///|
pub fn Tube::concat(self : Tube, other : Tube) -> Tube {
  let brs = self.branches[:].to_owned()
  for b in other.branches {
    brs.push(b)
  }
  Tube::{ branches: brs, }
}

///|
/// If the tube is total the box is already closed and the lid is forced.
/// Making this a *strict* rule is what gives `fill(0) = cap` on the nose.
fn total_tube(tube : Tube, i : Int32) -> Val? {
  for b in tube.branches {
    if @cubical.cof_is_true(b.cof) {
      return Some(b.tm.at(@cubical.DOne))
    }
  }
  let _ = i
  None
}

///|
/// # The Kan algorithm: computing the lid of an open box
///
/// ```text
///        φ ↦ u(i)          (the tube, on the cofibration φ)
///      ┌───────────┐
///      │           │
///  i=1 ├ ─ ─ ─  ─ ┤  ←  the LID, what this function returns
///      │           │
///  i=0 └───────────┘
///           a₀             (the cap, agreeing with u(0) on φ)
/// ```
///
/// `comp fam i tube cap` is defined by **structural recursion on the type
/// family**, one clause per type former.  This is the CCHM composition
/// structure; every clause is an equation, not a search:
///
/// * `Fin n` — a discrete type has unique composition, so the lid is the cap.
/// * `U` — the lid is a **Glue type**: `Glue [φ ↦ (E(1), coe^{1→0} E)] A₀`.
///   Composition in the universe *is* gluing; this is the clause that
///   makes univalence computational.
/// * `Π` — the lid is a **lambda**, whose body is a composition in the
///   codomain along the coerced argument.
/// * `Σ` — the lid is a **pair**: compose the first component, then
///   compose the second over the *filler* of the first.
/// * `Path` — the lid is a **dimension abstraction**, composing in the
///   body with the two endpoints added to the tube.
/// * `Glue` — compose the glued parts, then compose the base against
///   their images, then `glue` the results back together.
///
/// Cost: `O(|type| · |tube|)` recursive calls, each doing `O(1)` work plus
/// the cofibration arithmetic.  Compare `cubical.comp`, which is
/// `O(|A_generic| · |tube|)` *element* inspections — exponential in the
/// size of the type rather than linear.
pub fn comp(fam : Fam, i : Int32, tube : Tube, cap : Val) -> Val {
  match total_tube(tube, i) {
    Some(v) => return v
    None => ()
  }
  // Regularity / normality, as a computation rule: a box whose type and
  // tube do not depend on the direction is filled by its cap.  Sound
  // because the cap agrees with the (constant) tube on φ, and it is what
  // makes uaβ hold on the nose for *every* type, not just discrete ones.
  if fam.is_constant(i) && tube.is_constant(i) {
    return cap
  }
  match fam.at(@cubical.DVar(i)) {
    VFin(_) | VNat => cap
    VU => comp_univ(fam, i, tube, cap)
    VPi(_, _) => comp_pi(fam, i, tube, cap)
    VSig(_, _) => comp_sig(fam, i, tube, cap)
    VPath(_, _, _) => comp_path(fam, i, tube, cap)
    VGlue(_, _) => comp_glue(fam, i, tube, cap)
    VCircle | VSusp(_) | VTrunc(_) | VCoeq(_, _, _) =>
      comp_hit(fam, i, tube, cap)
    _ => cap
  }
}

///|
/// **Filling.**  The filler of a box is the line `i ↦ comp^{0→i}`, and it
/// is obtained from composition alone by the connection trick:
///
/// ```text
/// fill fam i tube cap (r) = comp^{k} fam(r ∧ k)
///                              [ φ[i := r ∧ k] ↦ u(r ∧ k),  r=0 ↦ cap ] cap
/// ```
///
/// At `r = 0` the added branch is total, so the value is `cap` strictly;
/// at `r = 1` the connection is the identity and the value is the lid.
/// Those two equations are the boundary of the filler, and they hold by
/// construction rather than by a separate proof.
pub fn fill(fam : Fam, i : Int32, tube : Tube, cap : Val) -> DClo {
  memo_dclo(DClo::{
    f: fn(r) {
      let k = fresh_dim()
      let fk = Fam::{ f: fn(m) { fam.at(dim_and(r, m)) }, }
      let tk = tube
        .connect(i, r, k)
        .add(@cubical.CEq(r, 0), DClo::{ f: fn(_) { cap }, })
      comp(fk, k, tk, cap)
    },
  })
}

///|
/// **Coercion** (transport) is composition with an empty tube:
/// `coe^{0→1} (i.A) a = comp^i A [] a`.
///
/// The **regularity law** is built in: if the family does not depend on
/// the direction, the value is returned untouched.  Deciding that is a
/// syntactic occurrence check on the interval, so regularity is a
/// *computation rule*, not a theorem to be proved afterwards.
pub fn coe(fam : Fam, i : Int32, a : Val) -> Val {
  if fam.is_constant(i) {
    return a
  }
  comp(fam, i, Tube::empty(), a)
}

///|
/// Coercion backwards, `coe^{1→0}`, by reversing the family.
pub fn coe_back(fam : Fam, i : Int32, a : Val) -> Val {
  coe(fam.rev(), i, a)
}

///|
/// The coercion *line* `r ↦ coe^{0→r} (i.A) a`, i.e. the filler of the
/// empty box.  This is what `Π` and `Σ` need to move an argument to a
/// variable stage.
pub fn coe_to(fam : Fam, i : Int32, a : Val) -> DClo {
  if fam.is_constant(i) {
    return DClo::{ f: fn(_) { a }, }
  }
  fill(fam, i, Tube::empty(), a)
}

///|
/// The reversed coercion line `r ↦ coe^{1→r} (i.A) a`.
pub fn coe_back_to(fam : Fam, i : Int32, a : Val) -> DClo {
  let line = coe_to(fam.rev(), i, a)
  DClo::{ f: fn(r) { line.at(dim_not(r)) }, }
}

// --------------------------------------------------------------------
// One clause per type former.
// --------------------------------------------------------------------

///|
/// `comp^i U [φ ↦ E] A₀ = Glue [φ(1) ↦ (E(1), coe^{1→0} E)] A₀`.
///
/// The equivalence is the backward coercion in the tube type: on `φ` we
/// have `E(0) = A₀`, so `coe^{1→0} E : E(1) → A₀` is exactly the required
/// equivalence, and when `E` is constant in `i` regularity makes it the
/// identity — recovering the familiar homogeneous formula
/// `Glue [φ ↦ (E, id)] A₀`.
fn comp_univ(fam : Fam, i : Int32, tube : Tube, cap : Val) -> Val {
  let _ = fam
  let brs : Array[GlueBr] = []
  for b in tube.branches {
    let psi1 = cof_subst(b.cof, i, @cubical.DOne)
    if @cubical.cof_is_false(psi1) {
      continue
    }
    let fe = Fam::{ f: fn(r) { b.tm.at(r) }, }
    brs.push(GlueBr::{
      cof: psi1,
      ty: b.tm.at(@cubical.DOne),
      eq: Equiv::{
        src: b.tm.at(@cubical.DOne),
        tgt: cap,
        // The branch needs `E(1) ≃ A₀`, so the *forward* map is the
        // backward coercion in E.  Getting this the wrong way round is
        // invisible for involutions and wrong for every other
        // permutation, which is why the composite-transport test uses a
        // shift rather than a swap.
        fwd: VLam(Clo::{ f: fn(x) { coe_back(fe, i, x) }, }),
        bwd: VLam(Clo::{ f: fn(x) { coe(fe, i, x) }, }),
        alpha: Clo::{
          f: fn(x) { vapp(roundtrip_fun(line_of(b.tm, i), false), x) },
        },
        beta: Clo::{
          f: fn(x) { vapp(roundtrip_fun(line_of(b.tm, i), true), x) },
        },
        // Lazy: building the J-based contraction runs a coercion, which
        // can itself reach a Glue.  Forcing it here would recurse through
        // every layer of a nested Glue even when `equiv` never needs it.
        contr: lazy_contr(fn() { transport_contr(line_of(b.tm, i)) }),
        strict: lazy_bool(fn() { line_strict(b.tm, i) }),
      },
    })
  }
  mk_glue_ty(brs, cap)
}

///|
/// `comp^i (Π(x:A).B) [φ ↦ u] w₀ =`
/// `λ(x : A(1)). comp^i B(x̃(i)) [φ ↦ u(i)(x̃(i))] (w₀ (x̃(0)))`
/// where `x̃(i) = coe^{1→i} A x`.
///
/// The argument is dragged *backwards* along the domain so that the body
/// can be composed forwards; this contravariance is the whole content of
/// the clause.
fn comp_pi(fam : Fam, i : Int32, tube : Tube, cap : Val) -> Val {
  let fa = Fam::{
    f: fn(r) {
      match fam.at(r) {
        VPi(a, _) => a
        _ => abort("comp_pi: domain")
      }
    },
  }
  VLam(Clo::{
    f: fn(x) {
      let xt = coe_back_to(fa, i, x)
      let fb = Fam::{
        f: fn(r) {
          match fam.at(r) {
            VPi(_, c) => c.at(xt.at(r))
            _ => abort("comp_pi: codomain")
          }
        },
      }
      comp(fb, i, tube.app(xt), vapp(cap, xt.at(@cubical.DZero)))
    },
  })
}

///|
/// `comp^i (Σ(x:A).B) [φ ↦ u] p₀ = (a₁, b₁)` where
/// `a₁ = comp A [φ ↦ fst u] (fst p₀)`, `ã = fill A [φ ↦ fst u] (fst p₀)`,
/// and `b₁ = comp^i B(ã(i)) [φ ↦ snd u] (snd p₀)`.
///
/// The second component is composed over the *filler* of the first, not
/// over its lid: that is what makes the pair land in the right fibre.
fn comp_sig(fam : Fam, i : Int32, tube : Tube, cap : Val) -> Val {
  let fa = Fam::{
    f: fn(r) {
      match fam.at(r) {
        VSig(a, _) => a
        _ => abort("comp_sig: domain")
      }
    },
  }
  let t1 = tube.fst()
  let a1 = comp(fa, i, t1, vfst(cap))
  let aline = fill(fa, i, t1, vfst(cap))
  let fb = Fam::{
    f: fn(r) {
      match fam.at(r) {
        VSig(_, c) => c.at(aline.at(r))
        _ => abort("comp_sig: codomain")
      }
    },
  }
  let b1 = comp(fb, i, tube.snd(), vsnd(cap))
  VPair(a1, b1)
}

///|
/// `comp^i (Path (j.B) a b) [φ ↦ u] p₀ =`
/// `<j> comp^i B(j) [φ ↦ u@j, j=0 ↦ a, j=1 ↦ b] (p₀@j)`.
///
/// Composition of paths is composition in the body with the two endpoint
/// constraints added to the tube — the reason `Path` is a Kan type as
/// soon as its body is.
fn comp_path(fam : Fam, i : Int32, tube : Tube, cap : Val) -> Val {
  VPLam(DClo::{
    f: fn(j) {
      let fb = Fam::{
        f: fn(r) {
          match fam.at(r) {
            VPath(b, _, _) => b.at(j)
            _ => abort("comp_path: body")
          }
        },
      }
      // The two endpoint walls must be read **at each stage**.  Reading
      // them once at the generic stage `DVar(i)` and freezing them as
      // constant walls leaves the composition direction free inside the
      // lid: the endpoints of a dependent path vary along the family, and
      // that variation is exactly what the walls have to carry.
      let ea = DClo::{
        f: fn(r) {
          match fam.at(r) {
            VPath(_, a, _) => a
            _ => abort("comp_path: left")
          }
        },
      }
      let eb = DClo::{
        f: fn(r) {
          match fam.at(r) {
            VPath(_, _, b) => b
            _ => abort("comp_path: right")
          }
        },
      }
      let tk = tube
        .at_dim(j)
        .add(@cubical.CEq(j, 0), ea)
        .add(@cubical.CEq(j, 1), eb)
      comp(fb, i, tk, vpapp(cap, j))
    },
  })
}

///|
/// `comp^i (Glue [ψ ↦ (T, e)] A) [φ ↦ u] u₀ = glue [ψ(1) ↦ t₁] a₁` where
///
/// ```text
/// t₁ = comp^i T [φ ∧ ψ ↦ u] (u₀|ψ)
/// t̃  = fill^i T [φ ∧ ψ ↦ u] (u₀|ψ)
/// a₁ = comp^i A [φ ↦ unglue u, ψ ↦ e(t̃)] (unglue u₀)
/// ```
///
/// The compatibility `e(1)(t₁) = a₁` on `ψ(1)` holds because `a₁` was
/// composed *against the tube* `ψ ↦ e(t̃)`, whose value at `i = 1` is
/// `e(1)(t₁)`.  So the `glue` is well formed by construction — this is the
/// clause that makes `Glue` fibrant, and hence the universe fibrant, and
/// hence univalence available.
fn comp_glue(fam : Fam, i : Int32, tube : Tube, cap : Val) -> Val {
  let fa = Fam::{
    f: fn(r) {
      match fam.at(r) {
        VGlue(a, _) => a
        _ => abort("comp_glue: base")
      }
    },
  }
  // Read branch cofibrations *before* the smart constructor can collapse
  // them: at a stage where a branch is total the type is returned bare,
  // and reading the extent off that would lose the branch entirely.
  let raw = fn(r : Dim) -> Array[GlueBr] {
    match fam.at(r) {
      VGlue(_, bs) => bs
      _ => []
    }
  }
  let generic = raw(@cubical.DVar(i))
  // per surviving branch: (ψ(1), e(1), t' when ψ(0) holds)
  let live : Array[(Cof, Equiv, Val?)] = []
  for k in 0..<generic.length() {
    let psi_i = generic[k].cof
    let psi0 = cof_subst(psi_i, i, @cubical.DZero)
    let psi1 = cof_subst(psi_i, i, @cubical.DOne)
    if @cubical.cof_is_false(psi_i) || @cubical.cof_is_false(psi1) {
      continue
    }
    let ft = Fam::{
      f: fn(r) {
        let bs = raw(r)
        if k < bs.length() {
          bs[k].ty
        } else {
          generic[k].ty
        }
      },
    }
    let ek = generic[k].eq
    if @cubical.cof_is_true(psi0) {
      // ψ holds at the near end: the cap *is* a T-element there.  Compose
      // it in T, and compose the base against the image of its filler, so
      // that on this face the base already lands on e(1)(t').
      let tk = tube.restrict(psi_i)
      // On ψ(0) the type *is* T, so the cap has a T-part there.  Usually
      // it is literally a branch of the cap; but the cap may arrive as a
      // `glue` over a different extent (it came out of another
      // composition), in which case the equivalence supplies the part:
      // e(0)⁻¹ (unglue cap).  This is sound because e(0) is an equivalence
      // and the correction step below re-establishes compatibility.
      let capk = match glue_part(cap, psi0) {
        Some(v) => v
        None => vapp(ek.bwd, unglue(cap))
      }
      let t1 = comp(ft, i, tk, capk)
      live.push((psi1, ek, Some(t1)))
    } else {
      // ψ fails at the near end: the cap gives no T-element at all.  The
      // glued part will be produced by contracting the fibre of e(1).
      live.push((psi1, ek, None))
    }
  }
  // The base box is the *unglued* tube, nothing more.  An earlier version
  // added a branch on ψ(i) carrying the image of the T-filler; that
  // cofibration mentions the composition direction, which an open box may
  // not do, and it leaked the direction into the lid.  The correction step
  // below is what re-establishes compatibility, as in CCHM.
  let base_tube = tube.unglue()
  let a1 = comp(fa, i, base_tube, unglue_cap(fam, i, cap))
  if live.length() == 0 {
    return mk_glue([], a1)
  }
  // If some branch is total at the far end, the type *is* that branch's
  // glued type there (the strict face rule), so the base component is
  // irrelevant and there is no base type to read — the Glue has collapsed.
  // The correction step is only needed, and only well typed, otherwise.
  let mut total_far = false
  for (psi1, _, _) in live {
    if @cubical.cof_is_true(psi1) {
      total_far = true
    }
  }
  let parts : Array[GlueTm] = []
  let correction : Array[TubeBr] = []
  let j = fresh_dim()
  for (psi1, ek, t_opt) in live {
    // A partial element of the fibre of e(1) over a1:
    //   * where ψ(0) held, the composed T-element with a reflexive path
    //     (the base was composed against its image, so it already agrees);
    //   * on the tube, u(1) with a reflexive path.
    let partial : Array[(Cof, Val, Val)] = []
    match t_opt {
      Some(t1) => partial.push((psi1, t1, refl(vapp(ek.fwd, t1))))
      None => ()
    }
    for b in tube.branches {
      let c = cof_and(cof_subst(b.cof, i, @cubical.DOne), psi1)
      if !@cubical.cof_is_false(c) {
        let u1 = b.tm.at(@cubical.DOne)
        // The wall may itself be a `glue` over a different extent, having
        // come out of another composition.  Then it has no literal branch
        // on ψ(1), and using it *as* the T-element would put a glued value
        // where a bare one belongs — which is how a composition direction
        // leaked into the fibre contraction.  The equivalence supplies the
        // part, exactly as for the cap.
        let tp = match glue_part(u1, psi1) {
          Some(v) => v
          None => vapp(ek.bwd, unglue(u1))
        }
        partial.push((c, tp, refl(vapp(ek.fwd, tp))))
      }
    }
    // **equiv**: contract the fibre, extending the partial element.
    // For a strict isomorphism this is the centre, and α is reflexive, so
    // no correction is needed; `equiv` short-circuits on the flag.
    let (t1, alpha) = equiv(ek, a1, partial)
    parts.push(GlueTm::{ cof: psi1, tm: t1, })
    // α : Path (e(1) t1) a1.  Drag a1 back along it so that the base
    // component lands exactly on e(1)(t1); this is the step that makes
    // `glue` well formed for a *non-strict* equivalence.
    if !total_far && !ek.strict.get() {
      correction.push(TubeBr::{
        cof: psi1,
        tm: DClo::{ f: fn(r) { vpapp(alpha, dim_not(r)) }, },
      })
    }
  }
  if total_far {
    return mk_glue(parts, a1)
  }
  let a_far = fa.at(@cubical.DOne)
  // …and the far end of the original tube, unglued.  Without it the
  // corrected base would not agree with the walls on φ(1).
  for b in tube.branches {
    let c1 = cof_subst(b.cof, i, @cubical.DOne)
    if !@cubical.cof_is_false(c1) {
      let u1 = b.tm.at(@cubical.DOne)
      correction.push(TubeBr::{
        cof: c1,
        tm: DClo::{ f: fn(_) { unglue(u1) }, },
      })
    }
  }
  let far_tube = Tube::{ branches: correction, }
  let a_final = comp(fam_const(a_far), j, far_tube, a1)
  mk_glue(parts, a_final)
}

///|
/// Does a tube depend on the composition direction?
pub fn Tube::is_constant(self : Tube, i : Int32) -> Bool {
  for b in self.branches {
    if b.cof.mentions(i) {
      return false
    }
    if b.tm.at(@cubical.DVar(i)).mentions_dim(i) {
      return false
    }
  }
  true
}

///|
/// **Ungluing at stage 0.**  If a branch of the `Glue` is total at `i = 0`
/// then the type *is* the glued type there, so the cap is a bare element
/// of `T` and its base component is `e(0)(cap)`.  Forgetting this is the
/// classic way to get `uaβ` wrong: the transport would return `a` instead
/// of `e(a)`.
fn unglue_cap(fam : Fam, i : Int32, cap : Val) -> Val {
  match cap {
    VGlued(_, a) => a
    _ =>
      match fam.at(@cubical.DVar(i)) {
        VGlue(_, brs) => {
          for b in brs {
            if @cubical.cof_is_true(cof_subst(b.cof, i, @cubical.DZero)) {
              return vapp(b.eq.fwd, cap)
            }
          }
          cap
        }
        _ => cap
      }
  }
}

///|
/// The line of types carried by a tube branch, as a path value.
fn line_of(tm : DClo, _i : Int32) -> Val {
  VPLam(tm)
}

///|
/// Decide once, on a generic point, whether the coercion along a tube
/// line is a strict isomorphism.  Memoised by the caller's `Equiv`, so the
/// readback happens at most once per branch and never inside `equiv`.
fn line_strict(tm : DClo, i : Int32) -> Bool {
  let fe = Fam::{ f: fn(r) { tm.at(r) }, }
  let n = VNe(fresh_dim())
  let rt1 = coe(fe, i, coe_back(fe, i, n))
  let rt2 = coe_back(fe, i, coe(fe, i, n))
  quote_norm(rt1, 8) == quote_norm(n, 8) &&
  quote_norm(rt2, 8) == quote_norm(n, 8)
}
