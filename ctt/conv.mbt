///|
/// # Conversion, without a depth bound
///
/// The kernel used to decide definitional equality by *printing* both
/// values to depth 14 and comparing the strings.  That is a bounded
/// approximation twice over: it truncates at a fixed depth, and it
/// identifies anything whose truncated renderings coincide.
///
/// This is a structural check instead.  It walks the two values together,
/// probing a closure on both sides at the *same* fresh variable, so
/// α-equivalence is handled by construction rather than by a naming
/// convention.  There is no depth parameter.
///
/// ## Termination
///
/// The value domain is the image of a total type theory: every closure
/// comes from a term, β-reduction is strongly normalising, and the
/// constructors a normal form can carry are finite.  Probing a closure
/// exposes strictly more of a finite normal form each time, so the walk
/// terminates on any two values.  There is no fixpoint in `Val`, hence no
/// way to build the infinite value that would defeat this.
///
/// ## Proof irrelevance
///
/// An `Equiv` carries `alpha`, `beta` and `contr`.  Those inhabit
/// *propositions* — `isContr` of a fibre is a proposition, and once the
/// fibre is contractible the round-trip homotopies are determined up to
/// homotopy.  Comparing them would force a `J`-built contraction for no
/// mathematical content, so conversion of equivalences compares source,
/// target and the two maps.  This is the standard convention: an
/// equivalence *is* its underlying map, the rest is data proving a
/// proposition.

///|
/// Probe a term closure on both sides **from the same name supply**.
///
/// A closure body may itself allocate fresh directions — `comp` does, at
/// every step.  If the two sides are evaluated with the supply left where
/// the previous probe put it, those internal allocations drift apart and
/// two α-equivalent values come back with different variable indices.
/// Resetting the supply to the same base before each side makes the
/// internal names line up, which is exactly what α-equivalence means.
fn probe2(c1 : Clo, c2 : Clo, k : Int32) -> Bool {
  let save = fresh_dims.next
  fresh_dims.next = k + 1
  let v1 = c1.at(VNe(k))
  fresh_dims.next = k + 1
  let v2 = c2.at(VNe(k))
  fresh_dims.next = save
  conv(v1, v2, k + 1)
}

///|
/// The same discipline for a dimension closure.
fn probe_dim2(d1 : DClo, d2 : DClo, k : Int32) -> Bool {
  let save = fresh_dims.next
  fresh_dims.next = k + 1
  let v1 = d1.at(@cubical.DVar(k))
  fresh_dims.next = k + 1
  let v2 = d2.at(@cubical.DVar(k))
  fresh_dims.next = save
  conv(v1, v2, k + 1)
}

///|
/// Structural conversion.  `k` is the supply of *shared* probe variables:
/// both sides are probed at the same one, which is what makes the check
/// respect α-equivalence without renaming anything.
fn conv(a : Val, b : Val, k : Int32) -> Bool {
  match (a, b) {
    (VU, VU) | (VNat, VNat) | (VZero, VZero) => true
    (VFin(m), VFin(n)) => m == n
    (VLit(m), VLit(n)) => m == n
    (VNe(m), VNe(n)) => m == n
    (VSuc(m), VSuc(n)) => conv(m, n, k)
    (VSplit(m, bs, sc), VSplit(n, bt, sd)) => {
      if m != n || bs.length() != bt.length() || !conv(sc, sd, k) {
        return false
      }
      for i, x in bs {
        if !conv(x, bt[i], k) {
          return false
        }
      }
      true
    }
    (VNatRec(z1, s1, c1), VNatRec(z2, s2, c2)) => {
      let y = VNe(k + 1)
      conv(z1, z2, k + 2) &&
      conv(c1, c2, k + 2) &&
      probe2(
        Clo::{ f: fn(p) { vapp(s1.at(p), y) }, },
        Clo::{ f: fn(p) { vapp(s2.at(p), y) }, },
        k,
      )
    }
    (VPi(a1, c1), VPi(a2, c2)) | (VSig(a1, c1), VSig(a2, c2)) =>
      conv(a1, a2, k) && probe2(c1, c2, k)
    (VPath(f1, x1, y1), VPath(f2, x2, y2)) =>
      conv_dim_clo(f1, f2, k) && conv(x1, x2, k) && conv(y1, y2, k)
    (VLam(c1), VLam(c2)) => probe2(c1, c2, k)
    // η: a lambda against a non-lambda is compared after applying both
    (VLam(c1), _) => probe2(c1, Clo::{ f: fn(x) { vapp(b, x) }, }, k)
    (_, VLam(c2)) => probe2(Clo::{ f: fn(x) { vapp(a, x) }, }, c2, k)
    (VPair(x1, y1), VPair(x2, y2)) => conv(x1, x2, k) && conv(y1, y2, k)
    (VPLam(d1), VPLam(d2)) => conv_dim_clo(d1, d2, k)
    (VGlue(a1, b1), VGlue(a2, b2)) => {
      if b1.length() != b2.length() || !conv(a1, a2, k) {
        return false
      }
      for i, x in b1 {
        let y = b2[i]
        if !@cubical.cof_same(x.cof, y.cof) ||
          !conv(x.ty, y.ty, k) ||
          !conv(x.eq.fwd, y.eq.fwd, k) {
          return false
        }
      }
      true
    }
    (VGlued(b1, a1), VGlued(b2, a2)) => {
      if b1.length() != b2.length() || !conv(a1, a2, k) {
        return false
      }
      for i, x in b1 {
        let y = b2[i]
        if !@cubical.cof_same(x.cof, y.cof) || !conv(x.tm, y.tm, k) {
          return false
        }
      }
      true
    }
    (VCircle, VCircle) | (VBase, VBase) => true
    (VNorth, VNorth) | (VSouth, VSouth) => true
    (VLoop(r), VLoop(s)) => @cubical.dim_eq(r, s)
    (VMerid(_, a, r), VMerid(_, b, s)) => conv(a, b, k) && @cubical.dim_eq(r, s)
    (VSq(_, x1, y1, r), VSq(_, x2, y2, s)) =>
      conv(x1, x2, k) && conv(y1, y2, k) && @cubical.dim_eq(r, s)
    (VSusp(a), VSusp(b)) | (VTrunc(a), VTrunc(b)) => conv(a, b, k)
    (VInc(a), VInc(b)) => conv(a, b, k)
    (VHComp(t1, u1, c1), VHComp(t2, u2, c2)) => {
      if u1.branches.length() != u2.branches.length() ||
        !conv(t1, t2, k) ||
        !conv(c1, c2, k) {
        return false
      }
      for i, x in u1.branches {
        let y = u2.branches[i]
        if !@cubical.cof_same(x.cof, y.cof) || !conv_dim_clo(x.tm, y.tm, k) {
          return false
        }
      }
      true
    }
    (VCircRec(t1, b1, l1, x1), VCircRec(t2, b2, l2, x2)) =>
      conv(t1, t2, k) && conv(b1, b2, k) && conv(l1, l2, k) && conv(x1, x2, k)
    (VTruncRec(t1, f1, p1, x1), VTruncRec(t2, f2, p2, x2)) =>
      conv(t1, t2, k) && conv(f1, f2, k) && conv(p1, p2, k) && conv(x1, x2, k)
    (VSuspRec(t1, n1, s1, m1, x1), VSuspRec(t2, n2, s2, m2, x2)) =>
      conv(t1, t2, k) &&
      conv(n1, n2, k) &&
      conv(s1, s2, k) &&
      conv(m1, m2, k) &&
      conv(x1, x2, k)
    (VCoeq(b1, f1, g1), VCoeq(b2, f2, g2)) =>
      conv(b1, b2, k) && conv(f1, f2, k) && conv(g1, g2, k)
    (VCoeqInc(a), VCoeqInc(b)) => conv(a, b, k)
    (VCoeqRel(a, r), VCoeqRel(b, s)) => conv(a, b, k) && @cubical.dim_eq(r, s)
    (VCoeqRec(t1, h1, p1, x1), VCoeqRec(t2, h2, p2, x2)) =>
      conv(t1, t2, k) && conv(h1, h2, k) && conv(p1, p2, k) && conv(x1, x2, k)
    _ => false
  }
}

///|
/// Probe a dimension closure on both sides at the same fresh direction.
fn conv_dim_clo(d1 : DClo, d2 : DClo, k : Int32) -> Bool {
  probe_dim2(d1, d2, k)
}

///|
/// # Definitional equality
///
/// Structural conversion, unbounded.  β and η for functions and paths, the
/// strict `Glue` face rules and the strict `unglue ∘ glue` rule all fire
/// during evaluation, so this walk only has to compare normal forms.
pub fn val_conv(a : Val, b : Val) -> Bool {
  conv(a, b, fresh_dim())
}

///|
pub impl Eq for Val with fn equal(a, b) {
  val_conv(a, b)
}

///|
pub impl Debug for Equiv with fn to_repr(self) {
  let s = quote_norm(self.src, 6)
  let t = quote_norm(self.tgt, 6)
  Repr::literal(s + " ≃ " + t)
}

///|
pub impl Eq for Equiv with fn equal(a, b) {
  val_conv(a.src, b.src) &&
  val_conv(a.tgt, b.tgt) &&
  val_conv(a.fwd, b.fwd) &&
  val_conv(a.bwd, b.bwd)
}
