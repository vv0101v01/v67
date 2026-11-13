///|
/// # Structural entailment in the face lattice
///
/// `cof_entails(phi, psi, n)` decides `phi <= psi` by enumerating all `3^n`
/// subcubes.  That is a fine oracle, but as a *kernel* primitive it puts a
/// hard exponential wall on the number of dimensions in scope: the cost is
/// `3^n` in the largest dimension index, so a deep composition — which
/// allocates a fresh direction at every step — dies long before the
/// mathematics does.
///
/// This file decides the same relation **structurally**, at a cost that
/// depends on the size of the two formulas and not at all on how many
/// dimensions exist.
///
/// ## Why a structural procedure exists
///
/// The face lattice is the *free distributive lattice* on the faces
/// `(i = 0)`, `(i = 1)`, modulo `(i = 0) ∧ (i = 1) = ⊥`.  It is not a
/// Boolean algebra: `(i = 0) ∨ (i = 1)` is the boundary of the interval,
/// strictly below `⊤`.  Two facts make the procedure work.
///
/// **1. Faces are join-prime.**  A consistent conjunction of literals `F`
/// has `F <= psi₁ ∨ psi₂` iff `F <= psi₁` or `F <= psi₂`.  Semantically `F`
/// has a generic point — its own directions pinned, every other direction
/// free — and Kleene disjunction returns `1` only when a disjunct already
/// is `1`.
///
/// **2. Every cofibration is a join of faces.**  Distribute `∧` over `∨`,
/// dropping contradictory disjuncts.
///
/// Together: `phi <= psi` iff every face of `phi` forces `psi` at its
/// generic point, and forcing is one Kleene evaluation, `O(|psi|)`, against
/// a *sparse* assignment.  Directions that do not occur cost nothing.
///
/// ## Reuse
///
/// The normal form is the one already used for dimension terms in
/// `interval.mbt`: a sorted, deduplicated, absorption-reduced list of
/// conjunctions, with the literal `2i` for `(i = 1)` and `2i + 1` for
/// `(i = 0)`.  The only addition is the face-lattice relation itself: a
/// conjunction holding both `2i` and `2i + 1` is `⊥` here, whereas the
/// dimension term `i ∧ ~i` is merely free.
///
/// ## Complexity
///
/// DNF is exponential in the *formula*, unavoidable for a free distributive
/// lattice, but the formulas a Kan composition produces are tiny.
/// There is **no dependence on the dimension supply**.

///|
/// Drop conjunctions that pin a direction both ways — the one relation
/// that distinguishes the face lattice from the free De Morgan algebra.
fn faces_consistent(terms : Array[Array[Int32]]) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for t in terms {
    let mut ok = true
    for k in 0..<t.length() {
      if k > 0 && t[k] == t[k - 1] + 1 && t[k - 1] % 2 == 0 {
        ok = false
      }
    }
    if ok {
      out.push(t)
    }
  }
  out
}

///|

///|
/// Merge two sorted literal lists, reporting a clash.  Linear, unlike the
/// quadratic dedup-and-absorb pass in `dnf_canon`.
fn merge_lits(a : Array[Int32], b : Array[Int32]) -> Array[Int32]? {
  let out : Array[Int32] = []
  let mut i = 0
  let mut j = 0
  while i < a.length() && j < b.length() {
    let x = a[i]
    let y = b[j]
    if x == y {
      out.push(x)
      i = i + 1
      j = j + 1
    } else if x < y {
      out.push(x)
      i = i + 1
    } else {
      out.push(y)
      j = j + 1
    }
  }
  while i < a.length() {
    out.push(a[i])
    i = i + 1
  }
  while j < b.length() {
    out.push(b[j])
    j = j + 1
  }
  // In a sorted merge the two literals of a direction are adjacent, so
  // one linear pass decides consistency.  Checking during the merge is
  // not enough: the tails are appended after it.
  for k in 1..<out.length() {
    if out[k] == out[k - 1] + 1 && out[k - 1] % 2 == 0 {
      return None
    }
  }
  Some(out)
}

///|
fn cof_dnf_raw(phi : Cof) -> Array[Array[Int32]] {
  match phi {
    CTop => [[]]
    CBot => []
    CEq(r, eps) => faces_consistent(dnf_of(r, eps == 0))
    CAnd(a, b) => {
      let da = cof_dnf_raw(a)
      let db = cof_dnf_raw(b)
      // Fast path: a conjunction of two *single* faces is one face, and
      // merging their sorted literals is linear.  This is the shape the
      // kernel builds — a long chain of `∧` — and running the general
      // quadratic normalisation at every link made it cubic.
      if da.length() == 1 && db.length() == 1 {
        return match merge_lits(da[0], db[0]) {
          Some(m) => [m]
          None => []
        }
      }
      faces_consistent(dnf_and(da, db))
    }
    COr(a, b) => dnf_or(cof_dnf_raw(a), cof_dnf_raw(b))
  }
}

///|
/// The faces of a cofibration, each a sorted list of literals (`2i` for
/// `i = 1`, `2i + 1` for `i = 0`).  The empty list is the whole cube; an
/// empty outer list is `⊥`.
pub fn cof_faces(phi : Cof) -> Array[Array[Int32]] {
  cof_dnf_raw(phi)
}

///|
/// Kleene evaluation of a dimension term against a sparse face.  Absent
/// directions are free (`2`), so the cost never mentions the dimension
/// supply.  The literal list is sorted, so lookup is a binary search.
fn dim_eval_lits(r : Dim, lits : Array[Int32]) -> Int32 {
  match r {
    DZero => 0
    DOne => 1
    DVar(i) => {
      let mut lo = 0
      let mut hi = lits.length()
      while lo < hi {
        let mid = (lo + hi) / 2
        if lits[mid] < 2 * i {
          lo = mid + 1
        } else {
          hi = mid
        }
      }
      if lo < lits.length() && lits[lo] == 2 * i {
        1
      } else if lo < lits.length() && lits[lo] == 2 * i + 1 {
        0
      } else {
        2
      }
    }
    DNot(s) => {
      let v = dim_eval_lits(s, lits)
      if v == 2 {
        2
      } else {
        1 - v
      }
    }
    DAnd(a, b) => {
      let x = dim_eval_lits(a, lits)
      let y = dim_eval_lits(b, lits)
      if x == 0 || y == 0 {
        0
      } else if x == 1 && y == 1 {
        1
      } else {
        2
      }
    }
    DOr(a, b) => {
      let x = dim_eval_lits(a, lits)
      let y = dim_eval_lits(b, lits)
      if x == 1 || y == 1 {
        1
      } else if x == 0 && y == 0 {
        0
      } else {
        2
      }
    }
  }
}

///|
/// Does the face force `psi`?  Join-primeness turns the disjunctive case
/// into a plain "either" — exactly where the exponential enumeration used
/// to be.
fn face_forces(lits : Array[Int32], psi : Cof) -> Bool {
  match psi {
    CTop => true
    CBot => false
    CEq(r, eps) => dim_eval_lits(r, lits) == eps
    CAnd(a, b) => face_forces(lits, a) && face_forces(lits, b)
    COr(a, b) => face_forces(lits, a) || face_forces(lits, b)
  }
}

///|
/// # `phi <= psi`, decided structurally
///
/// No bound on the number of dimensions.  Agrees with
/// `cof_entails(phi, psi, n)` for every `n` mentioning both formulas — a
/// fact checked exhaustively against that oracle in `faces_wbtest.mbt`.
pub fn cof_leq(phi : Cof, psi : Cof) -> Bool {
  if phi == psi {
    return true
  }
  match psi {
    CTop => return true
    _ => ()
  }
  for lits in cof_dnf_raw(phi) {
    if !face_forces(lits, psi) {
      return false
    }
  }
  true
}

///|
pub fn cof_same(phi : Cof, psi : Cof) -> Bool {
  cof_leq(phi, psi) && cof_leq(psi, phi)
}

///|
pub fn cof_is_true(phi : Cof) -> Bool {
  cof_leq(CTop, phi)
}

///|
pub fn cof_is_false(phi : Cof) -> Bool {
  cof_dnf_raw(phi).length() == 0
}
