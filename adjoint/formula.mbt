///|
/// Propositions of adjoint logic.  The connectives are *uniform across
/// modes* — the same right and left rules at every mode — and only the two
/// **shifts** move between modes:
///
/// * `Up(m, k, A)` is `↑^m_k A_k`, a proposition at mode `m`, requiring `m ≥ k`.
/// * `Down(l, m, A)` is `↓^l_m A_l`, a proposition at mode `m`, requiring `l ≥ m`.
///
/// For fixed `k ≤ m` the pair forms an adjunction `↓^m_k ⊣ ↑^m_k`:
/// `Hom_k(↓^m_k A, B) ≅ Hom_m(A, ↑^m_k B)`.  In the LNL mode theory this is
/// Benton's `F ⊣ G`, and `!A = ↓^U_L ↑^U_L A`.
#derive(Debug, Eq)
pub(all) enum Formula {
  Atom(Int32)
  One
  Zero
  Top
  Tensor(Formula, Formula)
  Lolli(Formula, Formula)
  With(Formula, Formula)
  Plus(Formula, Formula)
  Up(Int32, Int32, Formula)
  Down(Int32, Int32, Formula)
}

///|
/// The mode a formula is *forced* to live at, if any.  Shifts fix their
/// mode; the other connectives are mode-polymorphic (`None`).
pub fn Formula::fixed_mode(self : Formula) -> Int32? {
  match self {
    Up(m, _, _) => Some(m)
    Down(_, m, _) => Some(m)
    _ => None
  }
}

///|
/// Number of constructors: the termination measure for proof search.
pub fn Formula::size(self : Formula) -> Int32 {
  match self {
    Atom(_) | One | Zero | Top => 1
    Tensor(a, b) | Lolli(a, b) | With(a, b) | Plus(a, b) =>
      1 + a.size() + b.size()
    Up(_, _, a) | Down(_, _, a) => 1 + a.size()
  }
}

///|
/// Well-formedness against a mode theory: every shift must respect the
/// preorder.  This is the only place the mode theory constrains syntax.
pub fn Formula::well_formed(self : Formula, modes : Modes) -> Bool {
  match self {
    Atom(_) | One | Zero | Top => true
    Tensor(a, b) | Lolli(a, b) | With(a, b) | Plus(a, b) =>
      a.well_formed(modes) && b.well_formed(modes)
    Up(m, k, a) => modes.ge(m, k) && a.well_formed(modes)
    Down(l, m, a) => modes.ge(l, m) && a.well_formed(modes)
  }
}

///|
/// A canonical string key, used for memoising the proof search.
pub fn Formula::key(self : Formula) -> String {
  match self {
    Atom(i) => "a\{i}"
    One => "1"
    Zero => "0"
    Top => "T"
    Tensor(a, b) => "(\{a.key()}*\{b.key()})"
    Lolli(a, b) => "(\{a.key()}-o\{b.key()})"
    With(a, b) => "(\{a.key()}&\{b.key()})"
    Plus(a, b) => "(\{a.key()}+\{b.key()})"
    Up(m, k, a) => "u\{m}_\{k}\{a.key()}"
    Down(l, m, a) => "d\{l}_\{m}\{a.key()}"
  }
}

///|
/// The exponential of the LNL mode theory: `!A = ↓^U_L ↑^U_L A`.
/// More generally `!^z A = ↓^z_L ↑^z_L A` for any mode `z ≥ L`.
pub fn bang(z : Int32, l : Int32, a : Formula) -> Formula {
  Down(z, l, Up(z, l, a))
}

///|
/// An antecedent: a formula together with the mode it is assumed at.
#derive(Debug, Eq)
pub struct Antecedent {
  mode : Int32
  formula : Formula
}

///|
pub fn Antecedent::new(mode : Int32, formula : Formula) -> Antecedent {
  Antecedent::{ mode, formula, }
}

///|
/// The declaration of independence: `Ψ ≥ k`, i.e. every antecedent mode is
/// `≥ k`.  A sequent violating this is not merely unprovable, it is
/// *ill-formed*, and the search rejects it outright.
pub fn independent(ctx : Array[Antecedent], k : Int32, modes : Modes) -> Bool {
  for a in ctx {
    if !modes.ge(a.mode, k) {
      return false
    }
  }
  true
}

///|
/// A canonical key for a sequent: the goal mode, the goal, and the
/// multiset of antecedents (sorted, since exchange is always allowed).
pub fn sequent_key(
  ctx : Array[Antecedent],
  k : Int32,
  goal : Formula,
) -> String {
  let parts : Array[String] = []
  for a in ctx {
    parts.push("\{a.mode}:\{a.formula.key()}")
  }
  parts.sort()
  let mut s = ""
  for p in parts {
    s = s + p + ","
  }
  s + "|-\{k}:" + goal.key()
}
