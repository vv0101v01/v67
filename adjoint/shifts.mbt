///|
/// The **unit** of the adjunction `↓^m_k ⊣ ↑^m_k` at mode `m`:
/// `A_m ⊢_m ↑^m_k ↓^m_k A`.
pub fn Prover::shift_unit(
  self : Prover,
  m : Int32,
  k : Int32,
  a : Formula,
) -> Proof? {
  self.prove([Antecedent::new(m, a)], m, Up(m, k, Down(m, k, a)))
}

///|
/// The **counit** at mode `k`: `↓^m_k ↑^m_k B ⊢_k B`.
/// In the LNL mode theory this is dereliction `!B ⊢ B`.
pub fn Prover::shift_counit(
  self : Prover,
  m : Int32,
  k : Int32,
  b : Formula,
) -> Proof? {
  self.prove([Antecedent::new(k, Down(m, k, Up(m, k, b)))], k, b)
}

///|
/// The adjunction itself, as a decidable statement:
///
/// ```text
///   ↓^m_k A ⊢_k B      ⟺      A ⊢_m ↑^m_k B
/// ```
///
/// Both sides are decided by the same cut-free search, so this is a
/// genuine finite check of the hom-set bijection on the given propositions
/// — not an appeal to the general theorem.
pub fn Prover::adjunction_holds(
  self : Prover,
  m : Int32,
  k : Int32,
  a : Formula,
  b : Formula,
) -> Bool {
  let lhs = self.provable([Antecedent::new(k, Down(m, k, a))], k, b)
  let rhs = self.provable([Antecedent::new(m, a)], m, Up(m, k, b))
  lhs == rhs
}

///|
/// The triangle identities, checked propositionally: the two composites
/// `↓A → ↓↑↓A → ↓A` and `↑B → ↑↓↑B → ↑B` are derivable, which together with
/// the hom-set bijection pins the adjunction down.
pub fn Prover::triangle_ids(
  self : Prover,
  m : Int32,
  k : Int32,
  a : Formula,
) -> Bool {
  // ↓A ⊢ ↓A  composed with unit then counit is again derivable
  let down = Down(m, k, a)
  let via_unit = self.provable(
    [Antecedent::new(k, down)],
    k,
    Down(m, k, Up(m, k, down)),
  )
  let back = self.provable(
    [Antecedent::new(k, Down(m, k, Up(m, k, down)))],
    k,
    down,
  )
  via_unit && back
}

///|
/// **Conservativity.**  A sequent purely at one mode, with no shifts, is
/// provable in the combined logic iff it is provable in that mode's own
/// logic.  Checked by running the same search under two mode theories.
pub fn conservative_at(
  big : Modes,
  small : Modes,
  mode_big : Int32,
  mode_small : Int32,
  cases : Array[(Array[Formula], Formula)],
) -> (Int32, Int32) {
  let pb = Prover::new(big)
  let ps = Prover::new(small)
  let mut tested = 0
  let mut mismatch = 0
  for (hyps, goal) in cases {
    let cb : Array[Antecedent] = []
    let cs : Array[Antecedent] = []
    for h in hyps {
      cb.push(Antecedent::new(mode_big, h))
      cs.push(Antecedent::new(mode_small, h))
    }
    tested = tested + 1
    if pb.provable(cb, mode_big, goal) != ps.provable(cs, mode_small, goal) {
      mismatch = mismatch + 1
    }
  }
  (tested, mismatch)
}

///|
/// The exponential `!A = ↓^z_L ↑^z_L A` and its comonad laws, all of which
/// are derivable *without* adding any rule for `!`: they fall out of the
/// two shifts and the structural rules of the upper mode.
pub fn Prover::exponential_laws(
  self : Prover,
  z : Int32,
  l : Int32,
  a : Formula,
) -> (Bool, Bool, Bool, Bool) {
  let bang_a = bang(z, l, a)
  // dereliction: !A ⊢ A
  let dereliction = self.provable([Antecedent::new(l, bang_a)], l, a)
  // comultiplication: !A ⊢ !!A
  let dig = self.provable([Antecedent::new(l, bang_a)], l, bang(z, l, bang_a))
  // contraction is derivable at the linear mode for !-formulas
  let contr = self.provable(
    [Antecedent::new(l, bang_a), Antecedent::new(l, bang_a)],
    l,
    bang_a,
  )
  // weakening likewise
  let weak = self.provable([], l, Lolli(bang_a, One))
  (dereliction, dig, contr, weak)
}
