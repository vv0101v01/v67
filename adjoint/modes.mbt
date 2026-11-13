///|
/// A **mode theory**: a finite preorder `m ≥ k` on modes of truth, each
/// carrying a set `σ(m) ⊆ {W, C}` of structural properties.
///
/// The preorder is the *declaration of independence*: a proof of `A_k` may
/// depend on a hypothesis `B_m` only when `m ≥ k`.  Cut elimination forces
/// monotonicity: `m ≥ k` implies `σ(m) ⊇ σ(k)`.  Both conditions are
/// decidable on a finite mode set, and `check` decides them.
///
/// Reference: Pruiksma, Chargin, Pfenning, Reed, *Adjoint Logic* (2018).
#derive(Debug, Eq)
pub struct Modes {
  names : Array[String]
  /// `geq[m][k]` is `m ≥ k`
  geq : Array[Array[Bool]]
  weaken : Array[Bool]
  contract : Array[Bool]
}

///|
pub fn Modes::new(
  names : Array[String],
  geq : Array[Array[Bool]],
  weaken : Array[Bool],
  contract : Array[Bool],
) -> Modes {
  Modes::{ names, geq, weaken, contract, }
}

///|
pub fn Modes::size(self : Modes) -> Int32 {
  self.names.length()
}

///|
/// `m ≥ k`: a proposition of mode `k` may depend on mode `m`.
pub fn Modes::ge(self : Modes, m : Int32, k : Int32) -> Bool {
  if m < 0 || m >= self.size() || k < 0 || k >= self.size() {
    return false
  }
  self.geq[m][k]
}

///|
pub fn Modes::allows_weaken(self : Modes, m : Int32) -> Bool {
  m >= 0 && m < self.size() && self.weaken[m]
}

///|
pub fn Modes::allows_contract(self : Modes, m : Int32) -> Bool {
  m >= 0 && m < self.size() && self.contract[m]
}

///|
/// Decide the mode-theory axioms: reflexivity, transitivity, and
/// monotonicity of the structural properties along the preorder.
/// Cost `O(n³)` for transitivity, `O(n²)` for monotonicity.
pub fn Modes::check(self : Modes) -> Bool {
  let n = self.size()
  if self.geq.length() != n ||
    self.weaken.length() != n ||
    self.contract.length() != n {
    return false
  }
  for m in 0..<n {
    if self.geq[m].length() != n {
      return false
    }
    // reflexivity
    if !self.geq[m][m] {
      return false
    }
  }
  // transitivity
  for a in 0..<n {
    for b in 0..<n {
      if self.geq[a][b] {
        for c in 0..<n {
          if self.geq[b][c] && !self.geq[a][c] {
            return false
          }
        }
      }
    }
  }
  // monotonicity: m ≥ k implies σ(m) ⊇ σ(k)
  for m in 0..<n {
    for k in 0..<n {
      if self.geq[m][k] {
        if self.weaken[k] && !self.weaken[m] {
          return false
        }
        if self.contract[k] && !self.contract[m] {
          return false
        }
      }
    }
  }
  true
}

///|
/// The LNL mode theory: `U ≥ L`, `U` structural (`W, C`), `L` linear.
/// Index 0 is `U`, index 1 is `L`.  This is the smallest mode theory in
/// which the exponential `!A = ↓^U_L ↑^U_L A` is definable.
pub fn modes_lnl() -> Modes {
  Modes::new(["U", "L"], [[true, true], [false, true]], [true, false], [
    true, false,
  ])
}

///|
pub let mode_u : Int32 = 0

///|
pub let mode_l : Int32 = 1

///|
/// A three-mode chain `U ≥ A ≥ L`: structural, affine, linear.  Affine
/// admits weakening but not contraction, so it sits strictly between.
pub fn modes_three() -> Modes {
  Modes::new(
    ["U", "A", "L"],
    [[true, true, true], [false, true, true], [false, false, true]],
    [true, true, false],
    [true, false, false],
  )
}

///|
pub let mode_a : Int32 = 1

///|
/// Two incomparable modes over a common linear mode: `U ≥ L`, `V ≥ L`,
/// `U` and `V` unrelated.  Used to model two independent effects; the
/// preorder is a poset that is not a chain.
pub fn modes_diamond() -> Modes {
  Modes::new(
    ["U", "V", "L"],
    [[true, false, true], [false, true, true], [false, false, true]],
    [true, true, false],
    [false, false, false],
  )
}

///|
/// A single linear mode: adjoint logic degenerates to intuitionistic
/// linear logic, which is the conservativity baseline.
pub fn modes_linear() -> Modes {
  Modes::new(["L"], [[true]], [false], [false])
}
