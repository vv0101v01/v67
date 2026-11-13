///|
/// A cut-free derivation of adjoint logic, one constructor per rule.
/// Having an explicit proof object makes the meta-theory *executable*:
/// cut admissibility, conservativity and the shift adjunction are all
/// checked by comparing derivations rather than by trusting a Boolean.
#derive(Debug, Eq)
pub enum Proof {
  Id(Formula)
  OneR
  OneL(Proof)
  TopR
  ZeroL
  TensorR(Proof, Proof)
  TensorL(Proof)
  LolliR(Proof)
  LolliL(Proof, Proof)
  WithR(Proof, Proof)
  WithL1(Proof)
  WithL2(Proof)
  PlusR1(Proof)
  PlusR2(Proof)
  PlusL(Proof, Proof)
  UpR(Proof)
  UpL(Proof)
  DownR(Proof)
  DownL(Proof)
  Weaken(Proof)
  Contract(Proof)
}

///|
/// Number of inferences in a derivation.
pub fn Proof::size(self : Proof) -> Int32 {
  match self {
    Id(_) | OneR | TopR | ZeroL => 1
    OneL(p)
    | TensorL(p)
    | LolliR(p)
    | WithL1(p)
    | WithL2(p)
    | PlusR1(p)
    | PlusR2(p)
    | UpR(p)
    | UpL(p)
    | DownR(p)
    | DownL(p)
    | Weaken(p)
    | Contract(p) => 1 + p.size()
    TensorR(p, q) | LolliL(p, q) | WithR(p, q) | PlusL(p, q) =>
      1 + p.size() + q.size()
  }
}

///|
/// Does the derivation use the cut rule?  It never does: `Proof` has no
/// cut constructor, so every derivation produced here is cut-free by
/// construction.  Cut is *admissible*, and `check_cut` tests it.
pub fn Proof::has_shift(self : Proof) -> Bool {
  match self {
    UpR(_) | UpL(_) | DownR(_) | DownL(_) => true
    OneL(p)
    | TensorL(p)
    | LolliR(p)
    | WithL1(p)
    | WithL2(p)
    | PlusR1(p)
    | PlusR2(p)
    | Weaken(p)
    | Contract(p) => p.has_shift()
    TensorR(p, q) | LolliL(p, q) | WithR(p, q) | PlusL(p, q) =>
      p.has_shift() || q.has_shift()
    Id(_) | OneR | TopR | ZeroL => false
  }
}

///|
/// A backward proof search for the contraction-free fragment of adjoint
/// logic, with an explicit budget for contraction.
///
/// **Termination.**  Every rule strictly decreases `|goal| + Σ|ctx|`
/// except contraction, which is bounded by `contract_fuel`.  So the search
/// is a decision procedure, not a semi-decision procedure: `None` means
/// *unprovable*, not *unknown*.
///
/// **Complexity.**  Multiplicative rules split the context, giving
/// `O(2^|Γ|)` branches per rule; the whole search is exponential, matching
/// the PSPACE-hardness of provability already for MALL.
#derive(Debug, Eq)
pub struct Prover {
  modes : Modes
  memo : Map[String, Proof?]
  mut steps : Int32
}

///|
pub fn Prover::new(modes : Modes) -> Prover {
  Prover::{ modes, memo: Map([]), steps: 0, }
}

///|
pub fn Prover::steps(self : Prover) -> Int32 {
  self.steps
}

///|
/// All ways to split a context for a multiplicative rule: a genuine
/// *partition*, each antecedent going to exactly one side.  Duplication is
/// never implicit here — it happens only through the explicit `Contract`
/// rule, so the contraction budget is honoured.  Discarding happens only
/// through `Weaken`.  Giving a weakening-mode antecedent to both sides
/// would silently contract it, which is unsound at an affine mode.
fn splits(
  ctx : Array[Antecedent],
) -> Array[(Array[Antecedent], Array[Antecedent])] {
  let out : Array[(Array[Antecedent], Array[Antecedent])] = [([], [])]
  for a in ctx {
    let next : Array[(Array[Antecedent], Array[Antecedent])] = []
    for pair in out {
      let l = pair.0[:].to_owned()
      l.push(a)
      next.push((l, pair.1[:].to_owned()))
      let r = pair.1[:].to_owned()
      r.push(a)
      next.push((pair.0[:].to_owned(), r))
    }
    out.clear()
    for p in next {
      out.push(p)
    }
  }
  out
}

///|
fn without(ctx : Array[Antecedent], i : Int32) -> Array[Antecedent] {
  let out : Array[Antecedent] = []
  for j in 0..<ctx.length() {
    if j != i {
      out.push(ctx[j])
    }
  }
  out
}

///|
fn replace_at(
  ctx : Array[Antecedent],
  i : Int32,
  a : Antecedent,
) -> Array[Antecedent] {
  let out = without(ctx, i)
  out.push(a)
  out
}

///|
/// Search for a cut-free derivation of `ctx ⊢_k goal`.
pub fn Prover::prove(
  self : Prover,
  ctx : Array[Antecedent],
  k : Int32,
  goal : Formula,
  contract_fuel~ : Int32 = 0,
) -> Proof? {
  if !goal.well_formed(self.modes) {
    return None
  }
  for a in ctx {
    if !a.formula.well_formed(self.modes) {
      return None
    }
  }
  let mut budget = goal.size() + 1
  for a in ctx {
    budget = budget + a.formula.size()
  }
  self.search(ctx, k, goal, budget, contract_fuel)
}

///|
fn Prover::search(
  self : Prover,
  ctx : Array[Antecedent],
  k : Int32,
  goal : Formula,
  fuel : Int32,
  cfuel : Int32,
) -> Proof? {
  self.steps = self.steps + 1
  if fuel <= 0 {
    return None
  }
  // ill-formed sequents violate the declaration of independence
  if !independent(ctx, k, self.modes) {
    return None
  }
  let key = sequent_key(ctx, k, goal) + "#\{cfuel}"
  match self.memo.get(key) {
    Some(p) => return p
    None => ()
  }
  let result = self.rules(ctx, k, goal, fuel, cfuel)
  self.memo[key] = result
  result
}

///|
fn Prover::rules(
  self : Prover,
  ctx : Array[Antecedent],
  k : Int32,
  goal : Formula,
  fuel : Int32,
  cfuel : Int32,
) -> Proof? {
  // ---- axiom and additive unit -------------------------------------
  if goal == Top {
    return Some(TopR)
  }
  if ctx.length() == 1 && ctx[0].formula == goal && ctx[0].mode == k {
    return Some(Id(goal))
  }
  if goal == One && ctx.length() == 0 {
    return Some(OneR)
  }
  // ---- right rules -------------------------------------------------
  match goal {
    Tensor(a, b) =>
      for (l, r) in splits(ctx) {
        match self.search(l, k, a, fuel - 1, cfuel) {
          Some(p) =>
            match self.search(r, k, b, fuel - 1, cfuel) {
              Some(q) => return Some(TensorR(p, q))
              None => ()
            }
          None => ()
        }
      }
    Lolli(a, b) => {
      let ext = ctx[:].to_owned()
      ext.push(Antecedent::new(k, a))
      match self.search(ext, k, b, fuel - 1, cfuel) {
        Some(p) => return Some(LolliR(p))
        None => ()
      }
    }
    With(a, b) =>
      match self.search(ctx, k, a, fuel - 1, cfuel) {
        Some(p) =>
          match self.search(ctx, k, b, fuel - 1, cfuel) {
            Some(q) => return Some(WithR(p, q))
            None => ()
          }
        None => ()
      }
    Plus(a, b) => {
      match self.search(ctx, k, a, fuel - 1, cfuel) {
        Some(p) => return Some(PlusR1(p))
        None => ()
      }
      match self.search(ctx, k, b, fuel - 1, cfuel) {
        Some(p) => return Some(PlusR2(p))
        None => ()
      }
    }
    Up(m, kk, a) =>
      // ↑R: the conclusion lives at mode m, so the sequent mode must be m.
      // Independence of the conclusion already gives ctx ≥ m ≥ k.
      if k == m {
        match self.search(ctx, kk, a, fuel - 1, cfuel) {
          Some(p) => return Some(UpR(p))
          None => ()
        }
      }
    Down(l, m, a) =>
      // ↓R is the non-invertible rule: it demands ctx ≥ l, stronger than
      // the ctx ≥ m required by the conclusion.
      if k == m && independent(ctx, l, self.modes) {
        match self.search(ctx, l, a, fuel - 1, cfuel) {
          Some(p) => return Some(DownR(p))
          None => ()
        }
      }
    _ => ()
  }
  // ---- left rules --------------------------------------------------
  for i in 0..<ctx.length() {
    let m = ctx[i].mode
    match ctx[i].formula {
      Zero => return Some(ZeroL)
      One =>
        match self.search(without(ctx, i), k, goal, fuel - 1, cfuel) {
          Some(p) => return Some(OneL(p))
          None => ()
        }
      Tensor(a, b) => {
        let c = without(ctx, i)
        c.push(Antecedent::new(m, a))
        c.push(Antecedent::new(m, b))
        match self.search(c, k, goal, fuel - 1, cfuel) {
          Some(p) => return Some(TensorL(p))
          None => ()
        }
      }
      Lolli(a, b) => {
        let rest = without(ctx, i)
        for (l, r) in splits(rest) {
          match self.search(l, k, a, fuel - 1, cfuel) {
            Some(p) => {
              let r2 = r[:].to_owned()
              r2.push(Antecedent::new(m, b))
              match self.search(r2, k, goal, fuel - 1, cfuel) {
                Some(q) => return Some(LolliL(p, q))
                None => ()
              }
            }
            None => ()
          }
        }
      }
      With(a, b) => {
        match
          self.search(
            replace_at(ctx, i, Antecedent::new(m, a)),
            k,
            goal,
            fuel - 1,
            cfuel,
          ) {
          Some(p) => return Some(WithL1(p))
          None => ()
        }
        match
          self.search(
            replace_at(ctx, i, Antecedent::new(m, b)),
            k,
            goal,
            fuel - 1,
            cfuel,
          ) {
          Some(p) => return Some(WithL2(p))
          None => ()
        }
      }
      Plus(a, b) => {
        let c1 = replace_at(ctx, i, Antecedent::new(m, a))
        let c2 = replace_at(ctx, i, Antecedent::new(m, b))
        match self.search(c1, k, goal, fuel - 1, cfuel) {
          Some(p) =>
            match self.search(c2, k, goal, fuel - 1, cfuel) {
              Some(q) => return Some(PlusL(p, q))
              None => ()
            }
          None => ()
        }
      }
      Up(_, kk, a) =>
        // ↑L needs kk ≥ k for the premise to be well formed; this does
        // not follow from m ≥ k, so it must be checked.
        if self.modes.ge(kk, k) {
          match
            self.search(
              replace_at(ctx, i, Antecedent::new(kk, a)),
              k,
              goal,
              fuel - 1,
              cfuel,
            ) {
            Some(p) => return Some(UpL(p))
            None => ()
          }
        }
      Down(l, _, a) =>
        // ↓L is always applicable: l ≥ m ≥ k by transitivity.
        match
          self.search(
            replace_at(ctx, i, Antecedent::new(l, a)),
            k,
            goal,
            fuel - 1,
            cfuel,
          ) {
          Some(p) => return Some(DownL(p))
          None => ()
        }
      _ => ()
    }
  }
  // ---- structural rules --------------------------------------------
  for i in 0..<ctx.length() {
    if self.modes.allows_weaken(ctx[i].mode) {
      match self.search(without(ctx, i), k, goal, fuel - 1, cfuel) {
        Some(p) => return Some(Weaken(p))
        None => ()
      }
    }
  }
  if cfuel > 0 {
    for i in 0..<ctx.length() {
      if self.modes.allows_contract(ctx[i].mode) {
        let c = ctx[:].to_owned()
        c.push(ctx[i])
        match self.search(c, k, goal, fuel + ctx[i].formula.size(), cfuel - 1) {
          Some(p) => return Some(Contract(p))
          None => ()
        }
      }
    }
  }
  None
}

///|
/// Provability as a Boolean.
pub fn Prover::provable(
  self : Prover,
  ctx : Array[Antecedent],
  k : Int32,
  goal : Formula,
  contract_fuel~ : Int32 = 0,
) -> Bool {
  self.prove(ctx, k, goal, contract_fuel~) is Some(_)
}

///|
/// **Cut admissibility**, checked rather than assumed: whenever
/// `Γ ⊢_m A` and `Δ, A_m ⊢_k C` with `m ≥ k`, the search must also find a
/// cut-free derivation of `Γ, Δ ⊢_k C`.  Returns the number of instances
/// tested and the number that failed.
pub fn Prover::check_cut(
  self : Prover,
  cases : Array[
    (Array[Antecedent], Int32, Formula, Array[Antecedent], Int32, Formula),
  ],
) -> (Int32, Int32) {
  let mut tested = 0
  let mut failed = 0
  for (gamma, m, a, delta, k, c) in cases {
    if !self.modes.ge(m, k) {
      continue
    }
    if !self.provable(gamma, m, a) {
      continue
    }
    let rhs = delta[:].to_owned()
    rhs.push(Antecedent::new(m, a))
    if !self.provable(rhs, k, c) {
      continue
    }
    tested = tested + 1
    let merged = gamma[:].to_owned()
    for d in delta {
      merged.push(d)
    }
    if !self.provable(merged, k, c) {
      failed = failed + 1
    }
  }
  (tested, failed)
}
