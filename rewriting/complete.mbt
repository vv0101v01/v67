///|
/// Is `t` reducible by the single rule `r` at *some* position?
fn reducible_by(t : Term, r : Rule) -> Term? {
  for pos in t.positions() {
    match t.at(pos) {
      None => ()
      Some(sub) =>
        match rewrite_root(sub, r) {
          None => ()
          Some(u) =>
            match t.replace(pos, u) {
              Some(whole) => return Some(whole)
              None => ()
            }
        }
    }
  }
  None
}

///|
/// Knuth–Bendix completion, incremental and bounded.
///
/// Invariant: `rules ∪ equations` presents the same equational theory as
/// the input.  Each round normalises one equation, orients it with LPO
/// (which guarantees the rule set stays terminating), interreduces the
/// rule set, and adds only the critical pairs *involving the new rule* —
/// the older pairs were already processed, so recomputing them would be
/// quadratic waste.
///
/// On success the result is convergent: terminating + confluent, hence
/// `joinable` decides the word problem of the original theory.
pub fn complete(
  equations : Array[(Term, Term)],
  prec : Map[String, Int32],
  max_steps~ : Int32 = 200,
  fuel~ : Int32 = 2000,
  max_size~ : Int32 = 200,
) -> CompletionResult {
  let rules : Array[Rule] = []
  let pending : Array[(Term, Term)] = []
  for e in equations {
    pending.push(e)
  }
  fn push_eq(a : Term, b : Term) -> Unit {
    if a != b && a.size() <= max_size && b.size() <= max_size {
      let eq = (a, b)
      if !pending.contains(eq) && !pending.contains((b, a)) {
        pending.push(eq)
      }
    }
  }

  let mut steps = 0
  while pending.length() > 0 && steps < max_steps {
    steps = steps + 1
    // Smallest-equation-first: the standard KB heuristic.  A LIFO or FIFO
    // choice lets large unorientable consequences pile up and the term
    // size explodes; picking the smallest pair keeps the search finite in
    // practice (and is what makes group completion terminate in 10 rules).
    let mut pick = 0
    let mut best = pending[0].0.size() + pending[0].1.size()
    for k in 1..<pending.length() {
      let sz = pending[k].0.size() + pending[k].1.size()
      if sz < best {
        best = sz
        pick = k
      }
    }
    let (a0, b0) = pending[pick]
    ignore(pending.remove(pick))
    let a = normalize(a0, rules, fuel~).term()
    let b = normalize(b0, rules, fuel~).term()
    if a == b {
      continue
    }
    let oriented = if lpo_gt(a, b, prec) {
      Some(rule(a, b))
    } else if lpo_gt(b, a, prec) {
      Some(rule(b, a))
    } else {
      None
    }
    match oriented {
      None => {
        let left_over : Array[(Term, Term)] = []
        for e in pending {
          left_over.push(e)
        }
        left_over.push((a, b))
        return CompletionResult::{
          rules,
          equations_left: left_over,
          steps,
          succeeded: false,
        }
      }
      Some(r) => {
        // collapse: old rules whose left side the new rule reduces go back
        // to the equation pool; compose: right sides stay normalised
        let kept : Array[Rule] = []
        for old in rules {
          match reducible_by(old.lhs, r) {
            Some(reduced) => push_eq(reduced, old.rhs)
            None =>
              kept.push(rule(old.lhs, normalize(old.rhs, [r], fuel~).term()))
          }
        }
        rules.clear()
        for k in kept {
          rules.push(k)
        }
        rules.push(r)
        // simplify: re-normalise the whole equation pool against the new
        // rule set and drop the ones that became trivial
        let simplified : Array[(Term, Term)] = []
        for (ea, eb) in pending {
          let na = normalize(ea, rules, fuel~).term()
          let nb = normalize(eb, rules, fuel~).term()
          if na != nb {
            let eq = (na, nb)
            if !simplified.contains(eq) && !simplified.contains((nb, na)) {
              simplified.push(eq)
            }
          }
        }
        pending.clear()
        for e in simplified {
          pending.push(e)
        }
        // only pairs involving the new rule are new information
        for g in rules {
          for cp in critical_pairs(r, g) {
            push_eq(
              normalize(cp.left, rules, fuel~).term(),
              normalize(cp.right, rules, fuel~).term(),
            )
          }
          if g != r {
            for cp in critical_pairs(g, r) {
              push_eq(
                normalize(cp.left, rules, fuel~).term(),
                normalize(cp.right, rules, fuel~).term(),
              )
            }
          }
        }
      }
    }
  }
  let report = check_local_confluence(rules, fuel~)
  CompletionResult::{
    rules,
    equations_left: pending,
    steps,
    succeeded: pending.length() == 0 &&
    report.locally_confluent() &&
    lpo_terminating(rules, prec),
  }
}
