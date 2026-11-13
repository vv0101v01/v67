///|
/// A critical pair of rules `r1`, `r2` at a non-variable position of `r1`'s
/// left-hand side: the two ways of rewriting the overlap.  `cp_left` peels
/// the outer rule, `cp_right` peels the inner one.
#derive(Debug, Eq)
pub struct CriticalPair {
  left : Term
  right : Term
  outer : Rule
  inner : Rule
  pos : Array[Int32]
}

///|
/// All critical pairs between two rules (including a rule with itself, at
/// every non-variable position, with variables renamed apart).
///
/// The Critical Pair Lemma: a term rewriting system is locally confluent
/// iff all its critical pairs are joinable.  Since there are finitely many
/// critical pairs, *local* confluence is decidable; with termination it
/// upgrades to confluence (Newman's lemma), hence to a decidable word
/// problem.
pub fn critical_pairs(r1 : Rule, r2 : Rule) -> Array[CriticalPair] {
  let shift = r1.lhs.max_var() + r1.rhs.max_var() + 1
  let r2r = r2.rename(shift)
  let out : Array[CriticalPair] = []
  for pos in r1.lhs.nonvar_positions() {
    match r1.lhs.at(pos) {
      None => ()
      Some(sub) =>
        match unify(sub, r2r.lhs) {
          None => ()
          Some(sigma) => {
            let l = r1.rhs.subst(sigma)
            let inner_red = r2r.rhs.subst(sigma)
            let whole = r1.lhs.subst(sigma)
            match whole.replace(pos, inner_red) {
              None => ()
              Some(r) =>
                out.push(CriticalPair::{
                  left: l,
                  right: r,
                  outer: r1,
                  inner: r2,
                  pos,
                })
            }
          }
        }
    }
  }
  out
}

///|
/// Every critical pair of a system, as `(left, right)` terms.
pub fn system_critical_pairs(rules : Array[Rule]) -> Array[(Term, Term)] {
  let out : Array[(Term, Term)] = []
  for r1 in rules {
    for r2 in rules {
      for cp in critical_pairs(r1, r2) {
        // trivial pairs (same term) carry no information
        if cp.left != cp.right {
          out.push((cp.left, cp.right))
        }
      }
    }
  }
  out
}

///|
/// Report of a confluence check.
#derive(Debug, Eq)
pub struct ConfluenceReport {
  pairs : Int32
  joinable_pairs : Int32
  unjoinable : Array[(Term, Term)]
}

///|
pub fn ConfluenceReport::locally_confluent(self : ConfluenceReport) -> Bool {
  self.unjoinable.length() == 0
}

///|
/// Decide local confluence by the critical pair lemma.
pub fn check_local_confluence(
  rules : Array[Rule],
  fuel~ : Int32 = 4000,
) -> ConfluenceReport {
  let cps = system_critical_pairs(rules)
  let bad : Array[(Term, Term)] = []
  let mut good = 0
  for (a, b) in cps {
    if joinable(a, b, rules, fuel~) {
      good = good + 1
    } else {
      bad.push((a, b))
    }
  }
  ConfluenceReport::{
    pairs: cps.length(),
    joinable_pairs: good,
    unjoinable: bad,
  }
}

///|
/// A lexicographic path order (LPO) with a given precedence on symbols.
/// `prec[f] > prec[g]` means `f` binds "higher".  LPO is a well-founded
/// simplification order, so `lhs > rhs` for every rule certifies
/// termination of the whole system.
pub fn lpo_gt(s : Term, t : Term, prec : Map[String, Int32]) -> Bool {
  fn weight(f : String) -> Int32 {
    prec.get_or_default(f, 0)
  }

  fn gt(a : Term, b : Term) -> Bool {
    match (a, b) {
      (_, Var(x)) => a != b && a.occurs(x)
      (Var(_), _) => false
      (App(f, ss), App(g, tt)) => {
        // (1) some argument of s is >= t
        for si in ss {
          if si == b || gt(si, b) {
            return true
          }
        }
        // (2) f > g and s > every argument of t
        if weight(f) > weight(g) {
          let mut all = true
          for tj in tt {
            if !gt(a, tj) {
              all = false
            }
          }
          if all {
            return true
          }
        }
        // (3) f = g, lexicographic on arguments, and s > every argument of t
        if f == g {
          let mut all = true
          for tj in tt {
            if !gt(a, tj) {
              all = false
            }
          }
          if all {
            let n = if ss.length() < tt.length() {
              ss.length()
            } else {
              tt.length()
            }
            for k in 0..<n {
              if ss[k] == tt[k] {
                continue
              }
              return gt(ss[k], tt[k])
            }
            return ss.length() > tt.length()
          }
        }
        false
      }
    }
  }

  gt(s, t)
}

///|
/// Termination certificate: every rule strictly decreases in LPO.
pub fn lpo_terminating(rules : Array[Rule], prec : Map[String, Int32]) -> Bool {
  for r in rules {
    if !lpo_gt(r.lhs, r.rhs, prec) {
      return false
    }
  }
  true
}

///|
/// Cheap termination certificate: strict size decrease with the variable
/// condition (each variable occurs at least as often on the left).  This
/// covers associativity-free systems such as De Morgan normalisation.
pub fn size_terminating(rules : Array[Rule]) -> Bool {
  for r in rules {
    if r.lhs.size() <= r.rhs.size() {
      return false
    }
    for x in r.rhs.vars() {
      if count_var(r.lhs, x) < count_var(r.rhs, x) {
        return false
      }
    }
  }
  true
}

///|
pub fn count_var(t : Term, x : Int32) -> Int32 {
  match t {
    Var(i) => if i == x { 1 } else { 0 }
    App(_, args) => {
      let mut s = 0
      for a in args {
        s = s + count_var(a, x)
      }
      s
    }
  }
}

///|
/// Result of Knuth–Bendix completion.
#derive(Debug)
pub struct CompletionResult {
  rules : Array[Rule]
  equations_left : Array[(Term, Term)]
  steps : Int32
  succeeded : Bool
}
