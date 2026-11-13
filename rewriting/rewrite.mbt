///|
/// One-way matching: find `sigma` with `sigma(pattern) = subject`.
/// Returns `None` on clash.  Matching is decidable in `O(|pattern|)`
/// map operations plus the cost of term equality.
pub fn match_term(pattern : Term, subject : Term) -> Map[Int32, Term]? {
  let sigma : Map[Int32, Term] = Map([])
  fn go(p : Term, s : Term) -> Bool {
    match p {
      Var(i) =>
        match sigma.get(i) {
          Some(prev) => prev == s
          None => {
            sigma[i] = s
            true
          }
        }
      App(f, ps) =>
        match s {
          App(g, ss) => {
            if f != g || ps.length() != ss.length() {
              return false
            }
            for k in 0..<ps.length() {
              if !go(ps[k], ss[k]) {
                return false
              }
            }
            true
          }
          Var(_) => false
        }
    }
  }

  if go(pattern, subject) {
    Some(sigma)
  } else {
    None
  }
}

///|
/// Syntactic unification (Robinson).  Returns the most general unifier, or
/// `None` when the two terms are not unifiable.  Occurs-check included, so
/// this is decidability of first-order unification, not Prolog's version.
pub fn unify(a : Term, b : Term) -> Map[Int32, Term]? {
  let sigma : Map[Int32, Term] = Map([])
  fn resolve(t : Term) -> Term {
    let mut cur = t
    while true {
      match cur {
        Var(i) =>
          match sigma.get(i) {
            Some(u) => cur = u
            None => return cur
          }
        App(_, _) => return cur
      }
    }
    cur
  }

  fn occurs_after_resolve(t : Term, x : Int32) -> Bool {
    match resolve(t) {
      Var(i) => i == x
      App(_, args) => {
        for a in args {
          if occurs_after_resolve(a, x) {
            return true
          }
        }
        false
      }
    }
  }

  let pending : Array[(Term, Term)] = [(a, b)]
  while pending.length() > 0 {
    let (s0, t0) = match pending.pop() {
      Some(pair) => pair
      None => break
    }
    let s = resolve(s0)
    let t = resolve(t0)
    match (s, t) {
      (Var(i), Var(j)) => if i != j { sigma[i] = Var(j) }
      (Var(i), _) => {
        if occurs_after_resolve(t, i) {
          return None
        }
        sigma[i] = t
      }
      (_, Var(j)) => {
        if occurs_after_resolve(s, j) {
          return None
        }
        sigma[j] = s
      }
      (App(f, fs), App(g, gs)) => {
        if f != g || fs.length() != gs.length() {
          return None
        }
        for k in 0..<fs.length() {
          pending.push((fs[k], gs[k]))
        }
      }
    }
  }
  // idempotent presentation: fully resolve every binding
  fn walk(t : Term) -> Term {
    match t {
      Var(i) =>
        match sigma.get(i) {
          Some(u) => walk(u)
          None => Var(i)
        }
      App(f, args) => {
        let out : Array[Term] = []
        for x in args {
          out.push(walk(x))
        }
        App(f, out)
      }
    }
  }

  let out : Map[Int32, Term] = Map([])
  for (k, val) in sigma {
    out[k] = walk(val)
  }
  Some(out)
}

///|
/// Apply a rule at the root, if it matches.
pub fn rewrite_root(t : Term, r : Rule) -> Term? {
  match match_term(r.lhs, t) {
    Some(sigma) => Some(r.rhs.subst(sigma))
    None => None
  }
}

///|
/// Leftmost-outermost one-step rewriting.  Returns the first reduct found
/// in a root-first, left-to-right scan, or `None` when `t` is a normal form.
pub fn rewrite_step(t : Term, rules : Array[Rule]) -> Term? {
  for r in rules {
    match rewrite_root(t, r) {
      Some(u) => return Some(u)
      None => ()
    }
  }
  match t {
    Var(_) => None
    App(f, args) => {
      for i in 0..<args.length() {
        match rewrite_step(args[i], rules) {
          Some(u) => {
            let out : Array[Term] = []
            for k in 0..<args.length() {
              out.push(if k == i { u } else { args[k] })
            }
            return Some(App(f, out))
          }
          None => ()
        }
      }
      None
    }
  }
}

///|
/// Outcome of normalisation.  `fuel` bounds the number of steps so that a
/// non-terminating system reports `Diverged` instead of looping forever —
/// termination is undecidable in general, so the engine is honest about it.
#derive(Debug, Eq)
pub enum NormalForm {
  Normal(Term)
  Diverged(Term)
}

///|
pub fn normalize(
  t : Term,
  rules : Array[Rule],
  fuel~ : Int32 = 10000,
) -> NormalForm {
  let mut cur = t
  let mut steps = 0
  while steps < fuel {
    match rewrite_step(cur, rules) {
      None => return Normal(cur)
      Some(u) => {
        cur = u
        steps = steps + 1
      }
    }
  }
  Diverged(cur)
}

///|
pub fn NormalForm::term(self : NormalForm) -> Term {
  match self {
    Normal(t) => t
    Diverged(t) => t
  }
}

///|
pub fn is_normal(t : Term, rules : Array[Rule]) -> Bool {
  match rewrite_step(t, rules) {
    None => true
    Some(_) => false
  }
}

///|
/// Joinability: both terms normalise to the same term.  For a confluent and
/// terminating system this *is* the decision procedure for the equational
/// theory (the word problem).
pub fn joinable(
  a : Term,
  b : Term,
  rules : Array[Rule],
  fuel~ : Int32 = 10000,
) -> Bool {
  normalize(a, rules, fuel~) == normalize(b, rules, fuel~)
}

///|
/// All one-step reducts of `t` (every rule at every position).  Used to
/// check local confluence exhaustively on small terms.
pub fn all_reducts(t : Term, rules : Array[Rule]) -> Array[Term] {
  let out : Array[Term] = []
  for pos in t.positions() {
    match t.at(pos) {
      None => ()
      Some(sub) =>
        for r in rules {
          match rewrite_root(sub, r) {
            None => ()
            Some(u) =>
              match t.replace(pos, u) {
                Some(whole) => if !out.contains(whole) { out.push(whole) }
                None => ()
              }
          }
        }
    }
  }
  out
}
