///|
/// A completely independent, substitution-based β-normaliser.  It exists
/// only to cross-validate NbE: two implementations with nothing in common
/// (one substitutes syntax, the other evaluates into a semantic domain)
/// must agree on every normal form.
fn shift(t : Term, d : Int32, cutoff : Int32) -> Term {
  match t {
    Var(i) => if i >= cutoff { Var(i + d) } else { Var(i) }
    Lam(ty, b) => Lam(ty, shift(b, d, cutoff + 1))
    App(a, b) => App(shift(a, d, cutoff), shift(b, d, cutoff))
    If(c, a, b) =>
      If(shift(c, d, cutoff), shift(a, d, cutoff), shift(b, d, cutoff))
    Add(a, b) => Add(shift(a, d, cutoff), shift(b, d, cutoff))
    IsZero(a) => IsZero(shift(a, d, cutoff))
    BoolLit(_) | NatLit(_) => t
  }
}

///|
/// `t[j := s]`, decrementing the indices above `j` so that the binder is
/// removed.  The standard capture-avoiding de Bruijn substitution.
fn subst(t : Term, j : Int32, s : Term) -> Term {
  match t {
    Var(i) =>
      if i == j {
        shift(s, j, 0)
      } else if i > j {
        Var(i - 1)
      } else {
        Var(i)
      }
    Lam(ty, b) => Lam(ty, subst(b, j + 1, s))
    App(a, b) => App(subst(a, j, s), subst(b, j, s))
    If(c, a, b) => If(subst(c, j, s), subst(a, j, s), subst(b, j, s))
    Add(a, b) => Add(subst(a, j, s), subst(b, j, s))
    IsZero(a) => IsZero(subst(a, j, s))
    BoolLit(_) | NatLit(_) => t
  }
}

///|
/// Weak head normal form by repeated head reduction.
pub fn whnf(t : Term) -> Term {
  let mut cur = t
  for _ in 0..<10000 {
    match cur {
      App(f, a) => {
        let f2 = whnf(f)
        match f2 {
          Lam(_, body) => cur = subst(body, 0, a)
          _ => return App(f2, a)
        }
      }
      If(c, a, b) => {
        let c2 = whnf(c)
        match c2 {
          BoolLit(true) => cur = a
          BoolLit(false) => cur = b
          _ => return If(c2, a, b)
        }
      }
      Add(a, b) => {
        let x = whnf(a)
        let y = whnf(b)
        match (x, y) {
          (NatLit(m), NatLit(n)) => return NatLit(m + n)
          _ => return Add(x, y)
        }
      }
      IsZero(a) => {
        let x = whnf(a)
        match x {
          NatLit(n) => return BoolLit(n == 0)
          _ => return IsZero(x)
        }
      }
      _ => return cur
    }
  }
  cur
}

///|
/// Full β-normal form, normalising under binders and inside residual
/// conditionals.  Like `normalize`, this produces β-normal forms without
/// η-contraction, so the two can be compared syntactically.
pub fn beta_nf(t : Term) -> Term {
  match whnf(t) {
    Lam(ty, b) => Lam(ty, beta_nf(b))
    App(f, a) => App(beta_nf(f), beta_nf(a))
    If(c, a, b) => If(beta_nf(c), beta_nf(a), beta_nf(b))
    Add(a, b) => Add(beta_nf(a), beta_nf(b))
    IsZero(a) => IsZero(beta_nf(a))
    other => other
  }
}
