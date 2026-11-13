///|
/// Simple types: booleans, naturals, and function spaces.
#derive(Debug, Eq)
pub(all) enum Ty {
  Bool
  Nat
  Arrow(Ty, Ty)
}

///|
pub fn Ty::key(self : Ty) -> String {
  match self {
    Bool => "B"
    Nat => "N"
    Arrow(a, b) => "(\{a.key()}->\{b.key()})"
  }
}

///|
/// Terms in de Bruijn notation.  `Var(i)` counts binders outwards, so `0`
/// is the innermost.  The language is strongly normalising, which is what
/// makes total evaluation — and hence NbE — possible.
#derive(Debug, Eq)
pub(all) enum Term {
  Var(Int32)
  Lam(Ty, Term)
  App(Term, Term)
  BoolLit(Bool)
  NatLit(Int32)
  If(Term, Term, Term)
  Add(Term, Term)
  IsZero(Term)
}

///|
pub fn Term::size(self : Term) -> Int32 {
  match self {
    Var(_) | BoolLit(_) | NatLit(_) => 1
    Lam(_, b) => 1 + b.size()
    App(a, b) | Add(a, b) => 1 + a.size() + b.size()
    If(c, a, b) => 1 + c.size() + a.size() + b.size()
    IsZero(a) => 1 + a.size()
  }
}

///|
/// A canonical key, used to compare normal forms up to α-equivalence
/// (de Bruijn indices make α-equivalence syntactic equality).
pub fn Term::key(self : Term) -> String {
  match self {
    Var(i) => "\{i}"
    Lam(t, b) => "(\\\{t.key()}.\{b.key()})"
    App(a, b) => "(\{a.key()} \{b.key()})"
    BoolLit(b) => if b { "tt" } else { "ff" }
    NatLit(n) => "\{n}"
    If(c, a, b) => "if \{c.key()} then \{a.key()} else \{b.key()}"
    Add(a, b) => "(\{a.key()}+\{b.key()})"
    IsZero(a) => "zero?(\{a.key()})"
  }
}

///|
/// Type inference in a context of types, innermost binder last.
/// Decidable and linear in the term size.
pub fn Term::infer(self : Term, ctx : Array[Ty]) -> Ty? {
  match self {
    Var(i) =>
      if i < 0 || i >= ctx.length() {
        None
      } else {
        Some(ctx[ctx.length() - 1 - i])
      }
    Lam(t, b) => {
      let c = ctx[:].to_owned()
      c.push(t)
      match b.infer(c) {
        None => None
        Some(r) => Some(Arrow(t, r))
      }
    }
    App(f, a) =>
      match (f.infer(ctx), a.infer(ctx)) {
        (Some(Arrow(d, c)), Some(t)) => if d == t { Some(c) } else { None }
        _ => None
      }
    BoolLit(_) => Some(Bool)
    NatLit(_) => Some(Nat)
    If(c, a, b) =>
      match (c.infer(ctx), a.infer(ctx), b.infer(ctx)) {
        (Some(Bool), Some(x), Some(y)) => if x == y { Some(x) } else { None }
        _ => None
      }
    Add(a, b) =>
      match (a.infer(ctx), b.infer(ctx)) {
        (Some(Nat), Some(Nat)) => Some(Nat)
        _ => None
      }
    IsZero(a) =>
      match a.infer(ctx) {
        Some(Nat) => Some(Bool)
        _ => None
      }
  }
}

///|
/// The number of free variables (the de Bruijn *level* the term needs).
pub fn Term::free_vars(self : Term) -> Int32 {
  match self {
    Var(i) => i + 1
    BoolLit(_) | NatLit(_) => 0
    Lam(_, b) => {
      let n = b.free_vars()
      if n > 0 {
        n - 1
      } else {
        0
      }
    }
    App(a, b) | Add(a, b) => {
      let x = a.free_vars()
      let y = b.free_vars()
      if x > y {
        x
      } else {
        y
      }
    }
    If(c, a, b) => {
      let mut m = c.free_vars()
      if a.free_vars() > m {
        m = a.free_vars()
      }
      if b.free_vars() > m {
        m = b.free_vars()
      }
      m
    }
    IsZero(a) => a.free_vars()
  }
}

///|
/// A typing context of `n` booleans, used for symbolic execution.
pub fn bool_ctx(n : Int32) -> Array[Ty] {
  Array::make(n, Ty::Bool)
}
