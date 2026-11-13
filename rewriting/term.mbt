///|
/// First-order terms.  Variables are coded by `Int32`; a constant is an
/// application with no arguments.  This is the carrier of every rewriting
/// system in the development: De Morgan normal forms, group presentations,
/// and the equational theory of the cubical connection algebra.
#derive(Debug, Eq, Hash)
pub enum Term {
  Var(Int32)
  App(String, Array[Term])
}

///|
pub fn v(i : Int32) -> Term {
  Var(i)
}

///|
pub fn constant(name : String) -> Term {
  App(name, [])
}

///|
pub fn app(name : String, args : Array[Term]) -> Term {
  App(name, args)
}

///|
/// Number of nodes.
pub fn Term::size(self : Term) -> Int32 {
  match self {
    Var(_) => 1
    App(_, args) => {
      let mut s = 1
      for a in args {
        s = s + a.size()
      }
      s
    }
  }
}

///|
pub fn Term::depth(self : Term) -> Int32 {
  match self {
    Var(_) => 1
    App(_, args) => {
      let mut d = 0
      for a in args {
        let ad = a.depth()
        if ad > d {
          d = ad
        }
      }
      d + 1
    }
  }
}

///|
/// Largest variable index + 1 (0 for a ground term).
pub fn Term::max_var(self : Term) -> Int32 {
  match self {
    Var(i) => i + 1
    App(_, args) => {
      let mut m = 0
      for a in args {
        let am = a.max_var()
        if am > m {
          m = am
        }
      }
      m
    }
  }
}

///|
pub fn Term::occurs(self : Term, x : Int32) -> Bool {
  match self {
    Var(i) => i == x
    App(_, args) => {
      for a in args {
        if a.occurs(x) {
          return true
        }
      }
      false
    }
  }
}

///|
/// Sorted, duplicate-free variable list.
pub fn Term::vars(self : Term) -> Array[Int32] {
  let acc : Array[Int32] = []
  fn go(t : Term) -> Unit {
    match t {
      Var(i) => if !acc.contains(i) { acc.push(i) }
      App(_, args) =>
        for a in args {
          go(a)
        }
    }
  }

  go(self)
  acc.sort()
  acc
}

///|
/// Capture-free substitution (first-order: no binders, so no renaming).
pub fn Term::subst(self : Term, sigma : Map[Int32, Term]) -> Term {
  match self {
    Var(i) =>
      match sigma.get(i) {
        Some(t) => t
        None => self
      }
    App(f, args) => {
      let out : Array[Term] = []
      for a in args {
        out.push(a.subst(sigma))
      }
      App(f, out)
    }
  }
}

///|
/// Shift every variable by `offset`; used to keep two rules variable-disjoint
/// before computing a critical pair.
pub fn Term::rename(self : Term, offset : Int32) -> Term {
  match self {
    Var(i) => Var(i + offset)
    App(f, args) => {
      let out : Array[Term] = []
      for a in args {
        out.push(a.rename(offset))
      }
      App(f, out)
    }
  }
}

///|
/// Human-readable rendering, infix for the usual binary suspects.
pub fn Term::render(self : Term) -> String {
  match self {
    Var(i) => "x\{i}"
    App(f, args) =>
      if args.length() == 0 {
        f
      } else if args.length() == 2 &&
        (f == "*" || f == "+" || f == "/\\" || f == "\\/") {
        "(\{args[0].render()} \{f} \{args[1].render()})"
      } else {
        let sb = StringBuilder()
        sb.write_string(f)
        sb.write_string("(")
        for i in 0..<args.length() {
          if i > 0 {
            sb.write_string(",")
          }
          sb.write_string(args[i].render())
        }
        sb.write_string(")")
        sb.to_string()
      }
  }
}

///|
/// All positions of the term, root first, in depth-first order.  A position
/// is the list of child indices leading from the root.
pub fn Term::positions(self : Term) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  fn go(t : Term, path : Array[Int32]) -> Unit {
    out.push(path[:].to_owned())
    match t {
      Var(_) => ()
      App(_, args) =>
        for i in 0..<args.length() {
          let p = path[:].to_owned()
          p.push(i)
          go(args[i], p)
        }
    }
  }

  go(self, [])
  out
}

///|
/// Non-variable positions: the only places a rewrite rule can overlap.
pub fn Term::nonvar_positions(self : Term) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for p in self.positions() {
    match self.at(p) {
      Some(Var(_)) => ()
      _ => out.push(p)
    }
  }
  out
}

///|
pub fn Term::at(self : Term, pos : Array[Int32]) -> Term? {
  let mut cur = self
  for i in pos {
    match cur {
      App(_, args) =>
        if i >= 0 && i < args.length() {
          cur = args[i]
        } else {
          return None
        }
      Var(_) => return None
    }
  }
  Some(cur)
}

///|
/// Replace the subterm at `pos` by `s`.  Returns `None` for a bad position.
pub fn Term::replace(self : Term, pos : Array[Int32], s : Term) -> Term? {
  if pos.length() == 0 {
    return Some(s)
  }
  match self {
    Var(_) => None
    App(f, args) => {
      let i = pos[0]
      if i < 0 || i >= args.length() {
        return None
      }
      let rest : Array[Int32] = []
      for k in 1..<pos.length() {
        rest.push(pos[k])
      }
      match args[i].replace(rest, s) {
        None => None
        Some(child) => {
          let out : Array[Term] = []
          for k in 0..<args.length() {
            out.push(if k == i { child } else { args[k] })
          }
          Some(App(f, out))
        }
      }
    }
  }
}

///|
/// A rewrite rule `lhs -> rhs`.  Well-formedness requires
/// `vars(rhs) ⊆ vars(lhs)` and a non-variable left-hand side.
#derive(Debug, Eq)
pub struct Rule {
  lhs : Term
  rhs : Term
}

///|
pub fn rule(lhs : Term, rhs : Term) -> Rule {
  Rule::{ lhs, rhs, }
}

///|
pub fn Rule::well_formed(self : Rule) -> Bool {
  match self.lhs {
    Var(_) => false
    App(_, _) => {
      for x in self.rhs.vars() {
        if !self.lhs.occurs(x) {
          return false
        }
      }
      true
    }
  }
}

///|
pub fn Rule::rename(self : Rule, offset : Int32) -> Rule {
  Rule::{ lhs: self.lhs.rename(offset), rhs: self.rhs.rename(offset), }
}

///|
pub fn Rule::render(self : Rule) -> String {
  "\{self.lhs.render()} -> \{self.rhs.render()}"
}
