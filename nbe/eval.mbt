///|
/// Semantic values for **normalisation by evaluation**.  A value is either
/// a canonical introduction (a boolean, a natural, a closure) or a
/// *neutral*: a stuck elimination headed by a free variable.  Separating
/// neutrals from canonical forms is the whole trick — it makes the
/// semantic domain closed under application, so `eval` is total and
/// `reify` can read a βη-normal form back off a value.
#derive(Debug, Eq)
pub(all) enum Value {
  VBool(Bool)
  VNat(Int32)
  /// closure: the type, the captured environment, and the body
  VLam(Ty, Array[Value], Term)
  VNe(Neutral)
}

///|
/// Neutral (stuck) computations, headed by a variable at a de Bruijn
/// *level*.  Levels — not indices — are used here so that values are
/// stable under weakening of the context.
#derive(Debug, Eq)
pub(all) enum Neutral {
  NVar(Int32)
  NApp(Neutral, Value)
  NIf(Value, Value, Value)
  NAdd(Value, Value)
  NIsZero(Value)
}

///|
/// The environment of a symbolic run: `n` free boolean variables, as
/// neutrals at levels `0 ..< n`.  Evaluating a term in this environment is
/// *exactly* symbolic execution — no separate interpreter is needed.
pub fn symbolic_env(n : Int32) -> Array[Value] {
  let out : Array[Value] = []
  for i in 0..<n {
    out.push(VNe(NVar(i)))
  }
  out
}

///|
/// The concrete environment for a truth assignment.
pub fn concrete_env(asg : Array[Bool]) -> Array[Value] {
  let out : Array[Value] = []
  for b in asg {
    out.push(VBool(b))
  }
  out
}

///|
/// Evaluate a term to a semantic value.  Total on well-typed terms:
/// the language is strongly normalising, so no fuel is required.
pub fn eval(env : Array[Value], t : Term) -> Value {
  match t {
    Var(i) => env[env.length() - 1 - i]
    Lam(ty, b) => VLam(ty, env[:].to_owned(), b)
    App(f, a) => apply(eval(env, f), eval(env, a))
    BoolLit(b) => VBool(b)
    NatLit(n) => VNat(n)
    If(c, a, b) =>
      match eval(env, c) {
        VBool(true) => eval(env, a)
        VBool(false) => eval(env, b)
        // a stuck condition: residualise the branch.  Both branches are
        // evaluated, which is precisely what symbolic execution does.
        cv => VNe(NIf(cv, eval(env, a), eval(env, b)))
      }
    Add(a, b) => {
      let x = eval(env, a)
      let y = eval(env, b)
      match (x, y) {
        (VNat(m), VNat(n)) => VNat(m + n)
        _ => VNe(NAdd(x, y))
      }
    }
    IsZero(a) =>
      match eval(env, a) {
        VNat(0) => VBool(true)
        VNat(_) => VBool(false)
        v => VNe(NIsZero(v))
      }
  }
}

///|
/// Semantic application.  On a closure it runs the body; on a neutral it
/// extends the stuck spine.  This is the only place β-reduction happens.
pub fn apply(f : Value, a : Value) -> Value {
  match f {
    VLam(_, env, body) => {
      let e = env[:].to_owned()
      e.push(a)
      eval(e, body)
    }
    VNe(n) => VNe(NApp(n, a))
    _ => abort("apply: not a function (ill-typed term)")
  }
}

///|
/// Read a value back as a βη-normal term at the given de Bruijn level.
/// On a function it η-expands: apply to a fresh variable and reify the
/// result.  That is why NbE produces η-long normal forms.
pub fn reify(level : Int32, v : Value) -> Term {
  match v {
    VBool(b) => BoolLit(b)
    VNat(n) => NatLit(n)
    VLam(ty, _, _) => Lam(ty, reify(level + 1, apply(v, VNe(NVar(level)))))
    VNe(n) => quote(level, n)
  }
}

///|
fn quote(level : Int32, n : Neutral) -> Term {
  match n {
    NVar(l) => Var(level - l - 1)
    NApp(f, a) => App(quote(level, f), reify(level, a))
    NIf(c, a, b) => If(reify(level, c), reify(level, a), reify(level, b))
    NAdd(a, b) => Add(reify(level, a), reify(level, b))
    NIsZero(a) => IsZero(reify(level, a))
  }
}

///|
/// **Normalisation by evaluation**: `nf = reify ∘ eval`.  The result is the
/// βη-normal form, in η-long form, and it is α-canonical because de Bruijn
/// indices are used throughout.
pub fn normalize(ctx : Array[Ty], t : Term) -> Term {
  let n = ctx.length()
  reify(n, eval(symbolic_env(n), t))
}

///|
/// Normalise a closed term of base type to a literal.
pub fn normalize_closed(t : Term) -> Term {
  reify(0, eval([], t))
}

///|
/// Does the term mention de Bruijn index `i` (at the given binder depth)?
fn mentions(t : Term, i : Int32) -> Bool {
  match t {
    Var(j) => j == i
    Lam(_, b) => mentions(b, i + 1)
    App(a, b) | Add(a, b) => mentions(a, i) || mentions(b, i)
    If(c, a, b) => mentions(c, i) || mentions(a, i) || mentions(b, i)
    IsZero(a) => mentions(a, i)
    BoolLit(_) | NatLit(_) => false
  }
}

///|
/// η-contraction: `λx. f x` becomes `f` when `x` is not free in `f`.
/// NbE as written produces β-normal forms that are η-*expanded* at every
/// lambda; contracting gives the βη-normal form.
pub fn eta_contract(t : Term) -> Term {
  match t {
    Lam(ty, b) => {
      let b2 = eta_contract(b)
      match b2 {
        App(f, Var(0)) =>
          if mentions(f, 0) {
            Lam(ty, b2)
          } else {
            shift(f, -1, 0)
          }
        _ => Lam(ty, b2)
      }
    }
    App(a, b) => App(eta_contract(a), eta_contract(b))
    If(c, a, b) => If(eta_contract(c), eta_contract(a), eta_contract(b))
    Add(a, b) => Add(eta_contract(a), eta_contract(b))
    IsZero(a) => IsZero(eta_contract(a))
    other => other
  }
}

///|
/// The βη-normal form: NbE followed by η-contraction.
pub fn normalize_eta(ctx : Array[Ty], t : Term) -> Term {
  eta_contract(normalize(ctx, t))
}

///|
/// Decidable β-equality: the β-normal forms are canonical, so comparing
/// their keys decides it.
pub fn beta_equal(ctx : Array[Ty], a : Term, b : Term) -> Bool {
  normalize(ctx, a).key() == normalize(ctx, b).key()
}

///|
/// Decidable βη-equality — the point of NbE.  Two terms are βη-equal iff
/// their βη-normal forms are syntactically identical.
pub fn beta_eta_equal(ctx : Array[Ty], a : Term, b : Term) -> Bool {
  normalize_eta(ctx, a).key() == normalize_eta(ctx, b).key()
}

///|
/// **Extensional equality** of two closed boolean functions, decided by
/// exhaustive evaluation.  This is strictly coarser than βη-equality:
/// `not (not x)` and `x` have different normal forms (NbE does not know
/// the Boolean η-rule) but the same truth table.  Deciding it needs the
/// base type to be finite, which is exactly what symbolic execution
/// exploits.
pub fn extensional_equal_bool(a : Term, b : Term) -> Bool {
  for v in [false, true] {
    let lit = Term::BoolLit(v)
    if eval([], App(a, lit)) != eval([], App(b, lit)) {
      return false
    }
  }
  true
}
