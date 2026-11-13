///|
/// Some reusable terms.
fn t_id(ty : Ty) -> Term {
  Lam(ty, Var(0))
}

///|
fn t_not() -> Term {
  Lam(Bool, If(Var(0), BoolLit(false), BoolLit(true)))
}

///|
test "type inference accepts well-typed terms and rejects the rest" {
  assert_eq(t_id(Bool).infer([]), Some(Arrow(Bool, Bool)))
  assert_eq(App(t_id(Nat), NatLit(3)).infer([]), Some(Nat))
  assert_eq(If(BoolLit(true), NatLit(1), NatLit(2)).infer([]), Some(Nat))
  assert_eq(IsZero(Add(NatLit(1), NatLit(2))).infer([]), Some(Bool))
  // a free variable is out of scope
  assert_true(Var(0).infer([]) is None)
  // applying a boolean
  assert_true(App(BoolLit(true), NatLit(0)).infer([]) is None)
  // branches of different type
  assert_true(If(BoolLit(true), NatLit(1), BoolLit(false)).infer([]) is None)
  // the argument type must match
  assert_true(App(t_id(Nat), BoolLit(true)).infer([]) is None)
  // a higher-order term
  let twice = Lam(
    Arrow(Bool, Bool),
    Lam(Bool, App(Var(1), App(Var(1), Var(0)))),
  )
  assert_eq(twice.infer([]), Some(Arrow(Arrow(Bool, Bool), Arrow(Bool, Bool))))
  assert_eq(App(App(twice, t_not()), BoolLit(true)).infer([]), Some(Bool))
}

///|
test "NbE agrees with an independent substitution-based normaliser" {
  let twice = Lam(
    Arrow(Bool, Bool),
    Lam(Bool, App(Var(1), App(Var(1), Var(0)))),
  )
  let cases : Array[(Array[Ty], Term)] = [
    ([], App(t_id(Nat), NatLit(7))),
    ([], App(t_id(Bool), BoolLit(false))),
    ([], If(BoolLit(true), NatLit(1), NatLit(2))),
    ([], Add(NatLit(2), NatLit(40))),
    ([], IsZero(NatLit(0))),
    ([], IsZero(Add(NatLit(1), NatLit(2)))),
    ([], App(t_not(), BoolLit(true))),
    ([], App(App(twice, t_not()), BoolLit(true))),
    ([], App(App(twice, t_not()), BoolLit(false))),
    ([Bool], If(Var(0), NatLit(1), NatLit(2))),
    ([Bool, Bool], If(Var(1), If(Var(0), NatLit(1), NatLit(2)), NatLit(3))),
    ([Arrow(Bool, Bool), Bool], App(Var(1), Var(0))),
    ([Arrow(Bool, Bool)], Lam(Bool, App(Var(1), Var(0)))),
    ([Nat], Add(Var(0), NatLit(1))),
    ([Nat], IsZero(Add(Var(0), NatLit(0)))),
    ([], Lam(Bool, If(Var(0), BoolLit(true), BoolLit(false)))),
  ]
  for (ctx, t) in cases {
    // both normalisers produce the same β-normal form
    let by_nbe = normalize(ctx, t)
    let by_subst = beta_nf(t)
    assert_eq(by_nbe.key(), by_subst.key())
    // and normalisation is idempotent
    assert_eq(normalize(ctx, by_nbe).key(), by_nbe.key())
    assert_eq(beta_nf(by_subst).key(), by_subst.key())
  }
}

///|
test "NbE decides beta-eta equality, and eta really is a separate step" {
  let ctx = [Ty::Arrow(Bool, Bool)]
  let f = Term::Var(0)
  let eta_f = Term::Lam(Bool, App(Var(1), Var(0)))
  // β-normal forms differ: NbE η-expands at lambdas
  assert_false(beta_equal(ctx, f, eta_f))
  // βη-normal forms coincide
  assert_true(beta_eta_equal(ctx, f, eta_f))
  assert_eq(normalize_eta(ctx, eta_f).key(), f.key())
  // Double negation is extensionally the identity but NOT βη-equal to it:
  // NbE has no Boolean η-rule, so the normal form stays a nested `if`.
  // Deciding extensional equality needs the base type to be finite.
  let twice = Lam(
    Arrow(Bool, Bool),
    Lam(Bool, App(Var(1), App(Var(1), Var(0)))),
  )
  let dn = App(twice, t_not())
  assert_false(beta_eta_equal([], dn, t_id(Bool)))
  assert_true(extensional_equal_bool(dn, t_id(Bool)))
  assert_false(extensional_equal_bool(t_not(), t_id(Bool)))
  // and the identity is not equal to negation
  assert_false(beta_eta_equal([], t_id(Bool), t_not()))
  // η-contraction does not fire when the variable really occurs
  let ctx2 = [Ty::Arrow(Bool, Arrow(Bool, Bool))]
  let g = Term::Lam(Bool, App(App(Var(1), Var(0)), Var(0)))
  assert_eq(normalize_eta(ctx2, g).key(), normalize(ctx2, g).key())
}

///|
test "symbolic execution is NbE with free variables: the decision tree" {
  // if x then (if y then 1 else 2) else 3
  let prog = Term::If(Var(1), If(Var(0), NatLit(1), NatLit(2)), NatLit(3))
  let sym = Symbolic::new(2)
  let ls = sym.run_nbe(prog)
  // three paths, with guards x/\y, x/\~y, ~x
  assert_eq(ls.length(), 3)
  assert_eq(ls[0].value, VNat(1))
  assert_eq(ls[1].value, VNat(2))
  assert_eq(ls[2].value, VNat(3))
  // Var(1) is the outer binder x (level 0), Var(0) is y (level 1)
  assert_true(
    guard_dm_eq(
      ls[0].path_cond,
      @cubical.DAnd(@cubical.DVar(0), @cubical.DVar(1)),
    ),
  )
  assert_true(
    guard_dm_eq(
      ls[1].path_cond,
      @cubical.DAnd(@cubical.DVar(0), @cubical.DNot(@cubical.DVar(1))),
    ),
  )
  assert_true(guard_dm_eq(ls[2].path_cond, @cubical.DNot(@cubical.DVar(0))))
  // the pruning executor agrees path for path
  let pruned = sym.run(prog)
  assert_eq(pruned.length(), 3)
  for i in 0..<3 {
    assert_eq(pruned[i].value, ls[i].value)
    assert_true(sym.guard_equiv(pruned[i].path_cond, ls[i].path_cond))
  }
}

///|
test "infeasible paths: De Morgan equality does not see them, feasibility does" {
  // if x then (if y then 1 else 2) else (if x then 3 else 4)
  let prog = Term::If(
    Var(1),
    If(Var(0), NatLit(1), NatLit(2)),
    If(Var(1), NatLit(3), NatLit(4)),
  )
  let sym = Symbolic::new(2)
  let all_paths = sym.run_nbe(prog)
  assert_eq(all_paths.length(), 4)
  // the third path has path_cond ~x /\ x
  let bad = all_paths[2].path_cond
  assert_true(
    guard_dm_eq(
      bad,
      @cubical.DAnd(@cubical.DNot(@cubical.DVar(0)), @cubical.DVar(0)),
    ),
  )
  // as a dimension term it is NOT zero: the free De Morgan algebra is not
  // Boolean, so the canonical form keeps the contradiction visible
  assert_false(guard_dm_eq(bad, @cubical.DZero))
  // but as a Boolean condition it is unsatisfiable
  assert_false(sym.feasible(bad))
  assert_eq(sym.model_count(bad), 0)
  // so the pruning executor drops it
  let pruned = sym.run(prog)
  assert_eq(pruned.length(), 3)
  assert_eq(pruned.map(fn(l) { l.value }), [VNat(1), VNat(2), VNat(4)])
  assert_eq(feasible_leaves(sym, all_paths).length(), 3)
}

///|
test "De Morgan laws hold for guards, excluded middle does not" {
  let sym = Symbolic::new(2)
  let x = @cubical.DVar(0)
  let y = @cubical.DVar(1)
  // De Morgan duality is an equality of the free algebra
  assert_true(
    guard_dm_eq(
      @cubical.DNot(@cubical.DOr(x, y)),
      @cubical.DAnd(@cubical.DNot(x), @cubical.DNot(y)),
    ),
  )
  assert_true(
    guard_dm_eq(
      @cubical.DNot(@cubical.DAnd(x, y)),
      @cubical.DOr(@cubical.DNot(x), @cubical.DNot(y)),
    ),
  )
  // involution
  assert_true(guard_dm_eq(@cubical.DNot(@cubical.DNot(x)), x))
  // excluded middle and non-contradiction fail in the De Morgan algebra
  assert_false(guard_dm_eq(@cubical.DOr(x, @cubical.DNot(x)), @cubical.DOne))
  assert_false(guard_dm_eq(@cubical.DAnd(x, @cubical.DNot(x)), @cubical.DZero))
  // yet they hold Boolean-wise, which is the right notion for paths
  assert_true(sym.guard_equiv(@cubical.DOr(x, @cubical.DNot(x)), @cubical.DOne))
  assert_true(
    sym.guard_equiv(@cubical.DAnd(x, @cubical.DNot(x)), @cubical.DZero),
  )
}

///|
test "symbolic execution is sound and complete against concrete evaluation" {
  let programs : Array[(Int32, Term)] = [
    (1, If(Var(0), NatLit(1), NatLit(2))),
    (2, If(Var(1), If(Var(0), NatLit(1), NatLit(2)), NatLit(3))),
    (
      2,
      If(
        Var(1),
        If(Var(0), NatLit(1), NatLit(2)),
        If(Var(1), NatLit(3), NatLit(4)),
      ),
    ),
    // a conditional *inside* a condition: the two executors build
    // different trees, but must agree on every concrete assignment
    (2, If(If(Var(1), Var(0), BoolLit(false)), NatLit(10), NatLit(20))),
    (
      3,
      If(
        Var(2),
        If(Var(1), NatLit(1), If(Var(0), NatLit(2), NatLit(3))),
        NatLit(4),
      ),
    ),
    // a beta-redex: symbolic execution must reduce it
    (1, App(Lam(Bool, If(Var(0), NatLit(5), NatLit(6))), Var(0))),
    // higher order: twice not applied to a symbolic boolean
    (
      1,
      App(
        App(
          Lam(Arrow(Bool, Bool), Lam(Bool, App(Var(1), App(Var(1), Var(0))))),
          t_not(),
        ),
        Var(0),
      ),
    ),
    // booleans as results, and arithmetic
    (2, If(Var(1), Add(NatLit(1), NatLit(2)), Add(NatLit(4), NatLit(5)))),
    (1, IsZero(If(Var(0), NatLit(0), NatLit(7)))),
  ]
  for (n, t) in programs {
    let sym = Symbolic::new(n)
    // both executors are sound and complete
    let (tested, bad) = sym.check_sound(t)
    assert_eq(tested, @core.ipow2(n))
    assert_eq(bad, 0)
    let (tested2, bad2) = sym.check_sound_nbe(t)
    assert_eq(tested2, @core.ipow2(n))
    assert_eq(bad2, 0)
    // and the feasible paths partition the assignment space
    assert_true(sym.check_partition(t))
  }
}

///|
test "the two symbolic executors agree path for path on atomic conditions" {
  // When every condition is a variable or a literal, the residual tree
  // built by NbE and the eagerly split tree built by the executor have
  // exactly the same shape, so the feasible leaves coincide as lists.
  let programs : Array[(Int32, Term)] = [
    (1, If(Var(0), NatLit(1), NatLit(2))),
    (2, If(Var(1), If(Var(0), NatLit(1), NatLit(2)), NatLit(3))),
    (
      2,
      If(
        Var(1),
        If(Var(0), NatLit(1), NatLit(2)),
        If(Var(1), NatLit(3), NatLit(4)),
      ),
    ),
    (
      3,
      If(
        Var(2),
        If(Var(1), NatLit(1), If(Var(0), NatLit(2), NatLit(3))),
        NatLit(4),
      ),
    ),
  ]
  for (n, t) in programs {
    let sym = Symbolic::new(n)
    let from_nbe = feasible_leaves(sym, sym.run_nbe(t))
    let from_exec = sym.run(t)
    assert_eq(from_nbe.length(), from_exec.length())
    for i in 0..<from_nbe.length() {
      assert_eq(from_nbe[i].value, from_exec[i].value)
      assert_true(
        sym.guard_equiv(from_nbe[i].path_cond, from_exec[i].path_cond),
      )
    }
  }
}

///|
test "symbolic guards are canonical: equivalent programs share path conditions" {
  // `if x then y else false` and `x /\ y` have the same path_cond structure
  let a = Term::If(Var(1), Var(0), BoolLit(false))
  let sym = Symbolic::new(2)
  let ls = sym.run(a)
  assert_eq(ls.length(), 2)
  // the then-branch returns the symbolic y, not a literal
  assert_eq(ls[0].value, VNe(NVar(1)))
  assert_true(guard_dm_eq(ls[0].path_cond, @cubical.DVar(0)))
  // and the NbE normal form of the same term is the residual decision tree
  let nf = normalize(bool_ctx(2), a)
  assert_eq(nf.key(), a.key())
  // while `if x then true else y` normalises to a different tree with the
  // same Boolean meaning -- canonical up to the algebra, not up to Boolean
  let b = Term::If(Var(1), BoolLit(true), Var(0))
  let sym2 = Symbolic::new(2)
  let lb = sym2.run(b)
  assert_eq(lb.length(), 2)
  assert_eq(lb[0].value, VBool(true))
  assert_true(sym2.guard_equiv(lb[0].path_cond, @cubical.DVar(0)))
}
