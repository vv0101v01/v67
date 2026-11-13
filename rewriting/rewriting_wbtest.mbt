///|
test "unification: mgu, occurs check, clash" {
  // f(x, g(y)) ~ f(g(z), g(a))  =>  x = g(a), y = a, z = a
  let a = constant("a")
  let s = app("f", [v(0), app("g", [v(1)])])
  let t = app("f", [app("g", [v(2)]), app("g", [a])])
  match unify(s, t) {
    None => fail("should unify")
    Some(sigma) => {
      assert_eq(s.subst(sigma), t.subst(sigma))
      assert_eq(sigma.get(0), Some(app("g", [v(2)])))
      assert_eq(sigma.get(1), Some(a))
    }
  }
  // occurs check: x ~ f(x) has no unifier
  assert_true(unify(v(0), app("f", [v(0)])) is None)
  // symbol clash
  assert_true(unify(constant("a"), constant("b")) is None)
  // arity clash
  assert_true(unify(app("f", [a]), app("f", [a, a])) is None)
}

///|
test "matching is one-way, rewriting is leftmost-outermost" {
  let a = constant("a")
  // a pattern with a symbol cannot match a bare variable subject
  assert_true(match_term(app("f", [v(0)]), v(7)) is None)
  assert_true(match_term(v(0), a) is Some(_))
  // pattern f(x,x) does not match f(a,b)
  assert_true(
    match_term(app("f", [v(0), v(0)]), app("f", [a, constant("b")])) is None,
  )
  let rs = [rule(app("f", [v(0)]), v(0))]
  assert_eq(normalize(app("f", [app("f", [a])]), rs), Normal(a))
}

///|
test "critical pair lemma: associativity is locally confluent, and terminating as a rewrite rule" {
  // (x*y)*z -> x*(y*z)
  let assoc = rule(
    app("*", [app("*", [v(0), v(1)]), v(2)]),
    app("*", [v(0), app("*", [v(1), v(2)])]),
  )
  let rs = [assoc]
  let rep = check_local_confluence(rs)
  assert_true(rep.locally_confluent())
  // the single critical pair comes from overlapping assoc with itself
  assert_eq(rep.pairs, 1)
  let prec : Map[String, Int32] = { "*": 1 }
  // associativity alone is LPO-terminating (right-norming decreases)
  assert_true(lpo_terminating(rs, prec))
  let t = app("*", [
    app("*", [app("*", [constant("a"), constant("b")]), constant("c")]),
    constant("d"),
  ])
  inspect(normalize(t, rs).term().render(), content="(a * (b * (c * d)))")
}

///|
test "group theory: Knuth-Bendix completes the free group word problem" {
  // (x*y)*z = x*(y*z), e*x = x, i(x)*x = e
  let e = constant("e")
  let mul = fn(x : Term, y : Term) -> Term { app("*", [x, y]) }
  let inv = fn(x : Term) -> Term { app("i", [x]) }
  let eqs = [
    (mul(mul(v(0), v(1)), v(2)), mul(v(0), mul(v(1), v(2)))),
    (mul(e, v(0)), v(0)),
    (mul(inv(v(0)), v(0)), e),
  ]
  let prec : Map[String, Int32] = { "*": 1, "i": 2, "e": 0 }
  let res = complete(eqs, prec, max_steps=400)
  assert_true(res.succeeded)
  let rs = res.rules
  assert_true(lpo_terminating(rs, prec))
  assert_true(check_local_confluence(rs).locally_confluent())
  let a = constant("a")
  let b = constant("b")
  // i(i(a)) = a
  assert_true(joinable(inv(inv(a)), a, rs))
  // a * i(a) = e  (right inverse is a consequence, not an axiom)
  assert_true(joinable(mul(a, inv(a)), e, rs))
  // i(a*b) = i(b)*i(a)
  assert_true(joinable(inv(mul(a, b)), mul(inv(b), inv(a)), rs))
  // a * e = a
  assert_true(joinable(mul(a, e), a, rs))
  // and the free group is not collapsed: a*b != b*a
  assert_false(joinable(mul(a, b), mul(b, a), rs))
  // normal form of a * i(a) * b is b
  assert_eq(normalize(mul(mul(a, inv(a)), b), rs), Normal(b))
}

///|
test "non-confluent system is detected, and completion repairs it" {
  // a -> b, a -> c : the peak b <- a -> c is not joinable
  let a = constant("a")
  let b = constant("b")
  let c = constant("c")
  let rs = [rule(a, b), rule(a, c)]
  let rep = check_local_confluence(rs)
  assert_false(rep.locally_confluent())
  assert_eq(rep.unjoinable.length(), 2)
  // orienting b > c completes it
  let prec : Map[String, Int32] = { "a": 2, "b": 1, "c": 0 }
  let res = complete([(a, b), (a, c)], prec)
  assert_true(res.succeeded)
  assert_true(joinable(b, c, res.rules))
}

///|
test "termination: size order certifies De Morgan-style push-negation rules" {
  // ~(x /\ y) -> ~x \/ ~y   grows, so size order fails;
  // ~~x -> x  and  ~0 -> 1  shrink, so it succeeds.
  let nn = rule(app("~", [app("~", [v(0)])]), v(0))
  let n0 = rule(app("~", [constant("0")]), constant("1"))
  assert_true(size_terminating([nn, n0]))
  let dm = rule(
    app("~", [app("/\\", [v(0), v(1)])]),
    app("\\/", [app("~", [v(0)]), app("~", [v(1)])]),
  )
  assert_false(size_terminating([dm]))
  let prec : Map[String, Int32] = { "~": 3, "/\\": 2, "\\/": 1, "0": 0, "1": 0 }
  assert_true(lpo_terminating([nn, n0, dm], prec))
}

///|
test "fuel makes non-termination observable instead of fatal" {
  // a -> f(a) loops forever
  let a = constant("a")
  let rs = [rule(a, app("f", [a]))]
  match normalize(a, rs, fuel=20) {
    Diverged(t) => assert_eq(t.size(), 21)
    Normal(_) => fail("should diverge")
  }
}
