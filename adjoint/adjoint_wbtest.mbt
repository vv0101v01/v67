///|
test "mode theories: preorder axioms and monotone structural rules" {
  assert_true(modes_lnl().check())
  assert_true(modes_three().check())
  assert_true(modes_diamond().check())
  assert_true(modes_linear().check())
  let lnl = modes_lnl()
  assert_true(lnl.ge(mode_u, mode_l))
  assert_false(lnl.ge(mode_l, mode_u))
  assert_true(lnl.allows_weaken(mode_u))
  assert_false(lnl.allows_weaken(mode_l))
  // a non-transitive relation is rejected
  let bad = Modes::new(
    ["a", "b", "c"],
    [[true, true, false], [false, true, true], [false, false, true]],
    [false, false, false],
    [false, false, false],
  )
  assert_false(bad.check())
  // structural rules must be monotone along the preorder: putting W only
  // at the LOWER mode breaks cut elimination, and check says so
  let bad2 = Modes::new(
    ["U", "L"],
    [[true, true], [false, true]],
    [false, true],
    [false, false],
  )
  assert_false(bad2.check())
}

///|
test "independence: an ill-formed sequent is rejected, not merely unprovable" {
  let p = Prover::new(modes_lnl())
  let a = Formula::Atom(0)
  // A_L ⊢_L A is fine
  assert_true(p.provable([Antecedent::new(mode_l, a)], mode_l, a))
  // A_L ⊢_U ↑^U_L A violates the declaration of independence (L ≱ U)
  assert_false(
    p.provable([Antecedent::new(mode_l, a)], mode_u, Up(mode_u, mode_l, a)),
  )
  // and a linear hypothesis cannot be promoted to !A
  assert_false(
    p.provable([Antecedent::new(mode_l, a)], mode_l, bang(mode_u, mode_l, a)),
  )
  // A hypothesis at mode U is a DIFFERENT proposition from the same
  // connective structure at mode L: identity requires the modes to match.
  // So even an unrestricted `a_U` does not prove `!a_L`.
  assert_false(
    p.provable([Antecedent::new(mode_u, a)], mode_l, bang(mode_u, mode_l, a)),
  )
  // What does prove it is the *promoted* proposition ↑^U_L a, assumed at U:
  // this is exactly the promotion rule of linear logic, !Γ ⊢ A ⟹ !Γ ⊢ !A.
  assert_true(
    p.provable(
      [Antecedent::new(mode_u, Up(mode_u, mode_l, a))],
      mode_l,
      bang(mode_u, mode_l, a),
    ),
  )
}

///|
test "shifts respect the preorder in the syntax" {
  let lnl = modes_lnl()
  // ↑^U_L is well formed, ↑^L_U is not
  assert_true(Formula::Up(mode_u, mode_l, Atom(0)).well_formed(lnl))
  assert_false(Formula::Up(mode_l, mode_u, Atom(0)).well_formed(lnl))
  // ↓^U_L is well formed (it lives at L), ↓^L_U is not
  assert_true(Formula::Down(mode_u, mode_l, Atom(0)).well_formed(lnl))
  assert_false(Formula::Down(mode_l, mode_u, Atom(0)).well_formed(lnl))
  // fixed modes are read off the shift
  assert_eq(Formula::Up(mode_u, mode_l, Atom(0)).fixed_mode(), Some(mode_u))
  assert_eq(Formula::Down(mode_u, mode_l, Atom(0)).fixed_mode(), Some(mode_l))
  assert_eq(Formula::Tensor(Atom(0), Atom(1)).fixed_mode(), None)
}

///|
test "the shift adjunction: unit, counit and the hom-set bijection" {
  let p = Prover::new(modes_lnl())
  let atoms = [Formula::Atom(0), Atom(1), Tensor(Atom(0), Atom(1)), One]
  for a in atoms {
    // unit at U and counit at L are derivable
    assert_true(p.shift_unit(mode_u, mode_l, a) is Some(_))
    assert_true(p.shift_counit(mode_u, mode_l, a) is Some(_))
    assert_true(p.triangle_ids(mode_u, mode_l, a))
    // and the adjunction holds for every pair of propositions
    for b in atoms {
      assert_true(p.adjunction_holds(mode_u, mode_l, a, b))
    }
  }
  // a case where BOTH sides are unprovable: the bijection is not vacuous
  let a = Formula::Atom(0)
  let b = Formula::Atom(1)
  assert_false(
    p.provable([Antecedent::new(mode_l, Down(mode_u, mode_l, a))], mode_l, b),
  )
  assert_false(
    p.provable([Antecedent::new(mode_u, a)], mode_u, Up(mode_u, mode_l, b)),
  )
  assert_true(p.adjunction_holds(mode_u, mode_l, a, b))
}

///|
test "the exponential !A = down-up A satisfies the comonad laws" {
  let p = Prover::new(modes_lnl())
  for a in [Formula::Atom(0), Atom(1), Tensor(Atom(0), Atom(1))] {
    let (dereliction, dig, contr, weak) = p.exponential_laws(mode_u, mode_l, a)
    assert_true(dereliction)
    assert_true(dig)
    assert_true(contr)
    assert_true(weak)
  }
  // the three-mode chain gives a second exponential !^A, and it also works
  let p3 = Prover::new(modes_three())
  let (d2, g2, c2, w2) = p3.exponential_laws(mode_a, 2, Atom(0))
  assert_true(d2)
  assert_true(g2)
  assert_true(c2)
  assert_true(w2)
}

///|
test "linear logic laws hold at the linear mode" {
  let p = Prover::new(modes_lnl())
  let a = Formula::Atom(0)
  let b = Formula::Atom(1)
  let c = Formula::Atom(2)
  let ctx = fn(xs : Array[Formula]) -> Array[Antecedent] {
    let out : Array[Antecedent] = []
    for x in xs {
      out.push(Antecedent::new(mode_l, x))
    }
    out
  }
  // tensor is symmetric and associative, and 1 is its unit
  assert_true(p.provable(ctx([Tensor(a, b)]), mode_l, Tensor(b, a)))
  assert_true(
    p.provable(ctx([Tensor(Tensor(a, b), c)]), mode_l, Tensor(a, Tensor(b, c))),
  )
  assert_true(p.provable(ctx([Tensor(a, One)]), mode_l, a))
  // currying
  assert_true(
    p.provable(ctx([Tensor(a, b)]), mode_l, c) ==
    p.provable(ctx([a]), mode_l, Lolli(b, c)),
  )
  assert_true(
    p.provable(ctx([Lolli(Tensor(a, b), c)]), mode_l, Lolli(a, Lolli(b, c))),
  )
  // with is a product, plus a coproduct
  assert_true(p.provable(ctx([With(a, b)]), mode_l, a))
  assert_true(p.provable(ctx([With(a, b)]), mode_l, b))
  assert_true(p.provable(ctx([a]), mode_l, Plus(a, b)))
  // Case analysis on a sum needs the two continuations combined with &
  // (external choice), not with two separate linear hypotheses: in the
  // a-branch the hypothesis b ⊸ c would be left over and cannot be
  // discarded at a linear mode.
  assert_true(
    p.provable(ctx([Plus(a, b), With(Lolli(a, c), Lolli(b, c))]), mode_l, c),
  )
  assert_false(
    p.provable(ctx([Plus(a, b), Lolli(a, c), Lolli(b, c)]), mode_l, c),
  )
  // at the unrestricted mode weakening is available, so it goes through
  let pu = Prover::new(modes_lnl())
  assert_true(
    pu.provable(
      [
        Antecedent::new(mode_u, Plus(a, b)),
        Antecedent::new(mode_u, Lolli(a, c)),
        Antecedent::new(mode_u, Lolli(b, c)),
      ],
      mode_u,
      c,
    ),
  )
  // distributivity of tensor over plus
  assert_true(
    p.provable(
      ctx([Tensor(a, Plus(b, c))]),
      mode_l,
      Plus(Tensor(a, b), Tensor(a, c)),
    ),
  )
  // linearity: a cannot be duplicated or discarded
  assert_false(p.provable(ctx([a]), mode_l, Tensor(a, a)))
  assert_false(p.provable(ctx([a]), mode_l, One))
  // but 0 proves anything and top is always provable
  assert_true(p.provable(ctx([Zero]), mode_l, Tensor(a, a)))
  assert_true(p.provable(ctx([a]), mode_l, Top))
}

///|
test "weakening and contraction are governed by the mode, not the formula" {
  let p = Prover::new(modes_lnl())
  let a = Formula::Atom(0)
  // at U both structural rules are available
  assert_true(p.provable([Antecedent::new(mode_u, a)], mode_u, One))
  assert_true(
    p.provable(
      [Antecedent::new(mode_u, a)],
      mode_u,
      Tensor(a, a),
      contract_fuel=1,
    ),
  )
  // with no contraction budget the same sequent is unprovable
  assert_false(p.provable([Antecedent::new(mode_u, a)], mode_u, Tensor(a, a)))
  // at the affine mode A weakening holds but contraction never does
  let p3 = Prover::new(modes_three())
  assert_true(p3.provable([Antecedent::new(mode_a, a)], mode_a, One))
  assert_false(
    p3.provable(
      [Antecedent::new(mode_a, a)],
      mode_a,
      Tensor(a, a),
      contract_fuel=3,
    ),
  )
  // at L neither holds
  assert_false(p3.provable([Antecedent::new(2, a)], 2, One))
}

///|
test "cut is admissible: every cut instance has a cut-free proof" {
  let p = Prover::new(modes_lnl())
  let a = Formula::Atom(0)
  let b = Formula::Atom(1)
  let c = Formula::Atom(2)
  let lin = fn(f : Formula) -> Antecedent { Antecedent::new(mode_l, f) }
  let cases : Array[
    (Array[Antecedent], Int32, Formula, Array[Antecedent], Int32, Formula),
  ] = [
    // cut on an atom
    ([lin(a)], mode_l, a, [lin(Lolli(a, b))], mode_l, b),
    // cut on a tensor
    (
      [lin(a), lin(b)],
      mode_l,
      Tensor(a, b),
      [lin(Lolli(Tensor(a, b), c))],
      mode_l,
      c,
    ),
    // cut on a shift: !a used to feed a linear implication
    ([lin(bang(mode_u, mode_l, a))], mode_l, a, [lin(Lolli(a, c))], mode_l, c),
    // cut at mode U against a mode L conclusion (U ≥ L), cutting on the
    // promoted proposition so that the modes line up
    (
      [Antecedent::new(mode_u, Up(mode_u, mode_l, a))],
      mode_u,
      Up(mode_u, mode_l, a),
      [lin(Lolli(a, b))],
      mode_l,
      b,
    ),
    // cut on a sum
    (
      [lin(a)],
      mode_l,
      Plus(a, b),
      [lin(With(Lolli(a, c), Lolli(b, c)))],
      mode_l,
      c,
    ),
  ]
  let (tested, failed) = p.check_cut(cases)
  assert_eq(tested, 5)
  assert_eq(failed, 0)
}

///|
test "conservativity: the linear fragment is exactly linear logic" {
  let a = Formula::Atom(0)
  let b = Formula::Atom(1)
  let c = Formula::Atom(2)
  let cases : Array[(Array[Formula], Formula)] = [
    ([a], a),
    ([a], Tensor(a, a)),
    ([a], One),
    ([Tensor(a, b)], Tensor(b, a)),
    ([a, Lolli(a, b)], b),
    ([Lolli(a, Lolli(b, c)), Tensor(a, b)], c),
    ([With(a, b)], a),
    ([Plus(a, b), Lolli(a, c), Lolli(b, c)], c),
    ([Plus(a, b), With(Lolli(a, c), Lolli(b, c))], c),
    ([Tensor(a, Plus(b, c))], Plus(Tensor(a, b), Tensor(a, c))),
    ([Zero], Tensor(a, b)),
    ([a], Top),
    ([One], a),
    ([Tensor(Tensor(a, b), c)], Tensor(a, Tensor(b, c))),
    ([Lolli(Tensor(a, b), c)], Lolli(a, Lolli(b, c))),
  ]
  // adding an unrestricted mode above L does not change linear provability
  let (tested, mismatch) = conservative_at(
    modes_lnl(),
    modes_linear(),
    mode_l,
    0,
    cases,
  )
  assert_eq(tested, 15)
  assert_eq(mismatch, 0)
  // nor does adding a whole chain of modes
  let (t2, m2) = conservative_at(modes_three(), modes_linear(), 2, 0, cases)
  assert_eq(t2, 15)
  assert_eq(m2, 0)
}

///|
test "proof search terminates and produces checkable derivations" {
  let p = Prover::new(modes_lnl())
  let a = Formula::Atom(0)
  let b = Formula::Atom(1)
  match p.prove([Antecedent::new(mode_l, Tensor(a, b))], mode_l, Tensor(b, a)) {
    None => fail("commutativity of tensor")
    Some(pr) => {
      // a cut-free derivation: tensor-L then tensor-R then two identities
      assert_true(pr.size() >= 3)
      assert_true(pr.has_shift() == false)
      match pr {
        TensorL(_) => ()
        _ => fail("expected a tensor left rule at the root")
      }
    }
  }
  // a derivation that genuinely uses a shift
  match p.shift_counit(mode_u, mode_l, a) {
    None => fail("dereliction")
    Some(pr) => assert_true(pr.has_shift())
  }
  // the search is memoised and does real work, but stays small
  assert_true(p.steps() > 0)
  assert_true(p.steps() < 100000)
}
