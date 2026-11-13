///|
test "Artin tower: R_2 dual numbers, units, truncation, square-zero kernel" {
  let p = 5
  let r3 = Artin::new(p, 3)
  let t = r3.uniformiser()
  assert_eq(t, [0, 1, 0])
  // t^2 != 0 but t^3 = 0 in R_3
  assert_eq(r3.mul(t, t), [0, 0, 1])
  assert_eq(r3.mul(r3.mul(t, t), t), [0, 0, 0])
  // units are exactly the series with nonzero constant term
  assert_true(r3.is_unit([2, 1, 3]))
  assert_false(r3.is_unit([0, 1, 0]))
  match r3.inv([2, 1, 3]) {
    None => fail("should be a unit")
    Some(b) => assert_eq(r3.mul([2, 1, 3], b), r3.one())
  }
  assert_true(r3.inv(t) is None)
  // valuation
  assert_eq(r3.valuation([0, 0, 4]), 2)
  assert_eq(r3.valuation(r3.zero()), 3)
  // tower map R_3 -> R_2 forgets the top coefficient
  assert_eq(r3.truncate([1, 2, 3], 2), [1, 2])
  assert_eq(r3.lift_zero([1, 2], 3), [1, 2, 0])
  // the small extension is square-zero and killed by the maximal ideal
  let ext = small_extension(p, 2)
  assert_true(ext.check())
  assert_eq(ext.kernel_dim, 1)
}

///|
test "Hochschild differential squares to zero iff the algebra is associative" {
  let p = 5
  for
    alg in [
      alg_field(p),
      alg_dual_numbers(p),
      alg_product(p),
      alg_truncated(p, 3),
    ] {
    assert_true(alg.is_associative())
    assert_true(alg.check_d2(0))
    assert_true(alg.check_d2(1))
  }
  // a deliberately non-associative algebra breaks delta^2 = 0
  let bad = Alg::new(2, p, [[[1, 0], [0, 0]], [[0, 1], [1, 0]]])
  assert_false(bad.is_associative())
  assert_false(bad.check_d2(0))
}

///|
test "HH^0 is the centre; separable algebras are rigid, dual numbers are not" {
  let p = 5
  // commutative algebras: HH^0 = the whole algebra
  let dual = alg_dual_numbers(p)
  assert_true(dual.is_commutative())
  assert_eq(dual.hh_dim(0), 2)
  // F_p x F_p is separable => HH^1 = HH^2 = 0 (rigid, no deformations)
  let prod = alg_product(p)
  assert_eq(prod.hh_dim(0), 2)
  assert_eq(prod.hh_dim(1), 0)
  assert_eq(prod.hh_dim(2), 0)
  // F_p[x]/(x^2) is not separable: it has a genuine HH^2
  assert_true(dual.hh_dim(1) > 0)
  assert_true(dual.hh_dim(2) > 0)
  // F_p itself is rigid
  let f = alg_field(p)
  assert_eq(f.hh_dim(0), 1)
  assert_eq(f.hh_dim(1), 0)
  assert_eq(f.hh_dim(2), 0)
}

///|
test "first-order deformations are cocycles, and the Gerstenhaber obstruction is a 3-cocycle" {
  let p = 5
  let alg = alg_dual_numbers(p)
  let space = alg.first_order_space()
  assert_true(space.length() > 0)
  let d3 = alg.hochschild_diff(3)
  for mu1 in space {
    // ob(mu1) must be killed by delta^3 : it is a 3-cocycle
    let ob = alg.gerstenhaber_obstruction(mu1)
    let out = fp_matmul_vec(d3, ob, p)
    for x in out {
      assert_eq(x, 0)
    }
    // and extendability to order 2 is decided by a linear system
    let _ = alg.extends_to_order2(mu1)
  }
  // the zero deformation always extends
  let zero : Array[Array[Array[Int32]]] = [
    [alg_zero(2), alg_zero(2)],
    [alg_zero(2), alg_zero(2)],
  ]
  assert_true(alg.extends_to_order2(zero))
}

///|
fn alg_zero(d : Int32) -> Array[Int32] {
  Array::make(d, 0)
}

///|
fn fp_matmul_vec(
  m : Array[Array[Int32]],
  x : Array[Int32],
  p : Int32,
) -> Array[Int32] {
  let out : Array[Int32] = []
  for row in m {
    let mut s = 0
    for j in 0..<x.length() {
      s = fp_add(s, fp_mul(row[j], x[j], p), p)
    }
    out.push(s)
  }
  out
}

///|
test "module deformation functor: Ext^0, Ext^1, and the tower of modules" {
  let p = 5
  let alg = alg_dual_numbers(p)
  let reg = regular_module(alg)
  assert_true(reg.check())
  assert_true(reg.check_d2())
  // End_A(A) = A^op has dimension 2 for the regular module
  assert_eq(reg.ext0(), 2)
  // the regular module over a self-injective algebra: Ext^1 is computed,
  // and every cocycle really gives a deformation over the dual numbers
  let basis = reg.cocycle_basis()
  assert_true(basis.length() > 0)
  let mut deformations = 0
  for f in basis {
    match reg.deform_by(f) {
      Some(def) => {
        assert_true(def.check())
        deformations = deformations + 1
      }
      None => ()
    }
  }
  assert_eq(deformations, basis.length())
  // the trivial tower is compatible at every stage
  let tower = trivial_tower(reg, p, 4)
  assert_eq(tower.height(), 4)
  assert_true(tower.check())
  // truncating a constant deformation gives the constant deformation
  let d3 = reg.constant_deform(Artin::new(p, 3))
  assert_eq(d3.truncate(2), reg.constant_deform(Artin::new(p, 2)))
  assert_true(d3.first_order() is Some(_))
}

///|
test "a non-cocycle direction is rejected by the deformation functor" {
  let p = 5
  let alg = alg_dual_numbers(p)
  let reg = regular_module(alg)
  // f(e_0) = identity is not a cocycle: it breaks rho(1) = id compatibility
  let bad : Array[Array[Array[Int32]]] = [[[1, 0], [0, 0]], [[0, 0], [0, 0]]]
  assert_true(reg.deform_by(bad) is None)
}

///|
test "incompatible tower stages are detected" {
  let p = 5
  let reg = regular_module(alg_dual_numbers(p))
  let s1 = reg.constant_deform(Artin::new(p, 1))
  let s2 = reg.constant_deform(Artin::new(p, 2))
  assert_true(ModTower::new([s1, s2]).check())
  // wrong order of stages breaks the ring-size invariant
  assert_false(ModTower::new([s2, s1]).check())
}
