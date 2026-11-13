///|
test "free De Morgan algebra on 1 generator has 6 elements, on 2 has 168" {
  let one = free_dm_algebra(1)
  assert_eq(one.length(), 6)
  // the four "Boolean" ones plus x/\~x and x\/~x
  assert_true(one.contains(DMA::zero()))
  assert_true(one.contains(DMA::one()))
  assert_true(one.contains(DMA::meet(DMA::gen(0), DMA::neg_gen(0))))
  assert_true(one.contains(DMA::join(DMA::gen(0), DMA::neg_gen(0))))
  // free De Morgan algebra on 2 generators: 168 elements
  assert_eq(free_dm_algebra(2).length(), 168)
}

///|
test "De Morgan laws hold, Boolean complementation does not" {
  let x = DMA::gen(0)
  let y = DMA::gen(1)
  let nx = DMA::neg_gen(0)
  let ny = DMA::neg_gen(1)
  // involution
  assert_eq(x.negate(), nx)
  assert_eq(nx.negate(), x)
  // De Morgan duality
  assert_eq(DMA::meet(x, y).negate(), DMA::join(nx, ny))
  assert_eq(DMA::join(x, y).negate(), DMA::meet(nx, ny))
  // distributivity + absorption
  assert_eq(
    DMA::meet(x, DMA::join(y, DMA::gen(2))),
    DMA::join(DMA::meet(x, y), DMA::meet(x, DMA::gen(2))),
  )
  assert_eq(DMA::join(x, DMA::meet(x, y)), x)
  // NOT Boolean: x /\ ~x != 0 and x \/ ~x != 1
  assert_false(DMA::meet(x, nx).is_zero())
  assert_false(DMA::join(x, nx).is_one())
  // The free De Morgan algebra is NOT normal (not a Kleene algebra):
  // the Kleene inequality x /\ ~x <= y \/ ~y fails, exactly as it does in
  // the four-element De Morgan algebra D4 with two fixed points of ~.
  // This is why the cubical interval is De Morgan and not Kleene.
  assert_false(DMA::leq(DMA::meet(x, nx), DMA::join(y, ny)))
  // and the "middle" elements are ordered
  assert_true(DMA::leq(DMA::meet(x, nx), x))
  assert_true(DMA::leq(x, DMA::join(x, nx)))
}

///|
test "antichain normal form decides equality, and agrees with the cubical DNF" {
  let terms : Array[Dim] = [
    @cubical.DZero,
    @cubical.DOne,
    @cubical.DVar(0),
    @cubical.DVar(1),
    @cubical.DNot(@cubical.DVar(0)),
    @cubical.DAnd(@cubical.DVar(0), @cubical.DVar(1)),
    @cubical.DOr(@cubical.DVar(0), @cubical.DVar(1)),
    @cubical.DAnd(@cubical.DVar(0), @cubical.DNot(@cubical.DVar(0))),
    @cubical.DOr(@cubical.DVar(0), @cubical.DNot(@cubical.DVar(0))),
    @cubical.DNot(@cubical.DAnd(@cubical.DVar(0), @cubical.DVar(1))),
    @cubical.DAnd(
      @cubical.DOr(@cubical.DVar(0), @cubical.DVar(1)),
      @cubical.DNot(@cubical.DVar(1)),
    ),
    @cubical.DOr(
      @cubical.DAnd(@cubical.DVar(0), @cubical.DVar(1)),
      @cubical.DAnd(@cubical.DVar(0), @cubical.DNot(@cubical.DVar(1))),
    ),
  ]
  for a in terms {
    for b in terms {
      // the two independent decision procedures must agree
      assert_eq(dim_eq(a, b), DMA::of_dim(a) == DMA::of_dim(b))
    }
  }
  // absorption in the antichain: x \/ (x /\ y) collapses to x
  assert_eq(
    DMA::of_dim(
      @cubical.DOr(
        @cubical.DVar(0),
        @cubical.DAnd(@cubical.DVar(0), @cubical.DVar(1)),
      ),
    ).render(),
    "x0",
  )
  // distribution normal form of ~(x0 /\ x1)
  assert_eq(
    DMA::of_dim(
      @cubical.DNot(@cubical.DAnd(@cubical.DVar(0), @cubical.DVar(1))),
    ).render(),
    "~x0 \\/ ~x1",
  )
}

///|
test "three-valued evaluation matches the interval semantics on all subcubes" {
  let terms : Array[Dim] = [
    @cubical.DAnd(@cubical.DVar(0), @cubical.DVar(1)),
    @cubical.DOr(@cubical.DVar(0), @cubical.DVar(1)),
    @cubical.DNot(@cubical.DAnd(@cubical.DVar(0), @cubical.DVar(1))),
    @cubical.DAnd(@cubical.DVar(0), @cubical.DNot(@cubical.DVar(0))),
    @cubical.DOr(@cubical.DVar(0), @cubical.DNot(@cubical.DVar(0))),
    @cubical.DAnd(
      @cubical.DOr(@cubical.DVar(0), @cubical.DVar(1)),
      @cubical.DNot(@cubical.DVar(1)),
    ),
  ]
  for code in 0..<pow3(2) {
    let pt = subcube_digits(code, 2)
    for t in terms {
      assert_eq(t.eval3(pt), DMA::of_dim(t).eval3(pt))
    }
  }
}

///|
test "cubical identities: face/degeneracy, and σδ = id" {
  for n in 1..<4 {
    for i in 0..<n {
      for eps in 0..<2 {
        // insert then forget is the identity
        assert_true(
          cube_map_eq(
            cube_then(cube_face(n, i, eps), cube_degen(n, i)),
            cube_id(n),
          ),
        )
      }
    }
  }
  // faces commute with the index shift: δ_i^e then δ_{j+1}^f = δ_j^f then δ_i^e (i <= j)
  for n in 0..<3 {
    for i in 0..<=n {
      for j in i..<=n {
        for e in 0..<2 {
          for f in 0..<2 {
            let lhs = cube_then(cube_face(n, i, e), cube_face(n + 1, j + 1, f))
            let rhs = cube_then(cube_face(n, j, f), cube_face(n + 1, i, e))
            assert_true(cube_map_eq(lhs, rhs))
          }
        }
      }
    }
  }
}

///|
test "connections: associativity, unit faces, and De Morgan duality" {
  for n in 1..<4 {
    for i in 0..<n {
      for eps in 0..<2 {
        // associativity of merging three coordinates
        let lhs = cube_then(cube_conn(n + 1, i, eps), cube_conn(n, i, eps))
        let rhs = cube_then(cube_conn(n + 1, i + 1, eps), cube_conn(n, i, eps))
        assert_true(cube_map_eq(lhs, rhs))
        // duplicating then merging is the identity (connections split the diagonal)
        assert_true(
          cube_map_eq(
            cube_then(cube_dup(n, i), cube_conn(n, i, eps)),
            cube_id(n),
          ),
        )
        // the matching face is absorbed: γ^0 with x_i = 0 pins to 0
        let absorb = cube_then(cube_face(n, i, eps), cube_conn(n, i, eps))
        assert_true(cube_map_eq(absorb, cube_pin(n, i, eps)))
        // the opposite face is a unit: γ^0 with x_i = 1 is the identity
        let unit = cube_then(cube_face(n, i, 1 - eps), cube_conn(n, i, eps))
        assert_true(cube_map_eq(unit, cube_id(n)))
      }
    }
  }
  // De Morgan duality of the two connections: r γ^0 (r x r) = γ^1 r
  for n in 1..<3 {
    for i in 0..<n {
      let revs = cube_then(cube_rev(n + 1, i), cube_rev(n + 1, i + 1))
      let lhs = cube_then(revs, cube_conn(n, i, 0))
      let rhs = cube_then(cube_conn(n, i, 1), cube_rev(n, i))
      assert_true(cube_map_eq(lhs, rhs))
    }
  }
}

///|
test "syntactic and pointwise equality of cube maps agree (completeness)" {
  // endomorphisms of I^2
  let endos : Array[CubeMap] = [
    cube_id(2),
    cube_rev(2, 0),
    cube_swap(2, 0),
    cube_pin(2, 1, 0),
    cube_then(cube_rev(2, 0), cube_swap(2, 0)),
    cube_then(cube_swap(2, 0), cube_rev(2, 0)),
    cube_then(cube_rev(2, 0), cube_rev(2, 1)),
  ]
  // maps I^2 -> I^1 (connections and their reversals)
  let projections : Array[CubeMap] = [
    cube_conn(1, 0, 0),
    cube_conn(1, 0, 1),
    cube_then(cube_conn(1, 0, 0), cube_rev(1, 0)),
    cube_then(cube_rev(2, 0), cube_conn(1, 0, 1)),
  ]
  for group in [endos, projections] {
    for m in group {
      assert_true(m.well_formed())
    }
    for a in group {
      for b in group {
        assert_eq(cube_map_eq(a, b), cube_map_pointwise_eq(a, b))
      }
    }
  }
  // reversal is an involution, swap is an involution
  assert_true(
    cube_map_eq(cube_then(cube_rev(2, 0), cube_rev(2, 0)), cube_id(2)),
  )
  assert_true(
    cube_map_eq(cube_then(cube_swap(2, 0), cube_swap(2, 0)), cube_id(2)),
  )
}

///|
test "cube maps act on subcubes: the connection merges two directions" {
  // γ^0 : I^2 -> I^1 sends (1,1) to 1, (0,1) to 0, (free,1) to free
  let g = cube_conn(1, 0, 0)
  assert_eq(g.apply([1, 1]), [1])
  assert_eq(g.apply([0, 1]), [0])
  assert_eq(g.apply([2, 1]), [2])
  assert_eq(g.apply([2, 0]), [0])
  // and the join connection is dual
  let h = cube_conn(1, 0, 1)
  assert_eq(h.apply([0, 0]), [0])
  assert_eq(h.apply([1, 0]), [1])
  assert_eq(h.apply([2, 1]), [1])
}
