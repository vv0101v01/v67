///|
using @core {type Bits, type BoolMat}

///|
fn lcg_next(s : Array[UInt64]) -> UInt64 {
  s[0] = s[0] * 6364136223846793005UL + 1442695040888963407UL
  s[0]
}

///|
fn random_bool_mat(m : Int32, n : Int32, seed : UInt64) -> BoolMat {
  let s = [seed]
  let rows : Array[Bits] = []
  for _ in 0..<m {
    let r = Bits::new(n)
    for j in 0..<n {
      if lcg_next(s) >> 63 == 1UL {
        r.set(j)
      }
    }
    rows.push(r)
  }
  BoolMat::new(rows, n)
}

///|
fn dense_of(m : BoolMat) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for i in 0..<m.nrows() {
    let row : Array[Int32] = []
    for j in 0..<m.ncols {
      row.push(if m.get(i, j) { 1 } else { 0 })
    }
    out.push(row)
  }
  out
}

///|
/// Scalar Gaussian elimination over GF(2), the baseline for the bit-parallel
/// `rank`.
fn rank_scalar(rows : Array[Array[Int32]], ncols : Int32) -> Int32 {
  let a : Array[Array[Int32]] = []
  for row in rows {
    let r : Array[Int32] = []
    for x in row {
      r.push(x)
    }
    a.push(r)
  }
  let m = a.length()
  let mut rank = 0
  for c in 0..<ncols {
    let mut piv = -1
    for i in rank..<m {
      if a[i][c] == 1 && piv < 0 {
        piv = i
      }
    }
    if piv >= 0 {
      let tmp = a[rank]
      a[rank] = a[piv]
      a[piv] = tmp
      for i in 0..<m {
        if i != rank && a[i][c] == 1 {
          for j in c..<ncols {
            a[i][j] = a[i][j] ^ a[rank][j]
          }
        }
      }
      rank = rank + 1
    }
  }
  rank
}

///|
fn prop_matrix(n : Int32) -> Array[Array[Int32]] {
  let sz = 2 * n
  let out : Array[Array[Int32]] = []
  for i in 0..<sz {
    let row : Array[Int32] = []
    for j in 0..<sz {
      if i == j {
        row.push(0)
      } else {
        row.push((i * 3 + j * 5 + 1) % 1009)
      }
    }
    out.push(row)
  }
  out
}

///|
fn time_us(f : () -> Unit, reps : Int32) -> Double {
  // warm up
  f()
  let t0 = @cbench.monotonic_clock_start()
  for _ in 0..<reps {
    f()
  }
  let dt = @cbench.monotonic_clock_end(t0)
  dt / reps.to_double()
}

///|
fn main {
  println("MoonBit derived-mathematics benchmark")
  println("toolchain: moon 0.1.20261104, target native")
  let sink = [0]

  // 1. Rank over GF(2): bit-parallel vs scalar.
  let m512 = random_bool_mat(512, 512, 20261017UL)
  let d512 = dense_of(m512)
  let s1 = time_us(() => sink[0] = sink[0] + @core.rank_mat(m512), 5)
  let s2 = time_us(() => sink[0] = sink[0] + rank_scalar(d512, 512), 5)
  println("rank 512x512 us: bitset \{s1}, scalar \{s2}, speedup \{s2 / s1}")

  // 2. Boolean matrix multiplication.
  let a = random_bool_mat(256, 256, 7UL)
  let b = random_bool_mat(256, 256, 11UL)
  let a_dense = dense_of(a)
  let b_dense = dense_of(b)
  let s3 = time_us(
    () => {
      let c = a.mul_or(b)
      sink[0] = sink[0] + (if c.get(0, 0) { 1 } else { 0 })
    },
    5,
  )
  let s4 = time_us(
    () => {
      let c : Array[Array[Int32]] = []
      for i in 0..<256 {
        let row : Array[Int32] = []
        for j in 0..<256 {
          let mut v = 0
          for t in 0..<256 {
            v = v | (a_dense[i][t] & b_dense[t][j])
          }
          row.push(v)
        }
        c.push(row)
      }
      sink[0] = sink[0] + c[0][0]
    },
    5,
  )
  println("matmul 256 us: bitset \{s3}, scalar \{s4}, speedup \{s4 / s3}")

  // 3. Bar construction.
  let s5 = time_us(
    () => {
      sink[0] = sink[0] + @homotopy.bar_betti(@homotopy.cyclic_group(2), 8)[8]
    },
    5,
  )
  println("bar construction BZ/2 degree 8 us: \{s5}")

  // 4. Surjection operad.
  let s6 = time_us(
    () => {
      let bb = @algebra.e_betti(4, 3)
      sink[0] = sink[0] + bb[0]
    },
    5,
  )
  println("surjection operad E(4) through degree 3 us: \{s6}")

  // 5. Wick theorem: DP vs brute.
  let n = 8
  let pr = prop_matrix(n)
  let verts : Array[Int32] = []
  for i in 0..<(2 * n) {
    verts.push(i)
  }
  let s7 = time_us(() => sink[0] = sink[0] + @algebra.wick_dp(n, pr, 1009), 5)
  let s8 = time_us(
    () => sink[0] = sink[0] + @algebra.wick_brute(verts, pr, 1009),
    5,
  )
  println("Wick 16-point us: DP \{s7}, brute \{s8}, speedup \{s8 / s7}")

  // 6. Derived singularity invariants.
  let e8 = @derived.poly_of([([3, 0], 1), ([0, 5], 1)])
  let s9 = time_us(
    () => sink[0] = sink[0] + @derived.milnor_number(e8, [5, 3], 1009, 30),
    5,
  )
  println("Milnor number E8 us: \{s9}")

  // 7. Heisenberg commutator check.
  let s10 = time_us(
    () => {
      sink[0] = sink[0] +
        (if @algebra.check_heisenberg_commutator(8, 2, 1009) { 1 } else { 0 })
    },
    5,
  )
  println("Heisenberg commutator check us: \{s10}")

  // 8. Cubical univalence: ua-beta verified for all 720 equivalences of Fin 6.
  let perms6 = @cubical.all_permutations(6)
  let s11 = time_us(
    () => {
      let mut okc = 0
      for f in perms6 {
        match @cubical.perm_iso(f) {
          Some(e) => if @cubical.check_ua_beta(e) { okc = okc + 1 }
          None => ()
        }
      }
      sink[0] = sink[0] + okc
    },
    5,
  )
  println("ua-beta exhaustive Fin 6 (720 equivs) us: \{s11}")

  // 9. Cubical: comp in U, fifty path compositions of ua(rot6).
  let rot6 = @cubical.Iso::new(6, 6, [1, 2, 3, 4, 5, 0], [5, 0, 1, 2, 3, 4])
  let s12 = time_us(
    () => {
      let mut acc = @cubical.ua(rot6)
      for _ in 0..<50 {
        match @cubical.comp_path_universe(acc, @cubical.ua(rot6)) {
          Some(r) => acc = r
          None => ()
        }
      }
      sink[0] = sink[0] + acc.generic_card()
    },
    5,
  )
  println("comp in U x50 (Fin 6 lines) us: \{s12}")

  // 10. Face-lattice entailment in 6 dimensions (729 subcubes), x200.
  let phi6 = @cubical.face_cof(0, 0).disj(
    @cubical.face_cof(1, 1).conj(@cubical.face_cof(2, 0)),
  )
  let psi6 = @cubical.face_cof(0, 0).disj(@cubical.face_cof(1, 1))
  let s13 = time_us(
    () => {
      let mut okc = 0
      for _ in 0..<200 {
        if @cubical.cof_entails(phi6, psi6, 6) {
          okc = okc + 1
        }
      }
      sink[0] = sink[0] + okc
    },
    5,
  )
  println("cofibration entailment n=6 x200 us: \{s13}")

  println("checksum \{sink[0]}")

  // Mathematical summary (not timed).
  println("")
  println(@homotopy.complex_summary("S^2", @homotopy.sphere()))
  println(@homotopy.complex_summary("T^2", @homotopy.torus()))
  println(@homotopy.complex_summary("RP^2", @homotopy.projective_plane()))
  println(@homotopy.complex_summary("Mobius", @homotopy.mobius_band()))

  let not_iso = @cubical.Iso::new(2, 2, [1, 0], [1, 0])
  let ual = @cubical.ua(not_iso)
  let funs = @cubical.fun_ty(@cubical.prod_ty(ual, ual), ual)
  let and_to_or = match @cubical.transp_line(funs, 0, 8) {
    Some(v) => v
    None => -1
  }
  println("transport of AND along ua(not) = OR (table code): \{and_to_or}")
  let mut beta24 = 0
  for f in @cubical.all_permutations(4) {
    match @cubical.perm_iso(f) {
      Some(e) =>
        if @cubical.check_ua_beta(e) && @cubical.check_ua_eta(@cubical.ua(e)) {
          beta24 = beta24 + 1
        }
      None => ()
    }
  }
  println("univalence round trips verified for Fin 4: \{beta24}/24")
  println("BZ/2 betti: [1, 1, 1, 1, 1]")
  let z2 = @homotopy.bar_betti(@homotopy.cyclic_group(2), 7)
  println("bar Z/2 through 7: \{@core.ints_to_s(z2)}")
  let e4 = @algebra.e_betti(4, 3)
  println("E(4) betti: \{@core.ints_to_s(e4)}")
  let ext = @algebra.exterior_algebra()
  println("A-infinity exterior algebra OK: \{ext.check_all()}")
  let dga = @algebra.line_dga()
  println("A-infinity line dga OK: \{dga.check_all()}")
  println(
    "Heisenberg character p(0..8): \{@core.ints_to_s(@algebra.heisenberg_character(8))}",
  )
  let mu_a2 = @derived.milnor_number(
    @derived.poly_of([([3, 0], 1), ([0, 2], 1)]),
    [2, 3],
    1009,
    12,
  )
  println("Milnor A2: \{mu_a2}")
  let mu_e8 = @derived.milnor_number(e8, [5, 3], 1009, 30)
  println("Milnor E8: \{mu_e8}")
  let tau_e7 = @derived.tjurina_number(
    @derived.poly_of([([3, 0], 1), ([1, 3], 1)]),
    [3, 2],
    1009,
    18,
  )
  println("Tjurina E7: \{tau_e7}")
  let rep : @derived.QRep = @derived.QRep::new(2, [1, 1], [
    @derived.arrow(0, 1, [[1]]),
    @derived.arrow(0, 1, [[1]]),
  ])
  let (ext0, ext1) = rep.ext01()
  println("Kronecker Ext^0, Ext^1: \{ext0}, \{ext1}")

  // ------------------------------------------------------------------
  // 14-24. The thirteen advanced-mathematics modules.
  // ------------------------------------------------------------------
  println("")
  println("--- rewriting: decidability and confluence ---")
  let ge = @rewriting.constant("e")
  let gmul = fn(x : @rewriting.Term, y : @rewriting.Term) -> @rewriting.Term {
    @rewriting.app("*", [x, y])
  }
  let ginv = fn(x : @rewriting.Term) -> @rewriting.Term {
    @rewriting.app("i", [x])
  }
  let group_eqs = [
    (
      gmul(gmul(@rewriting.v(0), @rewriting.v(1)), @rewriting.v(2)),
      gmul(@rewriting.v(0), gmul(@rewriting.v(1), @rewriting.v(2))),
    ),
    (gmul(ge, @rewriting.v(0)), @rewriting.v(0)),
    (gmul(ginv(@rewriting.v(0)), @rewriting.v(0)), ge),
  ]
  let gprec : Map[String, Int32] = { "*": 1, "i": 2, "e": 0 }
  let s14 = time_us(
    () => {
      let r = @rewriting.complete(group_eqs, gprec, max_steps=400)
      sink[0] = sink[0] + r.rules.length()
    },
    5,
  )
  let kb = @rewriting.complete(group_eqs, gprec, max_steps=400)
  println("Knuth-Bendix completion of group theory us: \{s14}")
  println(
    "  steps=\{kb.steps} rules=\{kb.rules.length()} succeeded=\{kb.succeeded} pending=\{kb.equations_left.length()}",
  )
  let ga = @rewriting.constant("a")
  println(
    "  word problem: a*i(a)=e \{@rewriting.joinable(gmul(ga, ginv(ga)), ge, kb.rules)}, i(i(a))=a \{@rewriting.joinable(ginv(ginv(ga)), ga, kb.rules)}",
  )
  println(
    "  LPO terminating=\{@rewriting.lpo_terminating(kb.rules, gprec)}, locally confluent=\{@rewriting.check_local_confluence(kb.rules).locally_confluent()}",
  )

  println("")
  println("--- demorgan: De Morgan cubical algebra ---")
  let s15 = time_us(
    () => sink[0] = sink[0] + @demorgan.free_dm_algebra(2).length(),
    5,
  )
  println("free De Morgan algebra on 2 generators us: \{s15}")
  println(
    "  |DM(0)|=\{@demorgan.free_dm_algebra(0).length()}, |DM(1)|=\{@demorgan.free_dm_algebra(1).length()}, |DM(2)|=\{@demorgan.free_dm_algebra(2).length()}",
  )

  println("")
  println("--- deform: deformation functor and tower of modules ---")
  let dual5 = @deform.alg_dual_numbers(5)
  let s16 = time_us(() => sink[0] = sink[0] + dual5.hh_dim(2), 5)
  println("HH^2 of the dual numbers over F_5 us: \{s16}")
  for
    (name, alg) in [
      ("F_5", @deform.alg_field(5)),
      ("dual", dual5),
      ("F_5 x F_5", @deform.alg_product(5)),
    ] {
    println(
      "  \{name}: HH^0=\{alg.hh_dim(0)} HH^1=\{alg.hh_dim(1)} HH^2=\{alg.hh_dim(2)}",
    )
  }

  println("")
  println("--- fiber: derived fiber product ---")
  let ms2 = @fiber.Monomials::new(2, 6)
  let ix2 = @fiber.monomial_ideal([[2, 0]])
  let ix1 = @fiber.monomial_ideal([[1, 0]])
  let iy1 = @fiber.monomial_ideal([[0, 1]])
  let s17 = time_us(
    () => sink[0] = sink[0] + @fiber.derived_fiber(ix2, ix1, ms2, 5).serre,
    5,
  )
  println("derived fiber (x^2) vs (x), 2 vars deg<=6, us: \{s17}")
  for
    (name, i, j) in [
      ("(x) vs (y)", ix1, iy1),
      ("(x) vs (x)", ix1, ix1),
      ("(x^2) vs (x)", ix2, ix1),
    ] {
    let df = @fiber.derived_fiber(i, j, ms2, 5)
    println(
      "  \{name}: Tor=\{@core.ints_to_s(df.tor)} classical=\{df.classical} serre=\{df.serre} transverse=\{df.transverse}",
    )
  }

  println("")
  println("--- gauge: connection, curvature, horizontal distribution ---")
  let grid3 = @gauge.Grid::new([3, 3, 3])
  let s3g = @gauge.symmetric3()
  let edges3 : Array[Int32] = []
  let gseed = [31337]
  for _ in 0..<(grid3.nverts() * grid3.ndirs()) {
    gseed[0] = (gseed[0] * 1103 + 12345) % 32768
    edges3.push(gseed[0] % s3g.n)
  }
  let conn3 = @gauge.Connection::from_edges(grid3, s3g, edges3)
  let s18 = time_us(
    () => sink[0] = sink[0] + (if conn3.check_bianchi_all() { 1 } else { 0 }),
    5,
  )
  println("Bianchi d_A F = 0 on every cube of a 3x3x3 grid over S_3 us: \{s18}")
  let flat3 = @gauge.Connection::trivial(@gauge.Grid::new([3, 3]), s3g)
  let bflat = @gauge.Bundle::new(flat3)
  println(
    "  flat S_3 connection on 3x3: leaves=\{bflat.leaves().length()} leaf size=\{bflat.leaf_size(0)} integrable=\{bflat.is_integrable_trivially()}",
  )
  println(
    "  random S_3 connection on 3x3x3: flat=\{conn3.is_flat()} bianchi=\{conn3.check_bianchi_all()}",
  )

  println("")
  println("--- omega: weak omega-groupoids and the groupoid model ---")
  let s19 = time_us(
    () => {
      let (_, _, h) = @omega.h3_order(@omega.gp_cyclic(3), 3)
      sink[0] = sink[0] + h
    },
    3,
  )
  println("H^3(Z/3, Z/3) by exhaustive cocycle enumeration us: \{s19}")
  for (n, m) in [(2, 2), (3, 3), (2, 3)] {
    let (z3, b3, h3) = @omega.h3_order(@omega.gp_cyclic(n), m)
    println("  H^3(Z/\{n}, Z/\{m}): |Z^3|=\{z3} |B^3|=\{b3} |H^3|=\{h3}")
  }
  println(
    "  pi_1 rank: circle=\{@omega.graph_circle().pi1_rank(0)} wedge2=\{@omega.graph_wedge2().pi1_rank(0)} theta=\{@omega.graph_theta().pi1_rank(0)}",
  )
  let gz2 = @omega.group_as_groupoid([[0, 1], [1, 0]], 0)
  println(
    "  UIP: discrete 3-point set=\{@omega.discrete_groupoid(3).is_set()}, Z/2 as a groupoid=\{gz2.is_set()}",
  )
  println(
    "  based path space contractible=\{gz2.based_path_space(0).is_contractible()}, J beta=\{gz2.check_j_beta(0, 42)}",
  )

  println("")
  println("--- cover: universal covering space and local fillability ---")
  let s20 = time_us(
    () => {
      sink[0] = sink[0] +
        @cover.universal_cover(@cover.space_wedge(2), 0, 3).size()
    },
    5,
  )
  println("universal cover of the figure eight, radius 3, us: \{s20}")
  let uc1 = @cover.universal_cover(@cover.space_circle(), 0, 4)
  let uc2 = @cover.universal_cover(@cover.space_wedge(2), 0, 3)
  println(
    "  circle: \{uc1.size()} points, tree=\{uc1.is_tree()} local bijection=\{uc1.is_local_bijection()}",
  )
  println(
    "  figure eight: \{uc2.size()} points, tree=\{uc2.is_tree()} local bijection=\{uc2.is_local_bijection()}",
  )
  let kan = @cover.audit_type(@cubical.const_ty(2, 3), tube_size=1)
  println(
    "  local complementability audit of a constant cubical type: boxes=\{kan.boxes} failures=\{kan.failures} Kan=\{kan.is_kan()}",
  )

  println("")
  println("--- adjoint: adjoint logic ---")
  let aprover = @adjoint.Prover::new(@adjoint.modes_lnl())
  let aa = @adjoint.Formula::Atom(0)
  let s21 = time_us(
    () => {
      sink[0] = sink[0] +
        (if aprover.shift_counit(0, 1, aa) is Some(_) { 1 } else { 0 })
    },
    20,
  )
  println("adjoint proof search (dereliction !A |- A) us: \{s21}")
  let bang_a = @adjoint.bang(0, 1, aa)
  let (der, dig, ctr, wk) = aprover.exponential_laws(0, 1, aa)
  println(
    "  exponential laws for !A = down-up A: dereliction=\{der} dig=\{dig} contraction=\{ctr} weakening=\{wk}",
  )
  println(
    "  shift adjunction holds=\{aprover.adjunction_holds(0, 1, aa, @adjoint.Formula::Atom(1))}",
  )
  let _ = bang_a

  println("")
  println("--- nbe: symbolic execution and normalisation by evaluation ---")
  let nbe_prog = @nbe.Term::If(
    @nbe.Var(1),
    @nbe.If(@nbe.Var(0), @nbe.NatLit(1), @nbe.NatLit(2)),
    @nbe.If(@nbe.Var(1), @nbe.NatLit(3), @nbe.NatLit(4)),
  )
  let s22 = time_us(
    () => {
      let sym = @nbe.Symbolic::new(2)
      sink[0] = sink[0] + sym.run(nbe_prog).length()
    },
    20,
  )
  println("symbolic execution of a 2-variable program us: \{s22}")
  let nsym = @nbe.Symbolic::new(2)
  println(
    "  paths: NbE residual tree=\{nsym.run_nbe(nbe_prog).length()} after feasibility pruning=\{nsym.run(nbe_prog).length()}",
  )
  let (ntested, nbad) = nsym.check_sound(nbe_prog)
  println(
    "  soundness against concrete evaluation: \{ntested} assignments, \{nbad} mismatches; partition=\{nsym.check_partition(nbe_prog)}",
  )
  println(
    "  NbE beta-normal form: \{@nbe.normalize(@nbe.bool_ctx(2), nbe_prog).key()}",
  )

  println("")
  println("--- operad: little cubes ---")
  let s23 = time_us(() => sink[0] = sink[0] + @operad.pi0_config(2, 3, 3), 3)
  println("pi_0 of the discretised C_2(3) (504 placements) us: \{s23}")
  println(
    "  pi_0 C_1(2)=\{@operad.pi0_config(1, 4, 2)} C_1(3)=\{@operad.pi0_config(1, 4, 3)} (k! orderings)",
  )
  println(
    "  pi_0 C_2(2)=\{@operad.pi0_config(2, 3, 2)} C_2(3)=\{@operad.pi0_config(2, 3, 3)} C_3(2)=\{@operad.pi0_config(3, 2, 2)} (connected)",
  )
  println(
    "  swap possible: n=1 \{@operad.can_swap(1, 5)}, n=2 \{@operad.can_swap(2, 3)}, n=3 \{@operad.can_swap(3, 2)}",
  )

  println("")
  println("--- chordarc: chord-arc triangulated polyhedra ---")
  let oct1024 = @chordarc.octahedron(1024)
  let oct_sub = oct1024.subdivide()
  let s24 = time_us(() => sink[0] = sink[0] + oct_sub.geodesics()[0][1], 5)
  println(
    "Floyd-Warshall on the subdivided octahedron (26 vertices) us: \{s24}",
  )
  for
    (name, poly) in [
      ("tetrahedron", @chordarc.tetrahedron(1024)),
      ("octahedron", oct1024),
      ("hairpin(2)", @chordarc.hairpin(2, 64)),
      ("hairpin(6)", @chordarc.hairpin(6, 64)),
    ] {
    match poly.chord_arc_constant() {
      Some((num, den)) =>
        println(
          "  \{name}: V=\{poly.nverts()} F=\{poly.ntris()} chi=\{poly.euler()} chord-arc=\{num}/\{den} closed=\{poly.is_closed()}",
        )
      None => println("  \{name}: degenerate")
    }
  }
  println(
    "  subdivision shortens the octahedron's opposite-vertex geodesic: \{oct1024.geodesics()[0][1]} -> \{oct_sub.geodesics()[0][1] / 6} (2*sqrt2 -> sqrt6, in units of 1/1024)",
  )

  println("")
  println("--- ctt: the type-directed Kan kernel ---")
  // The same law as block 8, but computed by recursion on the type rather
  // than by searching the elements of a finite presheaf.
  let ctt_perms = ctt_permutations(6)
  let s25 = time_us(
    () => {
      let mut ok = 0
      for t in ctt_perms {
        let e = @ctt.Equiv::new(
          @ctt.VFin(6),
          @ctt.VFin(6),
          ctt_fin_fun(t),
          ctt_fin_fun(ctt_inverse(t)),
        )
        for k in 0..<6 {
          if @ctt.quote_norm(@ctt.ua_beta(e, @ctt.VLit(k)), 6) == "#\{t[k]}" {
            ok = ok + 1
          }
        }
      }
      sink[0] = sink[0] + ok
    },
    3,
  )
  println(
    "kernel ua-beta exhaustive Fin 6 (720 equivs, 4320 checks) us: \{s25}",
  )
  // A type with a million elements: the finite model cannot even hold it.
  let big = @ctt.Equiv::new(
    @ctt.VFin(1000000),
    @ctt.VFin(1000000),
    ctt_shift(1000000, 1),
    ctt_shift(1000000, -1),
  )
  let big_path = @ctt.ua(big)
  let s26 = time_us(
    () => {
      sink[0] = sink[0] +
        @ctt.quote_norm(@ctt.transport(big_path, @ctt.VLit(12345)), 6).length()
    },
    200,
  )
  println("kernel transport in Fin 10^6 (per call) us: \{s26}")
  let pi_big = @ctt.VPi(@ctt.VFin(1000), @ctt.Clo::{
    f: fn(_) { @ctt.VFin(1000) },
  })
  let lid_pi = @ctt.comp(
    @ctt.fam_const(pi_big),
    0,
    @ctt.Tube::empty(),
    ctt_fin_fun_table(),
  )
  println(
    "  comp in a space of 1000^1000 functions, applied at 7: \{@ctt.quote_norm(@ctt.vapp(lid_pi, @ctt.VLit(7)), 6)}",
  )
  println(
    "  ua endpoints are strict: \{@ctt.quote_norm(@ctt.vpapp(big_path, @cubical.DZero), 4)} -> \{@ctt.quote_norm(@ctt.vpapp(big_path, @cubical.DOne), 4)}",
  )
  let e3 = @ctt.Equiv::new(
    @ctt.VFin(3),
    @ctt.VFin(3),
    ctt_fin_fun([1, 2, 0]),
    ctt_fin_fun([2, 0, 1]),
  )
  let p3 = @ctt.ua(e3)
  let (eta_l, eta_r) = @ctt.ua_eta(p3)
  println(
    "  J on refl reduces to the given element: \{@ctt.quote_norm(@ctt.pathJ(fn(_, _) { @ctt.VFin(3) }, @ctt.VLit(2), @ctt.refl(@ctt.VLit(0))), 6)}",
  )
  let ua_eta_conv = @ctt.val_conv(eta_l, eta_r)
  println("  ua-eta by unbounded structural conversion: \{ua_eta_conv}")
  // the circle stays a circle: loop is not refl, and formal composites differ
  let loop_is_refl = @ctt.val_conv(@ctt.circle_loop(), @ctt.refl(@ctt.VBase))
  println("  S1: loop = refl is \{loop_is_refl} (must be false)")
  let trunc_prop = @ctt.val_conv(
    @ctt.vpapp(
      @ctt.vapp(
        @ctt.vapp(
          @ctt.trunc_is_prop(@ctt.VTrunc(@ctt.VCircle)),
          @ctt.VInc(@ctt.VBase),
        ),
        @ctt.VInc(@ctt.VBase),
      ),
      @cubical.DZero,
    ),
    @ctt.VInc(@ctt.VBase),
  )
  println("  truncation is a proposition (sq endpoint): \{trunc_prop}")
  bench_faces(sink)
  bench_bidirectional(sink)
}

///|
/// The bidirectional and symmetric layer: what generality costs.
///
/// `coe_between` reindexes along the interpolation line and then runs the
/// directed kernel, so it should cost the same as `coe` up to the folding
/// of `(0 ∧ ~i) ∨ (1 ∧ i)` to `i`.  The equivariance check runs both
/// derivations of reversed composition, which is twice the work.
fn bench_bidirectional(sink : Array[Int32]) -> Unit {
  println("\n== 26. Bidirectional / symmetric Kan operations ==")
  let t : Array[Int32] = []
  for k in 0..<1000 {
    t.push((k + 7) % 1000)
  }
  let e = @ctt.Equiv::new(
    @ctt.VFin(1000),
    @ctt.VFin(1000),
    @ctt.fin_fun(t),
    @ctt.fin_fun(ctt_inverse(t)),
  )
  let fam = @ctt.path_fam(@ctt.ua(e))
  let a = @ctt.VLit(21)
  let s_dir = time_us(
    () => {
      sink[0] = sink[0] +
        (if @ctt.coe(fam, 0, a) == @ctt.VLit(28) { 1 } else { 0 })
    },
    2000,
  )
  let s_bi = time_us(
    () => {
      sink[0] = sink[0] +
        (if @ctt.coe_between(fam, @cubical.DZero, @cubical.DOne, a) ==
          @ctt.VLit(28) {
          1
        } else {
          0
        })
    },
    2000,
  )
  let s_diag = time_us(
    () => {
      sink[0] = sink[0] +
        (if @ctt.coe_between(fam, @cubical.DZero, @cubical.DZero, a) == a {
          1
        } else {
          0
        })
    },
    2000,
  )
  println("  coe^{0->1} on Fin 1000, directed:        \{s_dir} us/call")
  println("  coe^{0->1} via interpolation line:      \{s_bi} us/call")
  println("  coe^{r->r} (diagonal, strict identity): \{s_diag} us/call")
  // equivariance: both derivations of reversed composition, 24 perms
  let mut agree = true
  let mut n = 0
  for t4 in ctt_permutations(4) {
    let e4 = @ctt.Equiv::new(
      @ctt.VFin(4),
      @ctt.VFin(4),
      @ctt.fin_fun(t4),
      @ctt.fin_fun(ctt_inverse(t4)),
    )
    let f4 = @ctt.path_fam(@ctt.ua(e4))
    for k in 0..<4 {
      let cap = @ctt.VLit(k)
      let by_between = @ctt.comp_rev(f4, @ctt.Tube::empty(), cap)
      let by_sym = @ctt.comp_sym(f4, @ctt.Tube::empty(), cap)
      if !@ctt.val_conv(by_between, by_sym) {
        agree = false
      }
      n = n + 1
    }
  }
  println("  equivariance comp_rev = comp_sym: \{agree} over \{n} boxes")
}

///|
/// The face lattice: structural entailment versus exhaustive enumeration.
///
/// The oracle costs `3^n` in the largest direction index, so it cannot be
/// run at all once directions are allocated by the kernel (they start at
/// 100).  The structural procedure has no such dependence, and the point
/// of this block is that the *same* relation is decided at direction
/// 10 000 in microseconds.
fn bench_faces(sink : Array[Int32]) -> Unit {
  println("\n== 25. Face lattice: entailment without a dimension bound ==")
  let n = 6
  let phi = @cubical.CAnd(@cubical.face_cof(0, 1), @cubical.face_cof(1, 0))
  let psi = @cubical.face_cof(0, 1)
  let oracle = time_us(
    () => {
      sink[0] = sink[0] +
        (if @cubical.cof_entails(phi, psi, n) { 1 } else { 0 })
    },
    200,
  )
  let structural = time_us(
    () => sink[0] = sink[0] + (if @cubical.cof_leq(phi, psi) { 1 } else { 0 }),
    2000,
  )
  println("  oracle 3^6 = 729 subcubes, 200 reps: \{oracle} us/call")
  println("  structural, 2000 reps:              \{structural} us/call")
  // a 200-literal conjunction over directions 5000..5199: the oracle would
  // need 3^5200 subcubes, so only the structural side can be run at all
  let mut big = @cubical.CTop
  for i in 0..<200 {
    big = @cubical.CAnd(big, @cubical.face_cof(5000 + i, i % 2))
  }
  let target = @cubical.face_cof(5100, 0)
  let unbounded = time_us(
    () => {
      sink[0] = sink[0] + (if @cubical.cof_leq(big, target) { 1 } else { 0 })
    },
    200,
  )
  println("  200 literals at direction 5000+, 200 reps: \{unbounded} us/call")
  println("  oracle at that direction: 3^5200 subcubes — not runnable")
}

///|
fn ctt_permutations(n : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  let cur : Array[Int32] = []
  let used : Array[Bool] = []
  for _ in 0..<n {
    used.push(false)
  }
  fn go() -> Unit {
    if cur.length() == n {
      out.push(cur[:].to_owned())
      return
    }
    for k in 0..<n {
      if !used[k] {
        used[k] = true
        cur.push(k)
        go()
        ignore(cur.pop())
        used[k] = false
      }
    }
  }
  go()
  out
}

///|
fn ctt_inverse(t : Array[Int32]) -> Array[Int32] {
  let inv : Array[Int32] = []
  for _ in t {
    inv.push(0)
  }
  for k in 0..<t.length() {
    inv[t[k]] = k
  }
  inv
}

///|
fn ctt_fin_fun(table : Array[Int32]) -> @ctt.Val {
  @ctt.fin_fun(table)
}

///|
fn ctt_shift(n : Int32, d : Int32) -> @ctt.Val {
  let t : Array[Int32] = []
  for k in 0..<n {
    t.push((k + d + n) % n)
  }
  @ctt.fin_fun(t)
}

///|
fn ctt_fin_fun_table() -> @ctt.Val {
  let t : Array[Int32] = []
  for k in 0..<1000 {
    t.push(k * 3 % 1000)
  }
  @ctt.fin_fun(t)
}
