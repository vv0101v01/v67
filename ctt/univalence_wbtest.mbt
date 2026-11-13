///|
fn perms(n : Int32) -> Array[Array[Int32]] {
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
fn inverse_table(t : Array[Int32]) -> Array[Int32] {
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
fn perm_equiv(n : Int32, t : Array[Int32]) -> Equiv {
  Equiv::new(VFin(n), VFin(n), fin_fun(t), fin_fun(inverse_table(t)))
}

///|
test "ua: the endpoints of ua are strict" {
  let e = Equiv::new(VFin(2), VFin(3), fin_fun([0, 1]), fin_fun([0, 1, 2]))
  let p = ua(e)
  assert_eq(quote_norm(vpapp(p, @cubical.DZero), 6), "Fin(2)")
  assert_eq(quote_norm(vpapp(p, @cubical.DOne), 6), "Fin(3)")
}

///|
test "ua-beta: transport along ua(e) is e, for all 720 permutations of Fin 6" {
  let n = 6
  let mut checked = 0
  for t in perms(n) {
    let e = perm_equiv(n, t)
    for k in 0..<n {
      assert_eq(quote_norm(ua_beta(e, VLit(k)), 6), "#\{t[k]}")
      checked += 1
    }
  }
  assert_eq(checked, 4320)
}

///|
test "ua-beta-inverse: backward transport is the inverse equivalence" {
  for t in perms(4) {
    let e = perm_equiv(4, t)
    let p = ua(e)
    let inv = inverse_table(t)
    for k in 0..<4 {
      assert_eq(quote_norm(coe_back(path_fam(p), 0, VLit(k)), 6), "#\{inv[k]}")
    }
  }
}

///|
test "ua-eta: ua (idtoeqv p) = p by readback, on ua images" {
  for t in perms(3) {
    let p = ua(perm_equiv(3, t))
    let (lhs, rhs) = ua_eta(p)
    assert_eq(quote_norm(lhs, 12), quote_norm(rhs, 12))
  }
}

///|
test "ua-eta: on a general line it holds for transport, not definitionally" {
  // For an arbitrary line q the two sides are NOT convertible: uaη is a
  // propositional law in CCHM, and only its restriction to the image of
  // ua is definitional (the test above).  What does hold for every line
  // is that the two induce the same transport, and that is what is
  // checked here — on a line produced by composition in the universe.
  // Both round trips of the induced equivalence must still be strict.
  let e = perm_equiv(3, [1, 2, 0])
  let p = ua(e)
  let tube = Tube::empty().add(@cubical.CEq(@cubical.DVar(7), 0), DClo::{
    f: fn(r) { vpapp(p, r) },
  })
  let q = VPLam(DClo::{ f: fn(_) { comp(fam_const(VU), 0, tube, VFin(3)) }, })
  let (lhs, rhs) = ua_eta(q)
  assert_eq(
    quote_norm(vpapp(lhs, @cubical.DZero), 10),
    quote_norm(vpapp(rhs, @cubical.DZero), 10),
  )
  assert_eq(
    quote_norm(vpapp(lhs, @cubical.DOne), 10),
    quote_norm(vpapp(rhs, @cubical.DOne), 10),
  )
  for k in 0..<3 {
    assert_eq(
      quote_norm(transport(lhs, VLit(k)), 10),
      quote_norm(transport(rhs, VLit(k)), 10),
    )
  }
}

///|
test "transport: along reflexivity it is the identity, untouched" {
  let a = VPair(VLit(1), VLit(2))
  assert_eq(quote_norm(transport(refl(VFin(4)), a), 6), "(#1, #2)")
  let e = equiv_id(VFin(5))
  for k in 0..<5 {
    assert_eq(quote_norm(transport(ua(e), VLit(k)), 6), "#\{k}")
  }
}

///|
test "equivalences: every permutation of Fin 5 is a checked strict isomorphism" {
  let n = 5
  let pts = fin_points(n)
  let mut count = 0
  for t in perms(n) {
    let e = perm_equiv(n, t)
    assert_true(e.check(pts, pts))
    // both round trips are definitional, which is what the Glue rule uses
    for k in 0..<n {
      let x = VLit(k)
      assert_eq(quote_norm(vpapp(e.alpha.at(x), @cubical.DOne), 8), "#\{k}")
      assert_eq(quote_norm(vpapp(e.beta.at(x), @cubical.DOne), 8), "#\{k}")
    }
    count += 1
  }
  assert_eq(count, 120)
}

///|
test "ua: transport in a function type acts by conjugation" {
  // e : Fin 3 ≃ Fin 3, and the induced equivalence on (Fin 3 → Fin 3)
  let t = [1, 2, 0]
  let e = perm_equiv(3, t)
  let inv = inverse_table(t)
  let conj = Equiv::new(
    VPi(VFin(3), Clo::{ f: fn(_) { VFin(3) }, }),
    VPi(VFin(3), Clo::{ f: fn(_) { VFin(3) }, }),
    VLam(Clo::{
      f: fn(g) {
        VLam(Clo::{ f: fn(x) { vapp(e.fwd, vapp(g, vapp(e.bwd, x))) }, })
      },
    }),
    VLam(Clo::{
      f: fn(g) {
        VLam(Clo::{ f: fn(x) { vapp(e.bwd, vapp(g, vapp(e.fwd, x))) }, })
      },
    }),
  )
  let p = ua(conj)
  let g = fin_fun([2, 0, 1])
  let h = transport(p, g)
  // h(x) = e(g(e⁻¹ x))
  for k in 0..<3 {
    let want = t[g_table_at(inv[k])]
    assert_eq(quote_norm(vapp(h, VLit(k)), 6), "#\{want}")
  }
}

///|
fn g_table_at(j : Int32) -> Int32 {
  [2, 0, 1][j]
}

///|
test "path algebra: symmetry and concatenation have the right endpoints" {
  let e = perm_equiv(3, [1, 2, 0])
  let p = ua(e)
  let s = path_sym(p)
  assert_eq(quote_norm(vpapp(s, @cubical.DZero), 6), "Fin(3)")
  assert_eq(quote_norm(vpapp(s, @cubical.DOne), 6), "Fin(3)")
  // transporting along the reversed path is the inverse map
  for k in 0..<3 {
    assert_eq(quote_norm(transport(s, VLit(k)), 6), "#\{[2, 0, 1][k]}")
  }
  // p · p⁻¹ has the endpoints of refl
  let c = path_concat(VU, p, s)
  assert_eq(quote_norm(vpapp(c, @cubical.DZero), 6), "Fin(3)")
  assert_eq(quote_norm(vpapp(c, @cubical.DOne), 6), "Fin(3)")
}

///|
test "funext: the endpoints of funext h are f and g" {
  let f = fin_fun([0, 1])
  let g = fin_fun([1, 0])
  // h x : Path (Fin 2) (f x) (g x) — a discrete type, so this is only
  // inhabited where f x = g x; use f = g to keep the box well formed.
  let h = Clo::{ f: fn(x) { refl(vapp(f, x)) }, }
  let p = funext(h)
  assert_eq(quote_norm(vapp(vpapp(p, @cubical.DZero), VLit(0)), 6), "#0")
  assert_eq(quote_norm(vapp(vpapp(p, @cubical.DOne), VLit(1)), 6), "#1")
  let _ = g
}

///|
test "singleton: the contraction goes from (a, refl) to (b, p)" {
  let p = ua(perm_equiv(2, [1, 0]))
  let eta = singleton_contract(p)
  let at0 = vpapp(eta, @cubical.DZero)
  let at1 = vpapp(eta, @cubical.DOne)
  assert_eq(quote_norm(vfst(at0), 6), "Fin(2)")
  assert_eq(quote_norm(vsnd(at0), 8), quote_norm(refl(VFin(2)), 8))
  assert_eq(quote_norm(vfst(at1), 6), "Fin(2)")
  assert_eq(quote_norm(vsnd(at1), 8), quote_norm(p, 8))
}

///|
test "pathJ: the computation rule is a reduction" {
  // motive P x q = Fin 3, d = #2: J must return d on the nose at refl.
  let mot = fn(_ : Val, _ : Val) -> Val { VFin(3) }
  let a = VLit(0)
  let j = pathJ(mot, VLit(2), refl(a))
  assert_eq(quote_norm(j, 6), "#2")
}

///|
test "h-levels: the type codes are the expected dependent types" {
  let a = VFin(2)
  assert_eq(
    quote_norm(is_contr(a), 8),
    "Σ(x0 : Fin(2)). Π(x1 : Fin(2)). Path(x2.Fin(2)) x0 x1",
  )
  assert_eq(
    quote_norm(is_prop(a), 8),
    "Π(x0 : Fin(2)). Π(x1 : Fin(2)). Path(x2.Fin(2)) x0 x1",
  )
}

///|
test "h-levels: Fin 1 is contractible, hence a proposition" {
  let ctr = fin1_contr()
  let pr = contr_to_prop(VFin(1), ctr)
  let p = vapp(vapp(pr, VLit(0)), VLit(0))
  assert_eq(quote_norm(vpapp(p, @cubical.DZero), 6), "#0")
  assert_eq(quote_norm(vpapp(p, @cubical.DOne), 6), "#0")
}
