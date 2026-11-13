///|
/// A finite-dimensional module `V = F_p^k` over `A`, given by the action
/// matrices `act[i]` of the basis elements `e_i`.
///
/// Modules are the points of the deformation functor: deforming `V` over
/// an Artin ring means deforming these matrices, and the tower of such
/// deformations is a formal module.
#derive(Debug, Eq)
pub struct ModRep {
  alg : Alg
  dim : Int32
  act : Array[Array[Array[Int32]]]
}

///|
pub fn ModRep::new(
  alg : Alg,
  dim : Int32,
  act : Array[Array[Array[Int32]]],
) -> ModRep {
  ModRep::{ alg, dim, act, }
}

///|
/// The module axiom: `rho(e_i) rho(e_j) = sum_m c[i][j][m] rho(e_m)`.
/// Cost `O(d^2 k^3)`.
pub fn ModRep::check(self : ModRep) -> Bool {
  let d = self.alg.dim
  let p = self.alg.p
  for i in 0..<d {
    for j in 0..<d {
      let lhs = fp_matmul(self.act[i], self.act[j], p)
      let rhs = fp_mat_zero(self.dim, self.dim)
      for m in 0..<d {
        let c = self.alg.c[i][j][m]
        if c != 0 {
          for a in 0..<self.dim {
            for b in 0..<self.dim {
              rhs[a][b] = fp_add(rhs[a][b], fp_mul(c, self.act[m][a][b], p), p)
            }
          }
        }
      }
      if lhs != rhs {
        return false
      }
    }
  }
  true
}

///|
/// The regular module `A` acting on itself.
pub fn regular_module(alg : Alg) -> ModRep {
  let d = alg.dim
  let act : Array[Array[Array[Int32]]] = []
  for i in 0..<d {
    // rho(e_i) sends e_j to e_i e_j ; column j is c[i][j]
    let mat = fp_mat_zero(d, d)
    for j in 0..<d {
      for t in 0..<d {
        mat[t][j] = alg.c[i][j][t]
      }
    }
    act.push(mat)
  }
  ModRep::{ alg, dim: d, act, }
}

///|
/// `delta^0 : C^0 -> C^1`, `C^0 = End(V)`, `C^1 = Hom(A, End(V))`,
/// `delta^0(X)(a) = rho(a) X - X rho(a)`.  Its kernel is `End_A(V)`,
/// the endomorphism algebra of the module.
pub fn ModRep::delta0(self : ModRep) -> Array[Array[Int32]] {
  let k = self.dim
  let d = self.alg.dim
  let p = self.alg.p
  let mat = fp_mat_zero(d * k * k, k * k)
  for i in 0..<d {
    let rho = self.act[i]
    for a in 0..<k {
      for b in 0..<k {
        let row = i * k * k + a * k + b
        // (rho X)_{ab} = sum_t rho[a][t] X[t][b]
        for t in 0..<k {
          let col = t * k + b
          mat[row][col] = fp_norm(mat[row][col] + rho[a][t], p)
        }
        // -(X rho)_{ab} = -sum_t X[a][t] rho[t][b]
        for t in 0..<k {
          let col = a * k + t
          mat[row][col] = fp_norm(mat[row][col] - rho[t][b], p)
        }
      }
    }
  }
  mat
}

///|
/// `delta^1 : C^1 -> C^2`, `C^2 = Hom(A tensor A, End(V))`,
/// `delta^1(f)(a,b) = rho(a) f(b) - f(ab) + f(a) rho(b)`.
pub fn ModRep::delta1(self : ModRep) -> Array[Array[Int32]] {
  let k = self.dim
  let d = self.alg.dim
  let p = self.alg.p
  let mat = fp_mat_zero(d * d * k * k, d * k * k)
  for i in 0..<d {
    for j in 0..<d {
      for a in 0..<k {
        for b in 0..<k {
          let row = (i * d + j) * k * k + a * k + b
          // rho(e_i) f(e_j)
          for t in 0..<k {
            let col = j * k * k + t * k + b
            mat[row][col] = fp_norm(mat[row][col] + self.act[i][a][t], p)
          }
          // - f(e_i e_j) = -sum_m c[i][j][m] f(e_m)
          for m in 0..<d {
            let c = self.alg.c[i][j][m]
            if c != 0 {
              let col = m * k * k + a * k + b
              mat[row][col] = fp_norm(mat[row][col] - c, p)
            }
          }
          // + f(e_i) rho(e_j)
          for t in 0..<k {
            let col = i * k * k + a * k + t
            mat[row][col] = fp_norm(mat[row][col] + self.act[j][t][b], p)
          }
        }
      }
    }
  }
  mat
}

///|
/// `Ext^0_A(V,V) = End_A(V)`: the stabiliser Lie algebra of the module.
pub fn ModRep::ext0(self : ModRep) -> Int32 {
  fp_kernel(self.delta0(), self.alg.p).length()
}

///|
/// `Ext^1_A(V,V)`: the Zariski tangent space of the module's deformation
/// functor, i.e. deformations over the dual numbers modulo equivalence.
pub fn ModRep::ext1(self : ModRep) -> Int32 {
  fp_homology_dim(self.delta0(), self.delta1(), self.alg.p)
}

///|
/// Verify `delta^1 delta^0 = 0` — this holds precisely because `V` is a
/// module, so it is an independent check of `ModRep::check`.
pub fn ModRep::check_d2(self : ModRep) -> Bool {
  let prod = fp_matmul(self.delta1(), self.delta0(), self.alg.p)
  for row in prod {
    for x in row {
      if x != 0 {
        return false
      }
    }
  }
  true
}

///|
/// A deformation of a module over the Artin ring `R_n`: the action
/// matrices with coefficients in `R_n`, stored as
/// `act[i][a][b]` = an `R_n` element (a coefficient vector).
#derive(Debug, Eq)
pub struct ModDeform {
  alg : Alg
  ring : Artin
  dim : Int32
  act : Array[Array[Array[Array[Int32]]]]
}

///|
/// The constant (trivial) deformation of `V` over `R_n`.
pub fn ModRep::constant_deform(self : ModRep, ring : Artin) -> ModDeform {
  let act : Array[Array[Array[Array[Int32]]]] = []
  for i in 0..<self.alg.dim {
    let mat : Array[Array[Array[Int32]]] = []
    for a in 0..<self.dim {
      let row : Array[Array[Int32]] = []
      for b in 0..<self.dim {
        row.push(ring.from_int(self.act[i][a][b]))
      }
      mat.push(row)
    }
    act.push(mat)
  }
  ModDeform::{ alg: self.alg, ring, dim: self.dim, act, }
}

///|
/// Matrix product over the Artin ring.
fn artin_matmul(
  ring : Artin,
  a : Array[Array[Array[Int32]]],
  b : Array[Array[Array[Int32]]],
  k : Int32,
) -> Array[Array[Array[Int32]]] {
  let out : Array[Array[Array[Int32]]] = []
  for i in 0..<k {
    let row : Array[Array[Int32]] = []
    for j in 0..<k {
      let mut acc = ring.zero()
      for t in 0..<k {
        acc = ring.add(acc, ring.mul(a[i][t], b[t][j]))
      }
      row.push(acc)
    }
    out.push(row)
  }
  out
}

///|
/// Does the deformed action still satisfy the module axiom over `R_n`?
/// This is the equation the deformation functor is defined by.
pub fn ModDeform::check(self : ModDeform) -> Bool {
  let d = self.alg.dim
  let k = self.dim
  for i in 0..<d {
    for j in 0..<d {
      let lhs = artin_matmul(self.ring, self.act[i], self.act[j], k)
      let rhs : Array[Array[Array[Int32]]] = []
      for a in 0..<k {
        let row : Array[Array[Int32]] = []
        for b in 0..<k {
          let mut acc = self.ring.zero()
          for m in 0..<d {
            let c = self.alg.c[i][j][m]
            if c != 0 {
              let term = self.ring.mul(self.ring.from_int(c), self.act[m][a][b])
              acc = self.ring.add(acc, term)
            }
          }
          row.push(acc)
        }
        rhs.push(row)
      }
      if lhs != rhs {
        return false
      }
    }
  }
  true
}

///|
/// Truncate a deformation along the tower map `R_{n+1} -> R_n`.
pub fn ModDeform::truncate(self : ModDeform, to_n : Int32) -> ModDeform {
  let ring = Artin::new(self.ring.p, to_n)
  let act : Array[Array[Array[Array[Int32]]]] = []
  for m in self.act {
    let mat : Array[Array[Array[Int32]]] = []
    for row in m {
      let r : Array[Array[Int32]] = []
      for x in row {
        r.push(self.ring.truncate(x, to_n))
      }
      mat.push(r)
    }
    act.push(mat)
  }
  ModDeform::{ alg: self.alg, ring, dim: self.dim, act, }
}

///|
/// The first-order part of a deformation: the coefficient of `t`, as a
/// Hochschild 1-cochain `f(e_i) = act_1[i]`.
pub fn ModDeform::first_order(self : ModDeform) -> Array[Array[Array[Int32]]]? {
  if self.ring.n < 2 {
    return None
  }
  let out : Array[Array[Array[Int32]]] = []
  for m in self.act {
    let mat : Array[Array[Int32]] = []
    for row in m {
      let r : Array[Int32] = []
      for x in row {
        r.push(x[1])
      }
      mat.push(r)
    }
    out.push(mat)
  }
  Some(out)
}

///|
/// Build a first-order deformation from a Hochschild 1-cocycle `f`,
/// i.e. `rho_t(e_i) = rho(e_i) + t f(e_i)` over the dual numbers.
/// Returns `None` when `f` is not a cocycle (the axiom fails).
pub fn ModRep::deform_by(
  self : ModRep,
  cocycle : Array[Array[Array[Int32]]],
) -> ModDeform? {
  let ring = Artin::new(self.alg.p, 2)
  let act : Array[Array[Array[Array[Int32]]]] = []
  for i in 0..<self.alg.dim {
    let mat : Array[Array[Array[Int32]]] = []
    for a in 0..<self.dim {
      let row : Array[Array[Int32]] = []
      for b in 0..<self.dim {
        let coeff = [self.act[i][a][b], cocycle[i][a][b]]
        row.push(coeff)
      }
      mat.push(row)
    }
    act.push(mat)
  }
  let def = ModDeform::{ alg: self.alg, ring, dim: self.dim, act, }
  if def.check() {
    Some(def)
  } else {
    None
  }
}

///|
/// A basis of the cocycle space `Z^1 = ker delta^1`, each element given as
/// `f[i][a][b]`.  These are exactly the directions in which the module can
/// be deformed to first order.
pub fn ModRep::cocycle_basis(
  self : ModRep,
) -> Array[Array[Array[Array[Int32]]]] {
  let k = self.dim
  let d = self.alg.dim
  let ker = fp_kernel(self.delta1(), self.alg.p)
  let out : Array[Array[Array[Array[Int32]]]] = []
  for vec in ker {
    let f : Array[Array[Array[Int32]]] = []
    for i in 0..<d {
      let mat : Array[Array[Int32]] = []
      for a in 0..<k {
        let row : Array[Int32] = []
        for b in 0..<k {
          row.push(vec[i * k * k + a * k + b])
        }
        mat.push(row)
      }
      f.push(mat)
    }
    out.push(f)
  }
  out
}

///|
/// One step of the module tower: `M_{n+1} -> M_n`.  A tower is a compatible
/// family of deformations, i.e. a point of the formal deformation functor
/// `Def_V(F_p[[t]]) = lim_n Def_V(R_n)`.
#derive(Debug)
pub struct ModTower {
  stages : Array[ModDeform]
}

///|
pub fn ModTower::new(stages : Array[ModDeform]) -> ModTower {
  ModTower::{ stages, }
}

///|
/// The trivial tower, all stages constant.
pub fn trivial_tower(m : ModRep, p : Int32, height : Int32) -> ModTower {
  let stages : Array[ModDeform] = []
  for n in 1..<=height {
    stages.push(m.constant_deform(artin_ring(p, n)))
  }
  ModTower::{ stages, }
}

///|
pub fn artin_ring(p : Int32, n : Int32) -> Artin {
  Artin::new(p, n)
}

///|
/// Compatibility: every stage is a module and truncates to the previous
/// one.  This is exactly the condition for the family to be a point of the
/// inverse limit, so it is the verification a "formal module" must pass.
pub fn ModTower::check(self : ModTower) -> Bool {
  for k in 0..<self.stages.length() {
    let s = self.stages[k]
    if s.ring.n != k + 1 || !s.check() {
      return false
    }
    if k > 0 {
      let prev = self.stages[k - 1]
      if s.truncate(k) != prev {
        return false
      }
    }
  }
  true
}

///|
pub fn ModTower::height(self : ModTower) -> Int32 {
  self.stages.length()
}
