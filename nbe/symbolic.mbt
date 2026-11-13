///|
using @cubical {type Dim, dim_eq}

///|
/// **Symbolic execution over the De Morgan cubical algebra.**
///
/// A path condition is a dimension term: `0`, `1`, a variable, `~`, `/\`,
/// `\/`.  Reusing `cubical.Dim` means path conditions come with a canonical
/// form and a *decidable* equality (`dim_eq`) for free — and, importantly,
/// with the right notion of equality: De Morgan equality is finer than
/// Boolean equality, so `x /\ ~x` is not `0` as a dimension term even
/// though it is unsatisfiable as a Boolean formula.  Feasibility of a path
/// is therefore a *separate* decision procedure from equivalence of
/// guards, and both are provided.
#derive(Debug, Eq)
pub struct Symbolic {
  /// number of Boolean variables in scope
  nvars : Int32
  /// generators allocated for opaque_atoms (non-variable) conditions
  mut next : Int32
  opaque_atoms : Map[String, Int32]
}

///|
pub fn Symbolic::new(nvars : Int32) -> Symbolic {
  Symbolic::{ nvars, next: nvars, opaque_atoms: Map([]), }
}

///|
/// The number of atoms a path_cond may mention, including opaque_atoms conditions.
pub fn Symbolic::natoms(self : Symbolic) -> Int32 {
  self.next
}

///|
/// Read a Boolean *value* as a path_cond.  Variables become generators, a
/// residual `if` becomes `(c /\ a) \/ (~c /\ b)`, and anything else gets a
/// stable fresh generator keyed by its normal form.
pub fn Symbolic::cond_of(self : Symbolic, v : Value) -> Dim {
  match v {
    VBool(true) => @cubical.DOne
    VBool(false) => @cubical.DZero
    VNe(NVar(i)) => @cubical.DVar(i)
    VNe(NIf(c, a, b)) => {
      let dc = self.cond_of(c)
      let da = self.cond_of(a)
      let db = self.cond_of(b)
      @cubical.DOr(@cubical.DAnd(dc, da), @cubical.DAnd(@cubical.DNot(dc), db))
    }
    _ => {
      let key = reify(self.nvars, v).key()
      match self.opaque_atoms.get(key) {
        Some(i) => @cubical.DVar(i)
        None => {
          let i = self.next
          self.next = i + 1
          self.opaque_atoms[key] = i
          @cubical.DVar(i)
        }
      }
    }
  }
}

///|
/// One path of a symbolic run: the condition under which it is taken and
/// the value it produces.
#derive(Debug, Eq)
pub struct Leaf {
  path_cond : Dim
  value : Value
}

///|
pub fn Leaf::new(path_cond : Dim, value : Value) -> Leaf {
  Leaf::{ path_cond, value, }
}

///|
/// Read the decision tree off a semantic value.  This is the bridge
/// between NbE and symbolic execution: `eval` already residualised every
/// branch it could not decide, so the leaves of the residual `if`-tree
/// *are* the symbolic paths, and the accumulated conjunction of branch
/// conditions *is* the path condition.
pub fn Symbolic::leaves(
  self : Symbolic,
  v : Value,
  path_cond : Dim,
) -> Array[Leaf] {
  match v {
    VNe(NIf(c, a, b)) => {
      let d = self.cond_of(c)
      let out = self.leaves(a, @cubical.DAnd(path_cond, d))
      for l in self.leaves(b, @cubical.DAnd(path_cond, @cubical.DNot(d))) {
        out.push(l)
      }
      out
    }
    _ => [Leaf::{ path_cond, value: v, }]
  }
}

///|
/// Symbolic execution as NbE: evaluate with free variables, then read the
/// decision tree.  No path is pruned, so infeasible paths are still
/// present — which is what makes the comparison with the pruning
/// executor below meaningful.
pub fn Symbolic::run_nbe(self : Symbolic, t : Term) -> Array[Leaf] {
  self.leaves(eval(symbolic_env(self.nvars), t), @cubical.DOne)
}

///|
/// An independent symbolic executor: it splits at each conditional as it
/// goes and *prunes* paths whose condition is unsatisfiable.  The control
/// flow is genuinely different from `eval` — no residual `if` is ever
/// built — so agreement between the two is a real cross-check.
pub fn Symbolic::exec(
  self : Symbolic,
  env : Array[Value],
  t : Term,
  path_cond : Dim,
) -> Array[Leaf] {
  match t {
    Var(i) => [Leaf::{ path_cond, value: env[env.length() - 1 - i], }]
    Lam(ty, b) => [Leaf::{ path_cond, value: VLam(ty, env[:].to_owned(), b), }]
    BoolLit(b) => [Leaf::{ path_cond, value: VBool(b), }]
    NatLit(n) => [Leaf::{ path_cond, value: VNat(n), }]
    App(f, a) => {
      let out : Array[Leaf] = []
      for lf in self.exec(env, f, path_cond) {
        for la in self.exec(env, a, lf.path_cond) {
          match lf.value {
            VLam(_, cenv, body) => {
              // enter the body with the executor, so that conditionals
              // inside the function are split too
              let e = cenv[:].to_owned()
              e.push(la.value)
              for l in self.exec(e, body, la.path_cond) {
                out.push(l)
              }
            }
            _ =>
              out.push(Leaf::{
                path_cond: la.path_cond,
                value: apply(lf.value, la.value),
              })
          }
        }
      }
      out
    }
    Add(a, b) => {
      let out : Array[Leaf] = []
      for lx in self.exec(env, a, path_cond) {
        for ly in self.exec(env, b, lx.path_cond) {
          let v = match (lx.value, ly.value) {
            (VNat(m), VNat(n)) => VNat(m + n)
            (x, y) => VNe(NAdd(x, y))
          }
          out.push(Leaf::{ path_cond: ly.path_cond, value: v, })
        }
      }
      out
    }
    IsZero(a) => {
      let out : Array[Leaf] = []
      for lx in self.exec(env, a, path_cond) {
        let v = match lx.value {
          VNat(0) => VBool(true)
          VNat(_) => VBool(false)
          x => VNe(NIsZero(x))
        }
        out.push(Leaf::{ path_cond: lx.path_cond, value: v, })
      }
      out
    }
    If(c, a, b) => {
      let out : Array[Leaf] = []
      for lc in self.exec(env, c, path_cond) {
        match lc.value {
          VBool(true) =>
            for l in self.exec(env, a, lc.path_cond) {
              out.push(l)
            }
          VBool(false) =>
            for l in self.exec(env, b, lc.path_cond) {
              out.push(l)
            }
          cv => {
            let d = self.cond_of(cv)
            let gthen = @cubical.DAnd(lc.path_cond, d)
            let gelse = @cubical.DAnd(lc.path_cond, @cubical.DNot(d))
            if self.feasible(gthen) {
              for l in self.exec(env, a, gthen) {
                out.push(l)
              }
            }
            if self.feasible(gelse) {
              for l in self.exec(env, b, gelse) {
                out.push(l)
              }
            }
          }
        }
      }
      out
    }
  }
}

///|
/// Symbolic execution with pruning, starting from the top path_cond.
pub fn Symbolic::run(self : Symbolic, t : Term) -> Array[Leaf] {
  self.exec(symbolic_env(self.nvars), t, @cubical.DOne)
}

///|
/// Evaluate a path_cond under a total Boolean assignment, using the Kleene
/// evaluator of the interval algebra restricted to `{0, 1}`.
pub fn guard_holds(d : Dim, asg : Array[Bool]) -> Bool {
  let digits : Array[Int32] = []
  for b in asg {
    digits.push(if b { 1 } else { 0 })
  }
  d.eval3(digits) == 1
}

///|
/// The `k`-th truth assignment on `n` variables, in binary order.
pub fn assignment(n : Int32, k : Int32) -> Array[Bool] {
  let out : Array[Bool] = []
  for i in 0..<n {
    out.push(k / @core.ipow2(i) % 2 == 1)
  }
  out
}

///|
/// **Feasibility**, decided by exhaustive enumeration over `2^n`
/// assignments.  This is Boolean satisfiability, *not* De Morgan
/// equality: `x /\ ~x` is a nonzero dimension term but an infeasible path.
pub fn Symbolic::feasible(self : Symbolic, d : Dim) -> Bool {
  let n = self.natoms()
  for k in 0..<@core.ipow2(n) {
    if guard_holds(d, assignment(n, k)) {
      return true
    }
  }
  false
}

///|
/// The number of satisfying assignments of a path_cond.
pub fn Symbolic::model_count(self : Symbolic, d : Dim) -> Int32 {
  let n = self.natoms()
  let mut c = 0
  for k in 0..<@core.ipow2(n) {
    if guard_holds(d, assignment(n, k)) {
      c = c + 1
    }
  }
  c
}

///|
/// Boolean equivalence of guards (coarser than `dim_eq`).
pub fn Symbolic::guard_equiv(self : Symbolic, a : Dim, b : Dim) -> Bool {
  let n = self.natoms()
  for k in 0..<@core.ipow2(n) {
    let asg = assignment(n, k)
    if guard_holds(a, asg) != guard_holds(b, asg) {
      return false
    }
  }
  true
}

///|
/// De Morgan equivalence of guards, via the canonical DNF of the interval
/// algebra.  Strictly finer than Boolean equivalence.
pub fn guard_dm_eq(a : Dim, b : Dim) -> Bool {
  dim_eq(a, b)
}

///|
/// The feasible paths of a run, in order.
pub fn feasible_leaves(sym : Symbolic, ls : Array[Leaf]) -> Array[Leaf] {
  let out : Array[Leaf] = []
  for l in ls {
    if sym.feasible(l.path_cond) {
      out.push(l)
    }
  }
  out
}

///|
/// **Soundness and completeness of symbolic execution.**  For every total
/// assignment exactly one path is enabled, and its value is the concrete
/// result.  Checked exhaustively, so this is a finite proof for the given
/// program.
pub fn Symbolic::check_sound(self : Symbolic, t : Term) -> (Int32, Int32) {
  self.check_sound_leaves(t, self.run(t))
}

///|
/// The same check for the NbE-based run, after discarding infeasible
/// paths.  Validating both executors against concrete evaluation is what
/// licenses treating them as interchangeable.
pub fn Symbolic::check_sound_nbe(self : Symbolic, t : Term) -> (Int32, Int32) {
  let ls = feasible_leaves(self, self.run_nbe(t))
  self.check_sound_leaves(t, ls)
}

///|
pub fn Symbolic::check_sound_leaves(
  self : Symbolic,
  t : Term,
  ls : Array[Leaf],
) -> (Int32, Int32) {
  let mut tested = 0
  let mut bad = 0
  for k in 0..<@core.ipow2(self.nvars) {
    let asg = assignment(self.nvars, k)
    let cenv = concrete_env(asg)
    let concrete = eval(cenv, t)
    let mut hits = 0
    for l in ls {
      if guard_holds(l.path_cond, asg) {
        hits = hits + 1
        // a leaf of the NbE run may still be a residual term, so read it
        // back and evaluate it under the assignment before comparing
        let got = eval(cenv, reify(self.nvars, l.value))
        if got != concrete {
          bad = bad + 1
        }
      }
    }
    tested = tested + 1
    if hits != 1 {
      bad = bad + 1
    }
  }
  (tested, bad)
}

///|
/// **Partition property.**  The feasible path conditions are pairwise
/// disjoint and cover the whole assignment space.
pub fn Symbolic::check_partition(self : Symbolic, t : Term) -> Bool {
  let ls = self.run(t)
  let mut total = 0
  for i in 0..<ls.length() {
    total = total + self.model_count(ls[i].path_cond)
    for j in (i + 1)..<ls.length() {
      if self.feasible(@cubical.DAnd(ls[i].path_cond, ls[j].path_cond)) {
        return false
      }
    }
  }
  total == @core.ipow2(self.natoms())
}
