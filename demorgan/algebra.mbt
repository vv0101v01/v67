///|
/// The free De Morgan algebra on `n` generators, presented as a *canonical
/// antichain of literal conjunctions*.
///
/// A literal is coded `2*i` for `x_i` and `2*i+1` for `~x_i`.  An element is
/// a finite antichain of finite literal sets, read as a disjunction of
/// conjunctions; `[]` is `0` and `[[]]` is `1`.  Unlike a Boolean algebra
/// there is no complementation law: `x /\ ~x` is a nonzero element, and
/// `x \/ ~x` is not `1`.  This is exactly what makes the cubical interval
/// an interval rather than a two-point set.
#derive(Debug, Eq)
pub struct DMA {
  terms : Array[Array[Int32]]
}

///|
pub fn DMA::zero() -> DMA {
  DMA::{ terms: [], }
}

///|
pub fn DMA::one() -> DMA {
  DMA::{ terms: [[]], }
}

///|
pub fn DMA::gen(i : Int32) -> DMA {
  DMA::{ terms: [[2 * i]], }
}

///|
pub fn DMA::neg_gen(i : Int32) -> DMA {
  DMA::{ terms: [[2 * i + 1]], }
}

///|
fn sorted_unique(xs : Array[Int32]) -> Array[Int32] {
  let ys = xs[:].to_owned()
  ys.sort()
  let out : Array[Int32] = []
  for x in ys {
    if out.length() == 0 || out[out.length() - 1] != x {
      out.push(x)
    }
  }
  out
}

///|
fn subset_of(a : Array[Int32], b : Array[Int32]) -> Bool {
  for x in a {
    if !b.contains(x) {
      return false
    }
  }
  true
}

///|
/// Antichain normalisation: sort literals inside each conjunction, remove
/// duplicate conjunctions, then drop every conjunction that strictly
/// contains another (absorption `x \/ (x /\ y) = x`), then sort the list.
/// Two elements of the free De Morgan algebra are equal iff their
/// antichain normal forms coincide, so this is a decision procedure.
pub fn DMA::canon(terms : Array[Array[Int32]]) -> DMA {
  let norm : Array[Array[Int32]] = []
  for t in terms {
    let st = sorted_unique(t)
    if !norm.contains(st) {
      norm.push(st)
    }
  }
  let kept : Array[Array[Int32]] = []
  for t in norm {
    let mut absorbed = false
    for u in norm {
      if u.length() < t.length() && subset_of(u, t) {
        absorbed = true
      }
    }
    if !absorbed {
      kept.push(t)
    }
  }
  kept.sort_by(fn(a, b) {
    let n = if a.length() < b.length() { a.length() } else { b.length() }
    for k in 0..<n {
      if a[k] != b[k] {
        return if a[k] < b[k] { -1 } else { 1 }
      }
    }
    a.length().compare(b.length())
  })
  DMA::{ terms: kept, }
}

///|
pub fn DMA::join(a : DMA, b : DMA) -> DMA {
  let ts : Array[Array[Int32]] = []
  for t in a.terms {
    ts.push(t)
  }
  for t in b.terms {
    ts.push(t)
  }
  DMA::canon(ts)
}

///|
/// Meet distributes over the antichain: pairwise union of literal sets.
/// Cost `O(|a| * |b|)` conjunctions before absorption.
pub fn DMA::meet(a : DMA, b : DMA) -> DMA {
  let ts : Array[Array[Int32]] = []
  for x in a.terms {
    for y in b.terms {
      let m : Array[Int32] = []
      for v in x {
        m.push(v)
      }
      for v in y {
        m.push(v)
      }
      ts.push(m)
    }
  }
  DMA::canon(ts)
}

///|
/// De Morgan involution: swap the polarity of every literal and exchange
/// meet with join.  `~~a = a`, `~(a /\ b) = ~a \/ ~b`.
pub fn DMA::negate(self : DMA) -> DMA {
  // ~ (\/_i /\_j l_ij) = /\_i \/_j ~l_ij : distribute
  let mut acc = DMA::one()
  for conj in self.terms {
    let lits : Array[Array[Int32]] = []
    for l in conj {
      lits.push([l ^ 1])
    }
    acc = DMA::meet(acc, DMA::canon(lits))
  }
  acc
}

///|
pub fn DMA::is_zero(self : DMA) -> Bool {
  self.terms.length() == 0
}

///|
pub fn DMA::is_one(self : DMA) -> Bool {
  self.terms.length() == 1 && self.terms[0].length() == 0
}

///|
/// Lattice order: `a <= b` iff `a \/ b = b`.
pub fn DMA::leq(a : DMA, b : DMA) -> Bool {
  DMA::join(a, b) == b
}

///|
/// Three-valued evaluation, the semantics of a subcube: digit `2` means
/// the coordinate is still free (the generic point of that direction).
pub fn DMA::eval3(self : DMA, asg : Array[Int32]) -> Int32 {
  let mut best = 0
  for conj in self.terms {
    let mut val = 1
    for l in conj {
      let d = asg[l / 2]
      let lit = if l % 2 == 0 {
        d
      } else {
        match d {
          0 => 1
          1 => 0
          _ => 2
        }
      }
      if lit == 0 {
        val = 0
      } else if lit == 2 && val == 1 {
        val = 2
      }
    }
    if val == 1 {
      return 1
    }
    if val == 2 {
      best = 2
    }
  }
  best
}

///|
/// Bridge to the interval terms of the `cubical` package.
pub fn DMA::of_dim(r : Dim) -> DMA {
  match r {
    @cubical.DZero => DMA::zero()
    @cubical.DOne => DMA::one()
    @cubical.DVar(i) => DMA::gen(i)
    @cubical.DNot(x) => DMA::of_dim(x).negate()
    @cubical.DAnd(a, b) => DMA::meet(DMA::of_dim(a), DMA::of_dim(b))
    @cubical.DOr(a, b) => DMA::join(DMA::of_dim(a), DMA::of_dim(b))
  }
}

///|
pub fn DMA::to_dim(self : DMA) -> Dim {
  if self.terms.length() == 0 {
    return @cubical.DZero
  }
  let mut acc : Dim? = None
  for conj in self.terms {
    let mut c : Dim? = None
    for l in conj {
      let atom = if l % 2 == 0 {
        @cubical.DVar(l / 2)
      } else {
        @cubical.DNot(@cubical.DVar(l / 2))
      }
      c = match c {
        None => Some(atom)
        Some(prev) => Some(@cubical.DAnd(prev, atom))
      }
    }
    let term = match c {
      None => @cubical.DOne
      Some(t) => t
    }
    acc = match acc {
      None => Some(term)
      Some(prev) => Some(@cubical.DOr(prev, term))
    }
  }
  match acc {
    None => @cubical.DZero
    Some(t) => t
  }
}

///|
pub fn DMA::render(self : DMA) -> String {
  if self.terms.length() == 0 {
    return "0"
  }
  let parts : Array[String] = []
  for conj in self.terms {
    if conj.length() == 0 {
      parts.push("1")
    } else {
      let ls : Array[String] = []
      for l in conj {
        ls.push(if l % 2 == 0 { "x\{l / 2}" } else { "~x\{l / 2}" })
      }
      parts.push(ls.join("/\\"))
    }
  }
  parts.join(" \\/ ")
}

///|
/// The free De Morgan algebra on one generator has exactly 6 elements:
/// `0, x/\~x, x, ~x, x\/~x, 1`.  (The free Boolean algebra on one generator
/// has 4; the two extra elements are the "generic interval" ones.)
pub fn free_dm_algebra(n : Int32) -> Array[DMA] {
  // generate all antichains by closing {0,1,x_i,~x_i} under meet and join
  let seen : Array[DMA] = []
  let push = fn(d : DMA) -> Bool {
    if seen.contains(d) {
      false
    } else {
      seen.push(d)
      true
    }
  }

  ignore(push(DMA::zero()))
  ignore(push(DMA::one()))
  for i in 0..<n {
    ignore(push(DMA::gen(i)))
    ignore(push(DMA::neg_gen(i)))
  }
  let mut frontier = 0
  while frontier < seen.length() {
    let upto = seen.length()
    for i in frontier..<upto {
      for j in 0..<upto {
        ignore(push(DMA::meet(seen[i], seen[j])))
        ignore(push(DMA::join(seen[i], seen[j])))
      }
    }
    frontier = upto
  }
  seen
}
