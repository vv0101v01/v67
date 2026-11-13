///|
/// The operad axioms, as decidable predicates on exact integer data.
/// Because composition is exact, "associativity" here is literal equality
/// of configurations — not equality up to homotopy.

///|
/// Associativity: `γ(γ(c; d₁…d_k); e₁₁…) = γ(c; γ(d₁; e₁*), …, γ(d_k; e_k*))`,
/// where the flat list `es` is split according to the arities of the `ds`.
pub fn check_associativity(
  c : Config,
  ds : Array[Config],
  es : Array[Config],
) -> Bool {
  let inner = match c.compose(ds) {
    None => return false
    Some(x) => x
  }
  if inner.arity() != es.length() {
    return false
  }
  let lhs = match inner.compose(es) {
    None => return false
    Some(x) => x
  }
  // regroup es by the arities of the ds
  let groups : Array[Config] = []
  let mut at = 0
  for d in ds {
    let chunk : Array[Config] = []
    for _ in 0..<d.arity() {
      if at >= es.length() {
        return false
      }
      chunk.push(es[at])
      at = at + 1
    }
    match d.compose(chunk) {
      None => return false
      Some(g) => groups.push(g)
    }
  }
  match c.compose(groups) {
    None => false
    Some(rhs) => lhs == rhs
  }
}

///|
/// The unit laws: `γ(ι; c) = c` and `γ(c; ι, …, ι) = c`.
pub fn check_unit(c : Config) -> Bool {
  let unit = operad_unit(c.dim)
  match unit.compose([c]) {
    None => return false
    Some(left) => if left != c { return false }
  }
  let units : Array[Config] = []
  for _ in 0..<c.arity() {
    units.push(operad_unit(c.dim))
  }
  match c.compose(units) {
    None => false
    Some(right) => right == c
  }
}

///|
/// The flattened permutation of blocks: block `i` of the left-hand side
/// is block `sigma[i]` of the right-hand side.
fn block_sigma(sigma : Array[Int32], sizes : Array[Int32]) -> Array[Int32] {
  let k = sigma.length()
  // inverse of sigma
  let inv = Array::make(k, 0)
  for i in 0..<k {
    inv[sigma[i]] = i
  }
  // offset of each block on the right, whose block j has size sizes[inv[j]]
  let off = Array::make(k, 0)
  let mut acc = 0
  for j in 0..<k {
    off[j] = acc
    acc = acc + sizes[inv[j]]
  }
  let out : Array[Int32] = []
  for i in 0..<k {
    let base = off[sigma[i]]
    for t in 0..<sizes[i] {
      out.push(base + t)
    }
  }
  out
}

///|
/// Equivariance in the outer variable:
/// `γ(c·σ; d₁…d_k) = γ(c; d_{σ⁻¹(1)}…d_{σ⁻¹(k)})·(block σ)`.
pub fn check_equivariance_outer(
  c : Config,
  ds : Array[Config],
  sigma : Array[Int32],
) -> Bool {
  let k = c.arity()
  if ds.length() != k || sigma.length() != k {
    return false
  }
  let cs = match c.permute(sigma) {
    None => return false
    Some(x) => x
  }
  let lhs = match cs.compose(ds) {
    None => return false
    Some(x) => x
  }
  let inv = Array::make(k, 0)
  for i in 0..<k {
    inv[sigma[i]] = i
  }
  let shuffled : Array[Config] = []
  let sizes : Array[Int32] = []
  for j in 0..<k {
    shuffled.push(ds[inv[j]])
  }
  for d in ds {
    sizes.push(d.arity())
  }
  let base = match c.compose(shuffled) {
    None => return false
    Some(x) => x
  }
  match base.permute(block_sigma(sigma, sizes)) {
    None => false
    Some(rhs) => lhs == rhs
  }
}

///|
/// Equivariance in the inner variables:
/// `γ(c; d₁·τ₁, …, d_k·τ_k) = γ(c; d₁…d_k)·(τ₁ ⊕ … ⊕ τ_k)`.
pub fn check_equivariance_inner(
  c : Config,
  ds : Array[Config],
  taus : Array[Array[Int32]],
) -> Bool {
  if ds.length() != c.arity() || taus.length() != c.arity() {
    return false
  }
  let permuted : Array[Config] = []
  let flat : Array[Int32] = []
  let mut offset = 0
  for i in 0..<ds.length() {
    match ds[i].permute(taus[i]) {
      None => return false
      Some(p) => permuted.push(p)
    }
    for t in taus[i] {
      flat.push(offset + t)
    }
    offset = offset + ds[i].arity()
  }
  let lhs = match c.compose(permuted) {
    None => return false
    Some(x) => x
  }
  let base = match c.compose(ds) {
    None => return false
    Some(x) => x
  }
  match base.permute(flat) {
    None => false
    Some(rhs) => lhs == rhs
  }
}

///|
/// Composition preserves membership in `C_n(k)`: inserting valid
/// configurations into a valid one gives a valid one.  This is the
/// geometric content of the operad structure — disjointness is preserved
/// because the images of distinct outer cubes are disjoint.
pub fn compose_preserves_valid(c : Config, ds : Array[Config]) -> Bool {
  if !c.valid() {
    return false
  }
  for d in ds {
    if !d.valid() {
      return false
    }
  }
  match c.compose(ds) {
    None => false
    Some(g) => g.valid()
  }
}
