///|
/// # Small integer arithmetic shared by every package
///
/// These were duplicated six times across `algebra`, `cubical`,
/// `homotopy`, `deform`, `omega` and `nbe` before being consolidated here.
/// The scanner in `scripts/health.py` is what found them.

///|
/// `base^exp` for a non-negative exponent, by repeated multiplication.
///
/// Deliberately not exponentiation by squaring: every caller in this
/// repository uses it to size an enumeration (`n^k` cells, `d^{n+1}`
/// cochains), so the exponent is small and the intermediate values must
/// match the order the caller expects when `Int32` arithmetic wraps.
/// A negative exponent gives `1`, the empty product.
pub fn ipow(base : Int32, exp : Int32) -> Int32 {
  let mut acc : Int32 = 1
  for _ in 0..<exp {
    acc = acc * base
  }
  acc
}

///|
/// `2^k`, the size of a Boolean cube of dimension `k`.
pub fn ipow2(k : Int32) -> Int32 {
  ipow(2, k)
}
