///|
/// Explicit trait-method promotions.
///
/// `#derive(Debug, Eq)` used to promote `to_repr`/`equal` to ordinary
/// methods implicitly.  That promotion is deprecated, so every derived
/// trait method a caller uses is declared here instead.  Kept in one file
/// per package; the declarations came from the compiler's own suggestions.
pub extend DerivedFiber with Debug::{to_repr}

///|
pub extend MonomialIdeal with Debug::{to_repr}

///|
pub extend MonomialIdeal with Eq::{not_equal, equal}

///|
pub extend Monomials with Debug::{to_repr}

///|
pub extend Monomials with Eq::{not_equal, equal}

///|
pub extend Quotient with Debug::{to_repr}

///|
pub extend Quotient with Eq::{not_equal, equal}

///|
pub extend Taylor with Debug::{to_repr}

///|
pub extend TorBasis with Debug::{to_repr}

///|
pub extend TorBasis with Eq::{not_equal, equal}

///|
pub extend TorComplex with Debug::{to_repr}
