///|
/// Explicit trait-method promotions.
///
/// `#derive(Debug, Eq)` used to promote `to_repr`/`equal` to ordinary
/// methods implicitly.  That promotion is deprecated, so every derived
/// trait method a caller uses is declared here instead.  Kept in one file
/// per package; the declarations came from the compiler's own suggestions.
pub extend Alg with Debug::{to_repr}

///|
pub extend Alg with Eq::{not_equal, equal}

///|
pub extend Artin with Debug::{to_repr}

///|
pub extend Artin with Eq::{not_equal, equal}

///|
pub extend ModDeform with Debug::{to_repr}

///|
pub extend ModDeform with Eq::{not_equal, equal}

///|
pub extend ModRep with Debug::{to_repr}

///|
pub extend ModRep with Eq::{not_equal, equal}

///|
pub extend ModTower with Debug::{to_repr}

///|
pub extend SmallExtension with Debug::{to_repr}

///|
pub extend SmallExtension with Eq::{not_equal, equal}
