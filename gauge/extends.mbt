///|
/// Explicit trait-method promotions.
///
/// `#derive(Debug, Eq)` used to promote `to_repr`/`equal` to ordinary
/// methods implicitly.  That promotion is deprecated, so every derived
/// trait method a caller uses is declared here instead.  Kept in one file
/// per package; the declarations came from the compiler's own suggestions.
pub extend Bundle with Debug::{to_repr}

///|
pub extend Bundle with Eq::{not_equal, equal}

///|
pub extend Connection with Debug::{to_repr}

///|
pub extend Connection with Eq::{not_equal, equal}

///|
pub extend FinGroup with Debug::{to_repr}

///|
pub extend FinGroup with Eq::{not_equal, equal}

///|
pub extend Grid with Debug::{to_repr}

///|
pub extend Grid with Eq::{not_equal, equal}
