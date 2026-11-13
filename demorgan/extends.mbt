///|
/// Explicit trait-method promotions.
///
/// `#derive(Debug, Eq)` used to promote `to_repr`/`equal` to ordinary
/// methods implicitly.  That promotion is deprecated, so every derived
/// trait method a caller uses is declared here instead.  Kept in one file
/// per package; the declarations came from the compiler's own suggestions.
pub extend CubeMap with Debug::{to_repr}

///|
pub extend CubeMap with Eq::{not_equal, equal}

///|
pub extend DMA with Debug::{to_repr}

///|
pub extend DMA with Eq::{not_equal, equal}
