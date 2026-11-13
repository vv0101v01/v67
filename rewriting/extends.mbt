///|
pub extend Term with Eq::{equal, not_equal}

///|
pub extend Term with Hash::{hash, hash_combine}

///|
pub extend Term with Debug::{to_repr}

///|
pub extend Rule with Eq::{equal, not_equal}

///|
pub extend Rule with Debug::{to_repr}

///|
pub extend CriticalPair with Eq::{equal, not_equal}

///|
pub extend CriticalPair with Debug::{to_repr}

///|
pub extend ConfluenceReport with Eq::{equal, not_equal}

///|
pub extend ConfluenceReport with Debug::{to_repr}

///|
pub extend NormalForm with Eq::{equal, not_equal}

///|
pub extend NormalForm with Debug::{to_repr}

///|
pub extend CompletionResult with Debug::{to_repr}
