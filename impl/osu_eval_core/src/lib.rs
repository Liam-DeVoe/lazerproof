//! osu! lazer evaluator core, written in the Aeneas-translatable subset (docs/proof-poc.md
//! "Rust style rules"). Each function mirrors one `OsuModel` spec function and is proven to
//! refine it in `proofs/OsuProofs/*.lean`.

extern crate alloc;

pub mod float;
#[macro_use]
pub mod net;
pub mod hit_windows;
pub mod slider;
pub mod schedule;
pub mod beatmap;
pub mod sim;
pub mod replay;
pub mod lzma;
pub mod eval;
