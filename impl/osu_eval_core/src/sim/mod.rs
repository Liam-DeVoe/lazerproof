//! Port of the Lean simulation model `model/OsuModel/Sim/*` (M0-M4 core + NF/CL), function by function.
//! See docs/rust-sim-port.md (pinned Lean commit, correspondence, scope).
pub mod autogen;
pub mod basic;
pub mod err;
pub mod geometry;
pub mod mods;
pub mod netx;
pub mod playable;
pub mod schedule;
pub mod scoring;
pub mod state;
pub mod step;
pub mod transforms;
