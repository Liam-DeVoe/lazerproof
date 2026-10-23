//! Port of `model/OsuModel/Beatmap/*` (lazer's osu! beatmap pipeline: `.osu` -> playable
//! beatmap), function by function; see impl/STYLE.md. Entry point: `playable::load`.
//! Submodules mirror the Lean files of the same (snake_case) name.

pub mod chartable;
pub mod names;
pub mod dotnet;
pub mod vector2;
pub mod text;
pub mod control_points;
pub mod types;
pub mod path_approximator;
pub mod slider_path;
pub mod errors;
pub mod hit_object_parser;
pub mod decoder;
pub mod slider_event_generator;
pub mod objects;
pub mod processor;
pub mod playable;
pub mod mod_settings;
pub mod mods;
pub mod mod_random;
pub mod mod_target_practice;
/// Canonical text dump (test harness; plain Rust, excluded from Charon).
pub mod dump;
