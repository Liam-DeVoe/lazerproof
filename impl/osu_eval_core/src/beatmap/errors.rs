//! Error message ids of `DecodeError` (spec: the `String` messages of `DecodeM`). Ids instead of
//! `&'static str` keep borrows out of loop states (Aeneas). `text` (dump only, not translated)
//! holds the exact spec strings.

pub const M_ARGUMENTOUTOFRANGEEXCEPTION_NODESAMPLES: u32 = 0;
pub const M_ARGUMENTOUTOFRANGEEXCEPTION_GETCLOSESTHI: u32 = 1;
pub const M_BEAT_LENGTH_CANNOT_BE_NAN_IN_A_TIMING_CO: u32 = 2;
pub const M_JSON_BEATMAP_JSONBEATMAPDECODER_NOT_MODE: u32 = 3;
pub const M_RANDOM_WITHOUT_A_SEED_IS_NOT_REPRODUCIBL: u32 = 4;
pub const M_REPEAT_COUNT_IS_WAY_TOO_HIGH: u32 = 5;
pub const M_RULESET_IS_NOT_AVAILABLE_LOCALLY: u32 = 6;
pub const M_TARGET_PRACTICE_WITHOUT_A_SEED_IS_NOT_RE: u32 = 7;
pub const M_TIMESIGNATURE_NUMERATOR_MUST_BE_POSITIVE: u32 = 8;
pub const M_UNKNOWN_FILE_FORMAT_NO_CONTENT: u32 = 9;
pub const M_UNKNOWN_HIT_OBJECT_TYPE: u32 = 10;
pub const M_INDEX_0_OUT_OF_RANGE_EMPTY_STRING: u32 = 11;
pub const M_INDEX_0_OUT_OF_RANGE_NO_VERTICES: u32 = 12;
pub const M_INDEX_OUT_OF_RANGE: u32 = 13;
pub const M_UNSUPPORTED_TEXT_ENCODING_UTF_32_UNPAIRE: u32 = 14;
pub const M_SLIDER_PATH_FUEL_EXHAUSTED: u32 = 15;
pub const W_APPROACHRATE: u32 = 0;
pub const W_AUDIOLEADIN: u32 = 1;
pub const W_CIRCLESIZE: u32 = 2;
pub const W_HPDRAINRATE: u32 = 3;
pub const W_MATH_CLAMP: u32 = 4;
pub const W_MATH_CLAMP_TICKDISTANCE_0_LENGTH: u32 = 5;
pub const W_MODE: u32 = 6;
pub const W_OVERALLDIFFICULTY: u32 = 7;
pub const W_SLIDERMULTIPLIER: u32 = 8;
pub const W_SLIDERTICKRATE: u32 = 9;
pub const W_STACKLENIENCY: u32 = 10;
pub const W_ADDBANK: u32 = 11;
pub const W_BANK: u32 = 12;
pub const W_BEATLENGTH: u32 = 13;
pub const W_BREAK_END: u32 = 14;
pub const W_BREAK_START: u32 = 15;
pub const W_COORDINATE: u32 = 16;
pub const W_CUSTOMSAMPLEBANK: u32 = 17;
pub const W_EFFECTFLAGS: u32 = 18;
pub const W_FORMAT_VERSION: u32 = 19;
pub const W_HOLD_END: u32 = 20;
pub const W_LENGTH: u32 = 21;
pub const W_REPEATCOUNT: u32 = 22;
pub const W_SAMPLESET: u32 = 23;
pub const W_SAMPLEVOLUME: u32 = 24;
pub const W_SOUNDTYPE: u32 = 25;
pub const W_SPINNER_END: u32 = 26;
pub const W_STARTTIME: u32 = 27;
pub const W_TIME: u32 = 28;
pub const W_TIMESIGNATURE: u32 = 29;
pub const W_TYPE: u32 = 30;
pub const W_VOLUME: u32 = 31;

/// id -> spec text (dump only; excluded from Charon)
pub mod text {
    pub fn msg(i: u32) -> &'static str {
        match i {
            0 => "ArgumentOutOfRangeException (NodeSamples)",
            1 => "ArgumentOutOfRangeException (getClosestHitObject)",
            2 => "Beat length cannot be NaN in a timing control point",
            3 => "JSON beatmap (JsonBeatmapDecoder) not modelled",
            4 => "Random without a seed is not reproducible",
            5 => "Repeat count is way too high",
            6 => "Ruleset is not available locally.",
            7 => "Target Practice without a seed is not reproducible",
            8 => "TimeSignature numerator must be positive",
            9 => "Unknown file format (no content)",
            10 => "Unknown hit object type",
            11 => "index 0 out of range (empty string)",
            12 => "index 0 out of range (no vertices)",
            13 => "index out of range",
            14 => "unsupported text encoding (UTF-32 / unpaired surrogate)",
            15 => "slider path approximation fuel exhausted (more than 10^8 B-spline subdivisions)",
            _ => "?",
        }
    }
    pub fn what(i: u32) -> &'static str {
        match i {
            0 => "ApproachRate",
            1 => "AudioLeadIn",
            2 => "CircleSize",
            3 => "HPDrainRate",
            4 => "Math.Clamp",
            5 => "Math.Clamp(tickDistance, 0, length)",
            6 => "Mode",
            7 => "OverallDifficulty",
            8 => "SliderMultiplier",
            9 => "SliderTickRate",
            10 => "StackLeniency",
            11 => "addBank",
            12 => "bank",
            13 => "beatLength",
            14 => "break end",
            15 => "break start",
            16 => "coordinate",
            17 => "customSampleBank",
            18 => "effectFlags",
            19 => "format version",
            20 => "hold end",
            21 => "length",
            22 => "repeatCount",
            23 => "sampleSet",
            24 => "sampleVolume",
            25 => "soundType",
            26 => "spinner end",
            27 => "startTime",
            28 => "time",
            29 => "timeSignature",
            30 => "type",
            31 => "volume",
            _ => "?",
        }
    }
}
