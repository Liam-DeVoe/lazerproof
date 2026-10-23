//! Port of `OsuModel/Beatmap/Processor.lean` (`OsuBeatmapProcessor`/`BeatmapProcessor`): combo
//! information and stacking.
use super::objects::{end_position, end_time, is_circle, is_slider, is_spinner, set_stack_height, ObjectKind, OsuHitObject};
use super::slider_path;
use super::vector2::{self as v, Vec2};
use crate::float::F32;
use alloc::vec::Vec;

/// `STACK_DISTANCE = 3`
pub const STACK_DISTANCE: F32 = F32::from_bits(0x4040_0000);

/// `OsuHitObject.UpdateComboInformation(lastObj)` applied to `objs[i]` (and `objs[i-1]`'s
/// `LastInCombo`); spec `OsuBeatmapProcessor.updateComboInformation`
pub fn update_combo_information(objs: &mut Vec<OsuHitObject>, i: usize) {
    let has_last = i > 0;
    let (index, index_with_offsets, in_current_combo, last_is_spinner) = if has_last {
        let l = &objs[i - 1];
        (l.combo_index, l.combo_index_with_offsets, l.index_in_current_combo.wrapping_add(1), is_spinner(l))
    } else {
        (0, 0, 0, false)
    };
    if !is_spinner(&objs[i]) && (objs[i].new_combo || !has_last || last_is_spinner) {
        if has_last {
            objs[i - 1].last_in_combo = true;
        }
        let co = objs[i].combo_offset;
        objs[i].combo_index = index.wrapping_add(1);
        objs[i].combo_index_with_offsets = index_with_offsets.wrapping_add(co).wrapping_add(1);
        objs[i].index_in_current_combo = 0;
    } else {
        objs[i].combo_index = index;
        objs[i].combo_index_with_offsets = index_with_offsets;
        objs[i].index_in_current_combo = in_current_combo;
    }
}

/// `OsuBeatmapProcessor.PreProcess()` + `BeatmapProcessor.PreProcess()`; spec `preProcess`
pub fn pre_process(objs: &mut Vec<OsuHitObject>) {
    let mut i = 0;
    while i < objs.len() {
        if !is_spinner(&objs[i]) && (i == 0 || is_spinner(&objs[i - 1])) {
            objs[i].new_combo = true;
        }
        i = i + 1;
    }
    let mut j = 0;
    while j < objs.len() {
        update_combo_information(objs, j);
        j = j + 1;
    }
}

/// `(int)TimePreempt * StackLeniency`; spec `stackThreshold`
pub fn stack_threshold(stack_leniency: F32, h: &OsuHitObject) -> F32 {
    F32::from_i64(h.time_preempt.to_i32_sat() as i64).mul(stack_leniency)
}

/// `Vector2Extensions.Distance(a, b) < STACK_DISTANCE`; spec `near`
pub fn near(a: Vec2, b: Vec2) -> bool {
    v::distance_fw(a, b).lt(STACK_DISTANCE)
}

/// inner loop of `applyStacking` for a circle `objectI` (index `i`); returns the new
/// `extendedStartIndex`
pub fn stack_circle(sl: F32, hos: &mut Vec<OsuHitObject>, i: usize, extended_start_index0: usize) -> usize {
    let n = hos.len();
    let mut extended_start_index = extended_start_index0;
    let mut object_i_idx = i;
    let threshold = stack_threshold(sl, &hos[i]);
    let mut nn: i64 = i as i64;
    let mut go = true;
    let mut fuel = 0;
    while go && fuel < n + 1 {
        fuel = fuel + 1;
        nn = nn - 1;
        if nn < 0 {
            go = false;
        } else {
            let k = nn as usize;
            if is_spinner(&hos[k]) {
                // continue
            } else {
                let et = end_time(&hos[k]);
                let si = hos[object_i_idx].start_time.to_i32_sat();
                if threshold.lt(F32::from_i64(si.wrapping_sub(et.to_i32_sat()) as i64)) {
                    go = false;
                } else {
                    if k < extended_start_index {
                        set_stack_height(&mut hos[k], 0);
                        extended_start_index = k;
                    }
                    let n_end = end_position(&hos[k]);
                    let i_pos = hos[object_i_idx].position;
                    if is_slider(&hos[k]) && near(n_end, i_pos) {
                        let offset: i32 = hos[object_i_idx].stack_height.wrapping_sub(hos[k].stack_height).wrapping_add(1);
                        let mut j = k + 1;
                        while j < i + 1 {
                            if near(n_end, hos[j].position) {
                                let sh = hos[j].stack_height.wrapping_sub(offset);
                                set_stack_height(&mut hos[j], sh);
                            }
                            j = j + 1;
                        }
                        go = false;
                    } else if near(hos[k].position, i_pos) {
                        let sh = hos[object_i_idx].stack_height.wrapping_add(1);
                        set_stack_height(&mut hos[k], sh);
                        object_i_idx = k;
                    }
                }
            }
        }
    }
    extended_start_index
}

/// inner loop of `applyStacking` for a slider `objectI` (index `i`)
pub fn stack_slider(sl: F32, hos: &mut Vec<OsuHitObject>, i: usize, start_index: usize) {
    let n = hos.len();
    let threshold = stack_threshold(sl, &hos[i]);
    let mut object_i_idx = i;
    let mut nn: i64 = i as i64;
    let mut go = true;
    let mut fuel = 0;
    while go && fuel < n + 1 {
        fuel = fuel + 1;
        nn = nn - 1;
        if nn < start_index as i64 {
            go = false;
        } else {
            let k = nn as usize;
            if is_spinner(&hos[k]) {
                // continue
            } else if threshold.to_f64().lt(hos[object_i_idx].start_time.sub(hos[k].start_time)) {
                go = false;
            } else if near(end_position(&hos[k]), hos[object_i_idx].position) {
                let sh = hos[object_i_idx].stack_height.wrapping_add(1);
                set_stack_height(&mut hos[k], sh);
                object_i_idx = k;
            }
        }
    }
}

/// `applyStacking(beatmap, hitObjects, 0, n - 1)` (version >= 6); spec `applyStacking`
pub fn apply_stacking(sl: F32, hos: &mut Vec<OsuHitObject>) {
    let n = hos.len();
    let start_index = 0;
    let end_index = n - 1;
    let extended_end_index = end_index;
    let mut extended_start_index = start_index;
    let mut i = extended_end_index;
    let mut fuel = 0;
    while fuel < n && i > start_index {
        fuel = fuel + 1;
        if hos[i].stack_height != 0 || is_spinner(&hos[i]) {
            // skip
        } else if is_circle(&hos[i]) {
            extended_start_index = stack_circle(sl, hos, i, extended_start_index);
        } else if is_slider(&hos[i]) {
            stack_slider(sl, hos, i, start_index);
        }
        i = i - 1;
    }
}

/// `applyStackingOld(beatmap, hitObjects)` (version < 6); spec `applyStackingOld`
pub fn apply_stacking_old(sl: F32, hos: &mut Vec<OsuHitObject>) {
    let n = hos.len();
    let mut i = 0;
    while i < n {
        if hos[i].stack_height != 0 && !is_slider(&hos[i]) {
            // continue
        } else {
            let mut start_time = end_time(&hos[i]);
            let mut slider_stack: i32 = 0;
            let mut j = i + 1;
            let mut go = true;
            while go && j < n {
                let threshold = stack_threshold(sl, &hos[i]);
                if start_time.lt(hos[j].start_time.sub(threshold.to_f64())) {
                    go = false;
                } else {
                    let cur_pos = hos[i].position;
                    let position2 = match &hos[i].kind {
                        ObjectKind::Slider(s) => v::add(cur_pos, slider_path::position_at(&s.path, F64_ONE)),
                        _ => cur_pos,
                    };
                    if near(hos[j].position, cur_pos) {
                        let sh = hos[i].stack_height.wrapping_add(1);
                        set_stack_height(&mut hos[i], sh);
                        start_time = hos[j].start_time;
                    } else if near(hos[j].position, position2) {
                        slider_stack = slider_stack.wrapping_add(1);
                        let sh = hos[j].stack_height.wrapping_sub(slider_stack);
                        set_stack_height(&mut hos[j], sh);
                        start_time = hos[j].start_time;
                    }
                    j = j + 1;
                }
            }
        }
        i = i + 1;
    }
}

const F64_ONE: crate::float::F64 = crate::float::F64::from_bits(0x3FF0_0000_0000_0000);

/// `OsuBeatmapProcessor.ApplyStacking(beatmap)`; spec `applyStackingAll`
pub fn apply_stacking_all(format_version: i32, sl: F32, hos: &mut Vec<OsuHitObject>) {
    if hos.len() == 0 {
        return;
    }
    let mut i = 0;
    while i < hos.len() {
        set_stack_height(&mut hos[i], 0);
        i = i + 1;
    }
    if format_version >= 6 {
        apply_stacking(sl, hos);
    } else {
        apply_stacking_old(sl, hos);
    }
}
