/-
`beatmap::objects::sort_nested` (Rust) refines `sortNested` (mods proof agent; abs-style): `list_sort` on
start times, transported to the spec objects by the introsort naturality lemmas (`dnt_list`).
-/
import OsuProofs.Auto.Base
import OsuProofs.Beatmap.DotNetIntro
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

def onNd : beatmap.objects.NestedObject :=
  { kind := .Head, start_time := (default : NestedObject).startTime,
    position := ⟨(default : NestedObject).position.x, (default : NestedObject).position.y⟩, stack_height := 0#i32,
    scale := (default : NestedObject).scale, time_preempt := (default : NestedObject).timePreempt,
    time_fade_in := (default : NestedObject).timeFadeIn, hit_windows := .Empty,
    path_progress := (default : NestedObject).pathProgress, span_index := 0#i32,
    span_start_time := (default : NestedObject).spanStartTime, repeat_index := 0#i32,
    spinner_duration := (default : NestedObject).spinnerDuration,
    classic_slider_behaviour := false, kiai := false, strict_tracking_tail := false }

theorem on_nd_abs : (abs onNd : NestedObject) = default := by rfl


/-- `nestedHitObjects.Sort(by StartTime)` = `List<T>.Sort` (introsort) on the nested objects -/
theorem beatmap.objects.sort_nested_refines (ns : alloc.vec.Vec beatmap.objects.NestedObject)
    (hN : ns.val.length < 2^31) :
    ∃ r, beatmap.objects.sort_nested ns = ok r ∧ sortNested (abs ns) = (abs r : Array NestedObject) ∧
      r.val.length = ns.val.length := by
  letI : Inhabited beatmap.objects.NestedObject := ⟨onNd⟩
  obtain ⟨r, hr, hrv, hrl⟩ := beatmap.dotnet.list_sort_refines beatmap.objects.NestedObject.Insts.CoreCloneClone
    (fun x => rfl) beatmap.objects.NestedObject.Insts.Osu_eval_coreBeatmapDotnetSortCmp
    (fun x y => compareF64 x.start_time y.start_time)
    (fun x y => beatmap.dotnet.compare_f64_refines x.start_time y.start_time)
    (fun x => dns_cmp_refl x.start_time) ns hN
  refine ⟨r, hr, ?_, hrl⟩
  have e1 : (abs ns : Array NestedObject) = ns.val.toArray.map abs := by simp [abs]
  have e2 : (abs r : Array NestedObject) = r.val.toArray.map abs := by simp [abs]
  rw [e1, e2, hrv]
  unfold sortNested
  exact dnt_list (abs : beatmap.objects.NestedObject → NestedObject) on_nd_abs _ _ (fun x y => rfl) _

end OsuProofs
