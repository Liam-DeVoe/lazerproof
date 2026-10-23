import OsuModel.Beatmap.ModSettings
/-! Exhaustive check of the `Settings.assignFuel` bound (D27): over every reachable WU/WD rate state, the
nested `ValueChanged` chain of `Settings.assign` needs at most 2 levels of fuel, i.e. `toMod` with fuel 2
equals `toMod` with fuel 64 (and fuel 1 differs somewhere, so 2 is tight).
Run: `cd model && lake env lean --run scripts/assign_depth.lean`. -/
open OsuModel.Beatmap OsuModel.Beatmap.Settings

/-- `Settings.toMod` with the fuel of `assign` as a parameter (same body otherwise). -/
def toModF (fuel : Nat) (acronym : String) (settings : List (String × JsonVal)) : Array (String × SettingValue) :=
  match table acronym with
  | none => #[]
  | some defs => Id.run do
    let mut vals : Array (String × SettingValue) := (defs.map fun d => (d.key, d.default)).toArray
    for d in defs do
      match (settings.reverse.find? (·.1 == d.key)).map (·.2) with
      | none => pure ()
      | some j =>
        let old := ((vals.find? (·.1 == d.key)).map (·.2)).getD d.default
        match parse d.type old j with
        | some v => vals := assignF fuel acronym defs vals d.key v
        | none => pure ()
    return vals

def fp (vals : Array (String × SettingValue)) : List (String × String) :=
  vals.toList.map fun (k, v) => (k, match v with | .double x => toString x.toBits | v => toString (repr v))

def specials : List Float := [0.0/0.0, 1.0/0.0, -1.0/0.0, -0.0, 1e300, -1e300, 5e-324]

def main : IO UInt32 := do
  -- fine input grid: k * 0.0005 for k in [-200, 5000] plus specials and integers
  let fine : List Float := (List.range 5201).map (fun k => (k.toFloat - 200) * 0.0005) ++ specials
  let mut bad := 0
  let mut needs2 := 0
  let mut total := 0
  for acr in ["WU", "WD"] do
    let some defs := table acr | return 1
    let outs (key : String) : Array Float := Id.run do
      let some d := defs.find? (·.key == key) | return #[]
      let mut seen : Array Float := #[]
      for x in fine do
        match parse d.type d.default (.double x) with
        | some (.double y) => if !(seen.any (·.toBits == y.toBits)) then seen := seen.push y
        | _ => pure ()
      return seen
    let si := outs "initial_rate"
    let sf := outs "final_rate"
    IO.println s!"{acr}: {si.size} initial values, {sf.size} final values"
    let ini : List (Option Float) := none :: (si ++ specials.toArray).toList.map some
    let fin : List (Option Float) := none :: (sf ++ specials.toArray).toList.map some
    for a in ini do
      for b in fin do
        let st := (match a with | some x => [("initial_rate", JsonVal.double x)] | none => []) ++
                  (match b with | some x => [("final_rate", JsonVal.double x)] | none => [])
        total := total + 1
        let r64 := fp (toModF 64 acr st)
        if fp (toModF 2 acr st) != r64 then
          bad := bad + 1
          if bad ≤ 5 then IO.println s!"fuel 2 insufficient: {acr} {repr a} {repr b}"
        if fp (toModF 1 acr st) != r64 then needs2 := needs2 + 1
  IO.println s!"checked {total} states: fuel 2 insufficient {bad}, fuel 1 insufficient {needs2}"
  return (if bad == 0 then 0 else 1)
