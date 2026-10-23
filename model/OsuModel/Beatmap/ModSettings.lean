import OsuModel.Beatmap.DotNet

/-!
# Mod settings: `APIMod.ToMod` (`osu.Game/Online/API/APIMod.cs:47-77`)

A mod in a score / multiplayer room / replay is an `APIMod`: an acronym plus a
`Dictionary<string, object>` of settings as Newtonsoft deserialises JSON (`JsonVal`).
`APIMod.ToMod(ruleset)`:

1. `ruleset.CreateModFromAcronym(acronym)`, or `UnknownMod` (no effect anywhere in the pipeline);
2. for every `[SettingSource]` property in `GetSettingsSourceProperties()` order
   (`SettingSourceAttribute.cs:253-274`) whose snake_case name is a key of the dictionary:
   `Mod.CopyAdjustedSetting(bindable, value)` → `IParseable.Parse(value, InvariantCulture)`
   (`Mod.cs:223-238`); an exception is logged and the setting keeps its current value.

`Bindable<T>.Parse` (`osu.Framework/Bindables/Bindable.cs:252-302`, `BindableBool.cs:15-25`) then
assigns `Value`, which runs the bindable's setter: clamping/precision for `BindableNumber`
(`BindableNumber.cs:69-90`, `RangeConstrainedBindable.cs:256`), extended-range clamping for
`DifficultyBindable` (`DifficultyBindable.cs:114-130`), and the `ValueChanged` callbacks the mod
registered (only Wind Up / Wind Down cross-constrain settings, `ModWindUp.cs:38-51`,
`ModWindDown.cs:38-51`).

The setting tables below were checked against the live mod instances (`bmtest modinfo`).

Source status: the lazer/framework parts are transcribed from the checkouts (cited inline). The BCL
conversions (`Convert.ToInt32(double/long)`, `bool.Parse`, `object.ToString()` for the enum path,
Newtonsoft number classification) have no checkout here; they follow the .NET 10 / Newtonsoft
behaviour and are covered only by the randomised differential test (`bmtest/modgen.py` generates
strings, bools, nulls, ints, off-grid/out-of-range doubles and huge integers for every setting).
-/

namespace OsuModel.Beatmap
open OsuModel.Net

/-- A settings value as produced by Newtonsoft.Json for `Dictionary<string, object>`:
JSON integers in `long` range → `long`, larger ones → `BigInteger`, other numbers → `double`
(`double.Parse`, invariant), `true/false` → `bool`, strings, `null`. -/
inductive JsonVal where
  | long (v : Int)
  | big
  | double (v : F64)
  | bool (b : Bool)
  | str (s : String)
  | null
deriving Inhabited, Repr

/-- The bindable types used by osu! mod settings. -/
inductive SettingType where
  /-- `BindableBool` (`bindableBool = true`: accepts the strings "1"/"0") or plain `Bindable<bool>` -/
  | bool (bindableBool : Bool)
  /-- `BindableInt` (precision 1: the setter is a clamp) -/
  | int (min max : Int32)
  /-- `BindableDouble` -/
  | double (min max precision : F64)
  /-- `BindableFloat` -/
  | float (min max precision : F32)
  /-- `Bindable<TEnum>` (int-backed); member names and values -/
  | enum (names : List (String × Int32))
  /-- `Bindable<int?>` (seeds) -/
  | nullableInt
  /-- `DifficultyBindable : Bindable<float?>` -/
  | difficulty (min max : F32) (extMin extMax : Option F32)
deriving Inhabited

/-- A stored setting value. -/
inductive SettingValue where
  | bool (b : Bool)
  | int (v : Int32)
  | double (v : F64)
  | float (v : F32)
  | enum (v : Int32)
  | optInt (v : Option Int32)
  | optFloat (v : Option F32)
deriving Inhabited, Repr, BEq

structure SettingDef where
  /-- snake_case JSON key (`property.Name.ToSnakeCase()`) -/
  key : String
  type : SettingType
  /-- the value the constructor leaves in the bindable (after the initialiser's setter runs) -/
  default : SettingValue

/-- A decoded mod: the acronym (`UnknownMod` keeps `known = false`) and its settings in
`GetSettingsSourceProperties()` order. -/
structure ModConfig where
  acronym : String
  known : Bool := true
  settings : Array (String × SettingValue) := #[]
deriving Inhabited, Repr

namespace ModConfig
def get? (m : ModConfig) (key : String) : Option SettingValue := (m.settings.find? (·.1 == key)).map (·.2)
def getBool (m : ModConfig) (key : String) : Bool :=
  match m.get? key with | some (.bool b) => b | _ => false
def getInt (m : ModConfig) (key : String) : Int32 :=
  match m.get? key with | some (.int v) | some (.enum v) => v | _ => 0
def getDouble (m : ModConfig) (key : String) : F64 :=
  match m.get? key with | some (.double v) => v | _ => 0
def getFloat (m : ModConfig) (key : String) : F32 :=
  match m.get? key with | some (.float v) => v | _ => 0
def getOptInt (m : ModConfig) (key : String) : Option Int32 :=
  match m.get? key with | some (.optInt v) => v | _ => none
def getOptFloat (m : ModConfig) (key : String) : Option F32 :=
  match m.get? key with | some (.optFloat v) => v | _ => none
end ModConfig

namespace Settings

/-! ## `Convert.ChangeType(input, T, InvariantCulture)` -/

/-- `Convert.ToInt32(double)` (`Convert.cs`): round half to even, `OverflowException` outside
`[-2147483648.5, 2147483647.5)` (NaN included). -/
def convertToInt32 (v : F64) : Except NetExn Int32 :=
  if (0 : F64) ≤ v then
    if v < 2147483647.5 then
      let r := F64.toInt32 v
      let dif := v - F64.ofInt32 r
      .ok (if (0.5 : F64) < dif || (dif == 0.5 && r &&& 1 != 0) then r + 1 else r)
    else .error .overflow
  else if (-2147483648.5 : F64) ≤ v then
    let r := F64.toInt32 v
    let dif := v - F64.ofInt32 r
    .ok (if dif < -0.5 || (dif == -0.5 && r &&& 1 != 0) then r - 1 else r)
  else .error .overflow

/-- `Convert.ToInt32(long)`: overflow-checked. -/
def longToInt32 (v : Int) : Except NetExn Int32 :=
  if -2147483648 ≤ v && v ≤ 2147483647 then .ok (Int32.ofInt v) else .error .overflow

/-- `bool.Parse(string)`: trims white space and NUL at both ends, case-insensitive `True`/`False`. -/
def boolParse (s : String) : Except NetExn Bool :=
  let isTrim (c : Char) := isWhiteSpace c || c == '\x00'
  let t := String.ofList ((s.toList.dropWhile isTrim).reverse.dropWhile isTrim).reverse
  let l := t.toList.map Char.toLower
  if l == "true".toList then .ok true else if l == "false".toList then .ok false else .error .format

def toInt32 : JsonVal → Except NetExn Int32
  | .long v => longToInt32 v
  | .double v => convertToInt32 v
  | .bool b => .ok (if b then 1 else 0)
  | .str s => intParse s
  | .big | .null => .error .argument

def toF64 : JsonVal → Except NetExn F64
  | .long v => .ok (F64.ofInt v)
  | .double v => .ok v
  | .bool b => .ok (if b then 1 else 0)
  | .str s => doubleParse s
  | .big | .null => .error .argument

def toF32 : JsonVal → Except NetExn F32
  | .long v => .ok (F32.ofInt v)
  | .double v => .ok (F64.toF32 v)
  | .bool b => .ok (if b then 1 else 0)
  | .str s => floatParse s
  | .big | .null => .error .argument

def toBool (bindableBool : Bool) : JsonVal → Except NetExn Bool
  | .bool b => .ok b
  | .str "1" => if bindableBool then .ok true else boolParse "1"
  | .str "0" => if bindableBool then .ok false else boolParse "0"
  | .str s => boolParse s
  | .long v => .ok (v != 0)
  | .double v => .ok (!(v == 0))
  | .big | .null => .error .argument

/-- `input.ToString()` as used by the enum branch of `Bindable.Parse`, only as far as it can
lead to a successful `Enum.Parse`: integers print in decimal; a `double` prints as an integer
literal only when it is integral and below 1e15 in magnitude (otherwise the shortest round-trip
form contains `.`/`E` or is `NaN`/`Infinity`, none of which parse). -/
def enumString : JsonVal → Option String
  | .long v => some (toString v)
  | .double v =>
    if !v.isNaN && !v.isInf && F64.truncate v == v && F64.abs v < 1e15 then
      let i := (F64.toInt64 v).toInt
      some (if i == 0 && v.toBits >>> 63 == 1 then "-0" else toString i)
    else none
  | .bool b => some (if b then "True" else "False")
  | .str s => some s
  | .big | .null => none

/-! ## Setters -/

open Framework.Bindable in
/-- `BindableNumber<double>.Value = v` on a bindable currently holding `old`
(`OsuModel.Net.Framework.Bindable`: clamp, `decimal` precision snap, clamp, then the
`Bindable.Value` equality check, which keeps the old bits when `Equals(old, new)`).
`none` = the setter threw. -/
def setDouble (min max precision : F64) (old v : F64) : Option F64 :=
  match (BD.setValue { value := old, minV := min, maxV := max, prec := precision } v) with
  | .ok s => some s.value
  | .error _ => none

open Framework.Bindable in
/-- `BindableNumber<float>.Value = v` (see `setDouble`). -/
def setFloat (min max precision : F32) (old v : F32) : Option F32 :=
  match (BF.setValue { value := old, minV := min, maxV := max, prec := precision } v) with
  | .ok s => some s.value
  | .error _ => none

open Framework.Bindable in
/-- The value of `new BindableDouble(d) { MinValue, MaxValue, Precision }` (or with `Precision`
first when `precisionFirst`). -/
def initDouble (d min max precision : F64) (precisionFirst := false) : F64 :=
  let r := if precisionFirst then do
      let s ← BD.create d; let s ← s.setPrecision precision; let s ← s.setMin min; s.setMax max
    else BD.init d min max precision
  match r with | .ok s => s.value | .error _ => d

open Framework.Bindable in
def initFloat (d min max precision : F32) (precisionFirst := false) : F32 :=
  let r := if precisionFirst then do
      let s ← BF.create d; let s ← s.setPrecision precision; let s ← s.setMin min; s.setMax max
    else BF.init d min max precision
  match r with | .ok s => s.value | .error _ => d

/-- `BindableInt` setter: precision 1 makes the decimal snap the identity; clamp. -/
def setInt (min max : Int32) (v : Int32) : Int32 :=
  if v < min then min else if max < v then max else v

/-- `DifficultyBindable.Value` setter (`G/Rulesets/Mods/DifficultyBindable.cs:114-130`) for a non-null value: the stored value is clamped to the
extended range whatever `ExtendedLimits` is (see `docs/mods/difficulty-rate-fail.md` §2.4). -/
def setDifficulty (min max : F32) (extMin extMax : Option F32) (v : F32) : F32 :=
  -- CurrentNumber.MinValue = Clamp(MathF.Min(CurrentNumber.MinValue, v), ExtendedMinValue ?? MinValue, MinValue)
  -- (CurrentNumber starts at [MinValue, MaxValue] and is only touched by this setter and updateExtents)
  let lo := extMin.getD min
  let hi := extMax.getD max
  let cnMin := F32.clamp (F32.min min v) lo min
  let cnMax := F32.clamp (F32.max max v) max hi
  match cnMin, cnMax with
  | .ok a, .ok b => match F32.clamp v a b with | .ok r => r | .error _ => v
  | _, _ => v

/-- `Bindable<T>.Parse(input)` followed by the setter, on a bindable holding `old`.
`none` = exception (value unchanged). -/
def parse (t : SettingType) (old : SettingValue) (j : JsonVal) : Option SettingValue :=
  match t with
  | .bool bb => match toBool bb j with | .ok b => some (.bool b) | .error _ => none
  | .int mn mx => match toInt32 j with | .ok v => some (.int (setInt mn mx v)) | .error _ => none
  | .double mn mx p =>
    let o : F64 := match old with | .double x => x | _ => 0
    match toF64 j with | .ok v => (setDouble mn mx p o v).map SettingValue.double | .error _ => none
  | .float mn mx p =>
    let o : F32 := match old with | .float x => x | _ => 0
    match toF32 j with | .ok v => (setFloat mn mx p o v).map SettingValue.float | .error _ => none
  | .enum names => match enumString j with
    | some s => (enumTryParse names s).map SettingValue.enum
    | none => none
  | .nullableInt => match j with
    | .null | .str "" => some (.optInt none)
    | _ => match toInt32 j with | .ok v => some (.optInt (some v)) | .error _ => none
  | .difficulty mn mx emn emx => match j with
    | .null | .str "" => some (.optFloat none)
    | _ => match toF32 j with
      | .ok v => some (.optFloat (some (setDifficulty mn mx emn emx v)))
      | .error _ => none

/-! ## Setting tables (`GetSettingsSourceProperties()` order) -/

def sBool (key : String) (d : Bool) (bindableBool := true) : SettingDef := ⟨key, .bool bindableBool, .bool d⟩
def sInt (key : String) (d mn mx : Int32) : SettingDef := ⟨key, .int mn mx, .int (setInt mn mx d)⟩
def sDouble (key : String) (d mn mx p : F64) : SettingDef := ⟨key, .double mn mx p, .double (initDouble d mn mx p)⟩
def sFloat (key : String) (d mn mx p : F32) (precisionFirst := false) : SettingDef :=
  ⟨key, .float mn mx p, .float (initFloat d mn mx p precisionFirst)⟩
def sEnum (key : String) (names : List (String × Int32)) : SettingDef := ⟨key, .enum names, .enum 0⟩
def sSeed : SettingDef := ⟨"seed", .nullableInt, .optInt none⟩
def sDiff (key : String) (extMin : Option F32) : SettingDef := ⟨key, .difficulty 0 10 extMin (some 11), .optFloat none⟩

def rateDT : List SettingDef := [sDouble "speed_change" 1.5 1.01 2 0.01, sBool "adjust_pitch" false]
def rateHT : List SettingDef := [sDouble "speed_change" 0.75 0.5 0.99 0.01, sBool "adjust_pitch" false]

/-- `(float)0.1f` widened: `BindableDouble` initialisers with float literals (Wiggle). -/
def f32d (x : F32) : F64 := F32.toF64 x

/-- The settings of every osu! mod (`OsuRuleset.GetModsFor`), by acronym. -/
def table : String → Option (List SettingDef)
  | "EZ" => some [sInt "retries" 2 0 10]
  | "NF" => some []
  | "HT" => some rateHT
  | "DC" => some [sDouble "speed_change" 0.75 0.5 0.99 0.01]
  | "HR" => some []
  | "SD" => some [sBool "fail_on_slider_tail" false, sBool "restart" false]
  | "PF" => some [sBool "restart" true]
  | "DT" => some rateDT
  | "NC" => some [sDouble "speed_change" 1.5 1.01 2 0.01]
  | "HD" => some [sBool "only_fade_approach_circles" false]
  | "TC" => some []
  | "FL" => some [sDouble "follow_delay" 120 120 1200 120, sFloat "size_multiplier" 1 0.5 2 0.1,
                  sBool "combo_based_size" true]
  | "BL" => some []
  | "ST" => some []
  | "AC" => some [sDouble "minimum_accuracy" 0.9 0.6 0.999 0.001,
                  sEnum "accuracy_judge_mode" [("MaximumAchievable", 0), ("Standard", 1)], sBool "restart" false]
  | "TP" => some [sSeed, sBool "metronome" true]
  | "DA" => some [sDiff "circle_size" none, sDiff "approach_rate" (some (-10)), sDiff "drain_rate" none,
                  sDiff "overall_difficulty" none, sBool "extended_limits" false]
  | "CL" => some [sBool "no_slider_head_accuracy" true, sBool "classic_note_lock" true,
                  sBool "always_play_tail_sample" true, sBool "fade_hit_circle_early" true (bindableBool := false),
                  sBool "classic_health" true (bindableBool := false)]
  | "RD" => some [sFloat "angle_sharpness" 7 1 10 0.1, sSeed]
  | "MR" => some [sEnum "reflection" [("Horizontal", 0), ("Vertical", 1), ("Both", 2)]]
  | "AL" | "SG" | "AT" | "CN" | "RX" | "AP" | "SO" | "TR" | "SI" | "FR" | "BU" | "SY" | "TD" | "SV2" => some []
  | "WG" => some [sDouble "strength" 1 (f32d 0.1) (f32d 2) (f32d 0.1)]
  | "GR" => some [sFloat "start_scale" 0.5 0 0.99 0.01]
  | "DF" => some [sFloat "start_scale" 2 1 25 0.1]
  | "WU" => some [sDouble "initial_rate" 1 0.5 1.99 0.01, sDouble "final_rate" 1.5 0.51 2 0.01, sBool "adjust_pitch" true]
  | "WD" => some [sDouble "initial_rate" 1 0.51 2 0.01, sDouble "final_rate" 0.75 0.5 1.99 0.01, sBool "adjust_pitch" true]
  | "BR" => some [sDouble "spin_speed" 0.5 0.02 12 0.01,
                  sEnum "direction" [("Clockwise", 0), ("Counterclockwise", 1)]]
  | "AD" => some [sFloat "scale" 4 1.5 10 0.1 (precisionFirst := true),
                  ⟨"style", .enum [("Linear", 0), ("Gravity", 1), ("InOut1", 2), ("InOut2", 3), ("Accelerate1", 4),
                    ("Accelerate2", 5), ("Accelerate3", 6), ("Decelerate1", 7), ("Decelerate2", 8), ("Decelerate3", 9)],
                    .enum 1⟩]
  | "MU" => some [sBool "inverse_muting" false, sBool "enable_metronome" true, sInt "mute_combo_count" 100 0 500,
                  sBool "affects_hit_sounds" true]
  | "NS" => some [sInt "hidden_combo_count" 10 0 50]
  | "MG" => some [sFloat "attraction_strength" 0.5 0.05 1 0.05 (precisionFirst := true)]
  | "RP" => some [sFloat "repulsion_strength" 0.5 0.05 1 0.05 (precisionFirst := true)]
  | "AS" => some [sDouble "initial_rate" 1 0.5 2 0.01, sBool "adjust_pitch" true]
  | "DP" => some [sFloat "max_depth" 100 50 200 10 (precisionFirst := true), sBool "show_approach_circles" true]
  | "BM" => some [sInt "max_size_combo_count" 50 5 100, sFloat "max_cursor_size" 10 5 15 0.5]
  | _ => none

/-! ## `APIMod.ToMod` -/

def setValue (vals : Array (String × SettingValue)) (key : String) (v : SettingValue) : Array (String × SettingValue) :=
  vals.map fun (k, x) => if k == key then (k, v) else (k, x)

/-- The `ValueChanged` callbacks a mod registered on its settings (run only when the stored
value actually changes, `EqualityComparer<T>.Default`). Wind Up / Wind Down keep
`InitialRate < FinalRate` / `>`: `Final = new + Final.Precision` etc.
Total by explicit fuel (D27): each `fuel + 1` level is one `Bindable.Value` assignment, the nested
call (through `setD`) gets `fuel`. Fuel 0 (unreachable with `assignFuel`, see there) returns `vals`
unchanged. -/
def assignF : Nat → String → List SettingDef → Array (String × SettingValue) → String → SettingValue →
    Array (String × SettingValue)
  | 0, _, _, vals, _, _ => vals
  | fuel + 1, acr, defs, vals, key, v =>
    let old := (vals.find? (·.1 == key)).map (·.2)
    -- `Bindable.Value`: no store and no `ValueChanged` when `Equals(old, new)` (already applied
    -- by the numeric setters, which return the old bits in that case)
    let changed := match old, v with
      | some (.double a), .double b => !Framework.Bindable.equalsD a b
      | some (.float a), .float b => !Framework.Bindable.equalsF a b
      | some (.optFloat (some a)), .optFloat (some b) => !Framework.Bindable.equalsF a b
      | some a, b => !(a == b)
      | none, _ => true
    if !changed then vals else
    let vals := setValue vals key v
    let typeOf (k : String) := (defs.find? (·.key == k)).map (·.type)
    let dbl (k : String) : F64 := match (vals.find? (·.1 == k)).map (·.2) with | some (SettingValue.double x) => x | _ => 0
    let setD (k : String) (x : F64) (vals : Array (String × SettingValue)) : Array (String × SettingValue) :=
      match typeOf k with
      | some (.double mn mx p) =>
        match setDouble mn mx p (dbl k) x with
        | some y => assignF fuel acr defs vals k (.double y)
        | none => vals
      | _ => vals
    let nv : F64 := match v with | SettingValue.double x => x | _ => 0
    let fin : F64 := dbl "final_rate"
    let ini : F64 := dbl "initial_rate"
    let le (a b : F64) : Bool := a < b || a == b
    match acr, key with
    | "WU", "initial_rate" => if le fin nv then setD "final_rate" (nv + 0.01) vals else vals
    | "WU", "final_rate" => if le nv ini then setD "initial_rate" (nv - 0.01) vals else vals
    | "WD", "initial_rate" => if le nv fin then setD "final_rate" (nv - 0.01) vals else vals
    | "WD", "final_rate" => if le ini nv then setD "initial_rate" (nv + 0.01) vals else vals
    -- `InverseMuting.BindValueChanged(i => MuteComboCount.MinValue = i.NewValue ? 1 : 0, true)`
    -- (`G/Rulesets/Mods/ModMuted.cs:58`): the `MinValue` setter re-clamps the current value
    | "MU", "inverse_muting" =>
      let mn : Int32 := if v == SettingValue.bool true then 1 else 0
      match (vals.find? (·.1 == "mute_combo_count")).map (·.2) with
      | some (SettingValue.int c) => setValue vals "mute_combo_count" (SettingValue.int (setInt mn 500 c))
      | _ => vals
    | _, _ => vals

/-- Nesting bound for `assign`. The only nested assignments are the WU/WD rate callbacks, and a
chain is at most 2 assignments deep: a callback sets the other rate to the snapped `x ± 0.01`, which lies
strictly on the far side of `x`, so the second callback's condition is false (checked exhaustively
over the settings grid by `model/scripts/assign_depth.lean`, D27). 4 leaves a margin. -/
def assignFuel : Nat := 4

/-- `Bindable.Value = v` for setting `key` + the mod's `ValueChanged` callbacks (see `assignF`). -/
def assign (acr : String) (defs : List SettingDef) (vals : Array (String × SettingValue)) (key : String)
    (v : SettingValue) : Array (String × SettingValue) :=
  assignF assignFuel acr defs vals key v

/-- `APIMod.ToMod(ruleset)` for the osu! ruleset. `settings` is the JSON object in document order
(Newtonsoft keeps the last value of a duplicated key). -/
def toMod (acronym0 : String) (settings : List (String × JsonVal)) : ModConfig :=
  -- `CreateModFromAcronym`: `string.Equals(m.Acronym, acronym, OrdinalIgnoreCase)` (ASCII acronyms)
  let acronym := acronym0.map Char.toUpper
  match table acronym with
  | none => { acronym := acronym0, known := false }
  | some defs => Id.run do
    let mut vals : Array (String × SettingValue) := (defs.map fun d => (d.key, d.default)).toArray
    if settings.isEmpty then return { acronym, settings := vals }
    for d in defs do
      match (settings.reverse.find? (·.1 == d.key)).map (·.2) with
      | none => pure ()
      | some j =>
        let old := ((vals.find? (·.1 == d.key)).map (·.2)).getD d.default
        -- MU: `MuteComboCount.MinValue` follows `InverseMuting` (see `assign`)
        let ty := match acronym, d.type with
          | "MU", .int _ mx => SettingType.int (if (vals.find? (·.1 == "inverse_muting")).map (·.2) == some (.bool true) then 1 else 0) mx
          | _, t => t
        match parse ty old j with
        | some v => vals := assign acronym defs vals d.key v
        | none => pure ()
    return { acronym, settings := vals }

end Settings
end OsuModel.Beatmap
