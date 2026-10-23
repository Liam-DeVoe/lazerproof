import OsuModel.Beatmap.ModSettings

/-!
# APIMod list JSON for simtest (used by simtest; copy of the reader in `BmDump/Main.lean`, which lives in an executable
module and cannot be imported): numbers are classified like Newtonsoft.Json (`.`/`e`/`E` → double via
`double.Parse`, else long / BigInteger), then `Settings.toMod` (= `APIMod.ToMod`).
-/

open OsuModel.Beatmap
open OsuModel.Net

namespace SimJson

inductive V where
  | num (text : String)
  | str (s : String)
  | bool (b : Bool)
  | null
  | arr (xs : List V)
  | obj (kvs : List (String × V))
deriving Inhabited

abbrev P := StateT (List Char) (Except String)

/-- The input left after `ws` (structural recursion on the remaining input; total, D27). -/
def wsL : List Char → List Char
  | c :: cs => if c == ' ' || c == '\n' || c == '\t' || c == '\r' then wsL cs else c :: cs
  | [] => []

/-- Skip `' ' '\n' '\t' '\r'`. -/
def ws : P Unit := modify wsL

def expect (c : Char) : P Unit := do
  ws
  match (← get) with
  | d :: cs => if c == d then set cs else throw s!"expected {c}"
  | [] => throw s!"expected {c}"

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10 else c.toNat - 'A'.toNat + 10

/-- `strBody` as a function of the remaining input (structural recursion; total, D27): the string and the
input after the closing quote. -/
def strBodyL (acc : List Char) : List Char → Except String (String × List Char)
  | '"' :: cs => .ok (String.ofList acc.reverse, cs)
  | '\\' :: e :: cs =>
    match e with
    | 'n' => strBodyL ('\n' :: acc) cs | 't' => strBodyL ('\t' :: acc) cs | 'r' => strBodyL ('\r' :: acc) cs
    | 'b' => strBodyL ('\x08' :: acc) cs | 'f' => strBodyL ('\x0c' :: acc) cs
    | 'u' =>
      match cs with
      | a :: b :: c :: d :: rest =>
        strBodyL (Char.ofNat (((hexVal a * 16 + hexVal b) * 16 + hexVal c) * 16 + hexVal d) :: acc) rest
      | _ => .error "bad \\u"
    | c => strBodyL (c :: acc) cs
  | c :: cs => strBodyL (c :: acc) cs
  | [] => .error "unterminated string"

/-- String contents after the opening quote (consumes the closing quote). -/
def strBody (acc : List Char) : P String := fun s => strBodyL acc s

/-- `value` with explicit nesting fuel (structural recursion on `fuel`; total, D27). Each nested call
follows a consumed `[`, `{` or `,`, so with `fuel = (remaining input).length + 1` at the top the
remaining input is always shorter than the fuel and the fuel-0 branch is unreachable. -/
def valueF : Nat → P V
  | 0 => throw "internal: JSON nesting fuel exhausted"
  | fuel + 1 => do
    ws
    match (← get) with
    | '"' :: cs => set cs; return .str (← strBody [])
    | '[' :: cs =>
      set cs; ws
      if (← get).head? == some ']' then modify List.tail; return .arr []
      let mut xs := #[]
      repeat
        xs := xs.push (← valueF fuel); ws
        match (← get) with
        | ',' :: r => set r
        | ']' :: r => set r; break
        | _ => throw "bad array"
      return .arr xs.toList
    | '{' :: cs =>
      set cs; ws
      if (← get).head? == some '}' then modify List.tail; return .obj []
      let mut kvs := #[]
      repeat
        expect '"'
        let k ← strBody []
        expect ':'
        kvs := kvs.push (k, ← valueF fuel); ws
        match (← get) with
        | ',' :: r => set r
        | '}' :: r => set r; break
        | _ => throw "bad object"
      return .obj kvs.toList
    | 't' :: 'r' :: 'u' :: 'e' :: cs => set cs; return .bool true
    | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: cs => set cs; return .bool false
    | 'n' :: 'u' :: 'l' :: 'l' :: cs => set cs; return .null
    | cs =>
      let isNumChar (c : Char) := c.isDigit || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E'
      let t := cs.takeWhile isNumChar
      if t.isEmpty then throw "bad value"
      set (cs.drop t.length)
      return .num (String.ofList t)

/-- A JSON value. -/
def value : P V := do valueF ((← get).length + 1)

def toSetting : V → JsonVal
  | .num t =>
    if t.any (fun c => c == '.' || c == 'e' || c == 'E') then
      match doubleParse t with | .ok d => .double d | .error _ => .null
    else
      let n : Int := if t.startsWith "-" then -((t.drop 1).toNat! : Int) else (t.toNat! : Int)
      if -9223372036854775808 ≤ n && n ≤ 9223372036854775807 then .long n else .big
  | .str s => .str s
  | .bool b => .bool b
  | .null => .null
  | _ => .big   -- JObject/JArray values: never convertible

/-- `List<APIMod>` → decoded mod configs (`APIMod.ToMod`). -/
def parseMods (s : String) : Except String (List ModConfig) := do
  let (v, _) ← (value).run s.toList
  match v with
  | .arr xs => xs.mapM fun x => match x with
    | .obj kvs =>
      let acr := match kvs.find? (·.1 == "acronym") with | some (_, .str a) => a | _ => ""
      let settings := match kvs.find? (·.1 == "settings") with
        | some (_, .obj ss) => ss.map fun (k, v) => (k, toSetting v)
        | _ => []
      pure (Settings.toMod acr settings)
    | _ => throw "mod is not an object"
  | _ => throw "mods is not an array"

end SimJson
