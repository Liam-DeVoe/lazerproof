import OsuModel.Beatmap

/-!
# `bmdump`: the Lean side of the beatmap differential test

* `bmdump FILE.osu` — print the canonical dump of the playable beatmap (NoMod).
* `bmdump batch LIST OUTDIR` — LIST lines are `<osu path>\t<out name>`; writes OUTDIR/<out name>.
* `bmdump sorttest` — read `bmtest sorttest` output on stdin and check `listSort` against .NET.
-/

open OsuModel.Beatmap
open OsuModel.Net

/-! ## Minimal JSON reader for `APIMod` lists, classifying numbers like Newtonsoft.Json
(`JsonTextReader.ParseNumber`): a number containing `.`, `e` or `E` is a `double`
(`double.Parse`, invariant), otherwise a `long` (or `BigInteger` beyond the `long` range). -/
namespace Json

inductive V where
  | num (text : String)
  | str (s : String)
  | bool (b : Bool)
  | null
  | arr (xs : List V)
  | obj (kvs : List (String × V))
deriving Inhabited

abbrev P := StateT (List Char) (Except String)

partial def ws : P Unit := do
  match (← get) with
  | c :: cs => if c == ' ' || c == '\n' || c == '\t' || c == '\r' then set cs; ws else pure ()
  | [] => pure ()

def expect (c : Char) : P Unit := do
  ws
  match (← get) with
  | d :: cs => if c == d then set cs else throw s!"expected {c}"
  | [] => throw s!"expected {c}"

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10 else c.toNat - 'A'.toNat + 10

partial def strBody (acc : List Char) : P String := do
  match (← get) with
  | '"' :: cs => set cs; return String.ofList acc.reverse
  | '\\' :: e :: cs =>
    set cs
    match e with
    | 'n' => strBody ('\n' :: acc) | 't' => strBody ('\t' :: acc) | 'r' => strBody ('\r' :: acc)
    | 'b' => strBody ('\x08' :: acc) | 'f' => strBody ('\x0c' :: acc)
    | 'u' =>
      match (← get) with
      | a :: b :: c :: d :: rest =>
        set rest
        strBody (Char.ofNat (((hexVal a * 16 + hexVal b) * 16 + hexVal c) * 16 + hexVal d) :: acc)
      | _ => throw "bad \\u"
    | c => strBody (c :: acc)
  | c :: cs => set cs; strBody (c :: acc)
  | [] => throw "unterminated string"

partial def value : P V := do
  ws
  match (← get) with
  | '"' :: cs => set cs; return .str (← strBody [])
  | '[' :: cs =>
    set cs; ws
    if (← get).head? == some ']' then modify List.tail; return .arr []
    let mut xs := #[]
    repeat
      xs := xs.push (← value); ws
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
      kvs := kvs.push (k, ← value); ws
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

end Json

def dumpFile (path : String) (modsJson : Option String := none) : IO (Array String) := do
  let bytes ← IO.FS.readBinFile path
  let mods ← match modsJson with
    | none => pure []
    | some j => match Json.parseMods j with
      | .ok ms => pure ms
      | .error e => throw (IO.userError s!"bad mods json: {e}")
  return Dump.dumpLoad (load bytes (mods.map ModConfig.allHooks)) mods

def writeLines (h : IO.FS.Stream) (ls : Array String) : IO Unit := do
  for l in ls do
    h.putStr l
    h.putStr "\n"

def sortTest : IO UInt32 := do
  let stdin ← IO.getStdin
  let mut n := 0
  let mut bad := 0
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let line : String := trimEnd line
    match line.splitOn " " with
    | [ks, perm] =>
      let keys : Array Nat := if ks.isEmpty then #[] else (ks.splitOn ",").toArray.map String.toNat!
      let expected := if perm.isEmpty then "" else perm
      let arr : Array (Nat × Nat) := keys.mapIdx fun i k => (k, i)
      let sorted := listSort (fun a b => if a.1 < b.1 then -1 else if a.1 > b.1 then 1 else 0) arr
      let got := ",".intercalate (sorted.toList.map (fun x => toString x.2))
      n := n + 1
      if got != expected then
        bad := bad + 1
        if bad ≤ 5 then IO.println s!"MISMATCH keys={ks}\n  .NET {expected}\n  Lean {got}"
    | [perm] =>
      -- empty key list prints as " " + perm; handled by splitOn giving ["", perm]
      n := n + 1
      if perm != "" then bad := bad + 1
    | _ => pure ()
  IO.println s!"sorttest: {n} arrays, {bad} mismatches"
  return if bad == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["sorttest"] => sortTest
  | ["batch", list, outDir] =>
    IO.FS.createDirAll outDir
    let lines ← IO.FS.lines list
    for l in lines do
      match l.splitOn "\t" with
      | p :: name :: rest =>
        let out ← dumpFile p rest.head?
        IO.FS.withFile (outDir ++ "/" ++ name) .write fun h => writeLines (IO.FS.Stream.ofHandle h) out
      | _ => pure ()
    return 0
  | [file] =>
    let out ← dumpFile file
    writeLines (← IO.getStdout) out
    return 0
  | [file, mods] =>
    let out ← dumpFile file (some mods)
    writeLines (← IO.getStdout) out
    return 0
  | _ =>
    IO.eprintln "usage: bmdump FILE.osu | bmdump batch LIST OUTDIR | bmdump sorttest"
    return 2
