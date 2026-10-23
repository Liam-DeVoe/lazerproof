/- check_all.sh appends this after `#check @OsuProofs.<headline>` (audit pass 2, N1): every proof-local
(`OsuProofs.*`, non-theorem) constant reachable from the headline theorem's TYPE, transitively through definition
bodies / structure fields, printed with a structural hash of its type and value, so that a definition or structure
behind the headline changing (e.g. a hypothesis structure gaining a field) changes the allowlisted block. -/
open Lean Meta in
#eval show MetaM Unit from do
  let env ← getEnv
  let root := (← IO.getEnv "OSU_HEADLINE").getD "osu_eval_refines"
  let start := `OsuProofs ++ root.toName
  let some ci := env.find? start | IO.println s!"%%headline {start} not found"
  let mut todo : Array Name := ci.type.getUsedConstants
  let mut seen : NameSet := {}
  let mut out : Array String := #[]
  while h : todo.size > 0 do
    let n := todo.back; todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    unless (`OsuProofs).isPrefixOf n do continue
    let some c := env.find? n | continue
    if c.isTheorem then continue
    let mut deps := c.type.getUsedConstants
    let mut vh : UInt64 := 0
    match c with
    | .defnInfo d => deps := deps ++ d.value.getUsedConstants; vh := d.value.hash
    | .inductInfo i =>
      for ctor in i.ctors do
        if let some cc := env.find? ctor then
          deps := deps ++ cc.type.getUsedConstants; vh := mixHash vh cc.type.hash
    | _ => pure ()
    let kind := match c with
      | .defnInfo _ => "def" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor" | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "AXIOM" | _ => "other"
    out := out.push s!"{n} {kind} {c.type.hash} {vh}"
    todo := todo ++ deps
  for l in out.qsort (· < ·) do IO.println l
  IO.println s!"%%headline closure: {out.size} proof-local constants"
