/-
`beatmap::mod_settings`, part 5: the acronym lookup of `Settings.table` (`table_index`,
`has_no_settings`, `table`).
-/
import OsuProofs.Beatmap.ModSettings4
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap OsuModel.Net.Framework

namespace OsuProofs
open OsuImpl

/-- the setting-less acronyms of `Settings.table` -/
def noSettingsAcr : List String := ["NF", "HR", "TC", "BL", "ST", "AL", "SG", "AT", "CN", "RX", "AP", "SO", "TR", "SI", "FR", "BU", "SY", "TD", "SV2"]

/-- position of an acronym in the Rust `table` dispatch (`1000` = unknown); spec part of `Settings.table` -/
def tableIdx (a : String) : Nat :=
  if a = "EZ" then 0 else if a ∈ noSettingsAcr then 1
  else if a = "HT" then 2
  else if a = "DC" then 3
  else if a = "SD" then 4
  else if a = "PF" then 5
  else if a = "DT" then 6
  else if a = "NC" then 7
  else if a = "HD" then 8
  else if a = "FL" then 9
  else if a = "AC" then 10
  else if a = "TP" then 11
  else if a = "DA" then 12
  else if a = "CL" then 13
  else if a = "RD" then 14
  else if a = "MR" then 15
  else if a = "WG" then 16
  else if a = "GR" then 17
  else if a = "DF" then 18
  else if a = "WU" then 19
  else if a = "WD" then 20
  else if a = "BR" then 21
  else if a = "AD" then 22
  else if a = "MU" then 23
  else if a = "NS" then 24
  else if a = "MG" then 25
  else if a = "RP" then 26
  else if a = "AS" then 27
  else if a = "DP" then 28
  else if a = "BM" then 29
  else 1000

theorem lit_AC : "AC".toList = [Char.ofNat 65, Char.ofNat 67] := by decide
theorem lit_AD : "AD".toList = [Char.ofNat 65, Char.ofNat 68] := by decide
theorem lit_AL : "AL".toList = [Char.ofNat 65, Char.ofNat 76] := by decide
theorem lit_AP : "AP".toList = [Char.ofNat 65, Char.ofNat 80] := by decide
theorem lit_AS : "AS".toList = [Char.ofNat 65, Char.ofNat 83] := by decide
theorem lit_AT : "AT".toList = [Char.ofNat 65, Char.ofNat 84] := by decide
theorem lit_BL : "BL".toList = [Char.ofNat 66, Char.ofNat 76] := by decide
theorem lit_BM : "BM".toList = [Char.ofNat 66, Char.ofNat 77] := by decide
theorem lit_BR : "BR".toList = [Char.ofNat 66, Char.ofNat 82] := by decide
theorem lit_BU : "BU".toList = [Char.ofNat 66, Char.ofNat 85] := by decide
theorem lit_CL : "CL".toList = [Char.ofNat 67, Char.ofNat 76] := by decide
theorem lit_CN : "CN".toList = [Char.ofNat 67, Char.ofNat 78] := by decide
theorem lit_DA : "DA".toList = [Char.ofNat 68, Char.ofNat 65] := by decide
theorem lit_DC : "DC".toList = [Char.ofNat 68, Char.ofNat 67] := by decide
theorem lit_DF : "DF".toList = [Char.ofNat 68, Char.ofNat 70] := by decide
theorem lit_DP : "DP".toList = [Char.ofNat 68, Char.ofNat 80] := by decide
theorem lit_DT : "DT".toList = [Char.ofNat 68, Char.ofNat 84] := by decide
theorem lit_EZ : "EZ".toList = [Char.ofNat 69, Char.ofNat 90] := by decide
theorem lit_FL : "FL".toList = [Char.ofNat 70, Char.ofNat 76] := by decide
theorem lit_FR : "FR".toList = [Char.ofNat 70, Char.ofNat 82] := by decide
theorem lit_GR : "GR".toList = [Char.ofNat 71, Char.ofNat 82] := by decide
theorem lit_HD : "HD".toList = [Char.ofNat 72, Char.ofNat 68] := by decide
theorem lit_HR : "HR".toList = [Char.ofNat 72, Char.ofNat 82] := by decide
theorem lit_HT : "HT".toList = [Char.ofNat 72, Char.ofNat 84] := by decide
theorem lit_MG : "MG".toList = [Char.ofNat 77, Char.ofNat 71] := by decide
theorem lit_MR : "MR".toList = [Char.ofNat 77, Char.ofNat 82] := by decide
theorem lit_MU : "MU".toList = [Char.ofNat 77, Char.ofNat 85] := by decide
theorem lit_NC : "NC".toList = [Char.ofNat 78, Char.ofNat 67] := by decide
theorem lit_NF : "NF".toList = [Char.ofNat 78, Char.ofNat 70] := by decide
theorem lit_NS : "NS".toList = [Char.ofNat 78, Char.ofNat 83] := by decide
theorem lit_PF : "PF".toList = [Char.ofNat 80, Char.ofNat 70] := by decide
theorem lit_RD : "RD".toList = [Char.ofNat 82, Char.ofNat 68] := by decide
theorem lit_RP : "RP".toList = [Char.ofNat 82, Char.ofNat 80] := by decide
theorem lit_RX : "RX".toList = [Char.ofNat 82, Char.ofNat 88] := by decide
theorem lit_SD : "SD".toList = [Char.ofNat 83, Char.ofNat 68] := by decide
theorem lit_SG : "SG".toList = [Char.ofNat 83, Char.ofNat 71] := by decide
theorem lit_SI : "SI".toList = [Char.ofNat 83, Char.ofNat 73] := by decide
theorem lit_SO : "SO".toList = [Char.ofNat 83, Char.ofNat 79] := by decide
theorem lit_ST : "ST".toList = [Char.ofNat 83, Char.ofNat 84] := by decide
theorem lit_SV2 : "SV2".toList = [Char.ofNat 83, Char.ofNat 86, Char.ofNat 50] := by decide
theorem lit_SY : "SY".toList = [Char.ofNat 83, Char.ofNat 89] := by decide
theorem lit_TC : "TC".toList = [Char.ofNat 84, Char.ofNat 67] := by decide
theorem lit_TD : "TD".toList = [Char.ofNat 84, Char.ofNat 68] := by decide
theorem lit_TP : "TP".toList = [Char.ofNat 84, Char.ofNat 80] := by decide
theorem lit_TR : "TR".toList = [Char.ofNat 84, Char.ofNat 82] := by decide
theorem lit_WD : "WD".toList = [Char.ofNat 87, Char.ofNat 68] := by decide
theorem lit_WG : "WG".toList = [Char.ofNat 87, Char.ofNat 71] := by decide
theorem lit_WU : "WU".toList = [Char.ofNat 87, Char.ofNat 85] := by decide

theorem ofList_eq_lit (l : List Char) (s : String) : (String.ofList l = s) ↔ l = s.toList := by
  constructor
  · intro h; rw [← h, String.toList_ofList]
  · intro h; rw [h, String.ofList_toList]

theorem se_AC (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [65#u8, 67#u8] p)) =
      ok (decide (String.ofList (strS acr) = "AC")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_AC]; simp [litS, Array.to_slice, Array.make]

theorem se_AD (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [65#u8, 68#u8] p)) =
      ok (decide (String.ofList (strS acr) = "AD")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_AD]; simp [litS, Array.to_slice, Array.make]

theorem se_AL (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [65#u8, 76#u8] p)) =
      ok (decide (String.ofList (strS acr) = "AL")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_AL]; simp [litS, Array.to_slice, Array.make]

theorem se_AP (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [65#u8, 80#u8] p)) =
      ok (decide (String.ofList (strS acr) = "AP")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_AP]; simp [litS, Array.to_slice, Array.make]

theorem se_AS (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [65#u8, 83#u8] p)) =
      ok (decide (String.ofList (strS acr) = "AS")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_AS]; simp [litS, Array.to_slice, Array.make]

theorem se_AT (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [65#u8, 84#u8] p)) =
      ok (decide (String.ofList (strS acr) = "AT")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_AT]; simp [litS, Array.to_slice, Array.make]

theorem se_BL (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [66#u8, 76#u8] p)) =
      ok (decide (String.ofList (strS acr) = "BL")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_BL]; simp [litS, Array.to_slice, Array.make]

theorem se_BM (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [66#u8, 77#u8] p)) =
      ok (decide (String.ofList (strS acr) = "BM")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_BM]; simp [litS, Array.to_slice, Array.make]

theorem se_BR (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [66#u8, 82#u8] p)) =
      ok (decide (String.ofList (strS acr) = "BR")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_BR]; simp [litS, Array.to_slice, Array.make]

theorem se_BU (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [66#u8, 85#u8] p)) =
      ok (decide (String.ofList (strS acr) = "BU")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_BU]; simp [litS, Array.to_slice, Array.make]

theorem se_CL (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [67#u8, 76#u8] p)) =
      ok (decide (String.ofList (strS acr) = "CL")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_CL]; simp [litS, Array.to_slice, Array.make]

theorem se_CN (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [67#u8, 78#u8] p)) =
      ok (decide (String.ofList (strS acr) = "CN")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_CN]; simp [litS, Array.to_slice, Array.make]

theorem se_DA (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [68#u8, 65#u8] p)) =
      ok (decide (String.ofList (strS acr) = "DA")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_DA]; simp [litS, Array.to_slice, Array.make]

theorem se_DC (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [68#u8, 67#u8] p)) =
      ok (decide (String.ofList (strS acr) = "DC")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_DC]; simp [litS, Array.to_slice, Array.make]

theorem se_DF (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [68#u8, 70#u8] p)) =
      ok (decide (String.ofList (strS acr) = "DF")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_DF]; simp [litS, Array.to_slice, Array.make]

theorem se_DP (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [68#u8, 80#u8] p)) =
      ok (decide (String.ofList (strS acr) = "DP")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_DP]; simp [litS, Array.to_slice, Array.make]

theorem se_DT (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [68#u8, 84#u8] p)) =
      ok (decide (String.ofList (strS acr) = "DT")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_DT]; simp [litS, Array.to_slice, Array.make]

theorem se_EZ (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [69#u8, 90#u8] p)) =
      ok (decide (String.ofList (strS acr) = "EZ")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_EZ]; simp [litS, Array.to_slice, Array.make]

theorem se_FL (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [70#u8, 76#u8] p)) =
      ok (decide (String.ofList (strS acr) = "FL")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_FL]; simp [litS, Array.to_slice, Array.make]

theorem se_FR (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [70#u8, 82#u8] p)) =
      ok (decide (String.ofList (strS acr) = "FR")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_FR]; simp [litS, Array.to_slice, Array.make]

theorem se_GR (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [71#u8, 82#u8] p)) =
      ok (decide (String.ofList (strS acr) = "GR")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_GR]; simp [litS, Array.to_slice, Array.make]

theorem se_HD (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [72#u8, 68#u8] p)) =
      ok (decide (String.ofList (strS acr) = "HD")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_HD]; simp [litS, Array.to_slice, Array.make]

theorem se_HR (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [72#u8, 82#u8] p)) =
      ok (decide (String.ofList (strS acr) = "HR")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_HR]; simp [litS, Array.to_slice, Array.make]

theorem se_HT (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [72#u8, 84#u8] p)) =
      ok (decide (String.ofList (strS acr) = "HT")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_HT]; simp [litS, Array.to_slice, Array.make]

theorem se_MG (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [77#u8, 71#u8] p)) =
      ok (decide (String.ofList (strS acr) = "MG")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_MG]; simp [litS, Array.to_slice, Array.make]

theorem se_MR (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [77#u8, 82#u8] p)) =
      ok (decide (String.ofList (strS acr) = "MR")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_MR]; simp [litS, Array.to_slice, Array.make]

theorem se_MU (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [77#u8, 85#u8] p)) =
      ok (decide (String.ofList (strS acr) = "MU")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_MU]; simp [litS, Array.to_slice, Array.make]

theorem se_NC (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [78#u8, 67#u8] p)) =
      ok (decide (String.ofList (strS acr) = "NC")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_NC]; simp [litS, Array.to_slice, Array.make]

theorem se_NF (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [78#u8, 70#u8] p)) =
      ok (decide (String.ofList (strS acr) = "NF")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_NF]; simp [litS, Array.to_slice, Array.make]

theorem se_NS (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [78#u8, 83#u8] p)) =
      ok (decide (String.ofList (strS acr) = "NS")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_NS]; simp [litS, Array.to_slice, Array.make]

theorem se_PF (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [80#u8, 70#u8] p)) =
      ok (decide (String.ofList (strS acr) = "PF")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_PF]; simp [litS, Array.to_slice, Array.make]

theorem se_RD (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [82#u8, 68#u8] p)) =
      ok (decide (String.ofList (strS acr) = "RD")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_RD]; simp [litS, Array.to_slice, Array.make]

theorem se_RP (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [82#u8, 80#u8] p)) =
      ok (decide (String.ofList (strS acr) = "RP")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_RP]; simp [litS, Array.to_slice, Array.make]

theorem se_RX (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [82#u8, 88#u8] p)) =
      ok (decide (String.ofList (strS acr) = "RX")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_RX]; simp [litS, Array.to_slice, Array.make]

theorem se_SD (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [83#u8, 68#u8] p)) =
      ok (decide (String.ofList (strS acr) = "SD")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_SD]; simp [litS, Array.to_slice, Array.make]

theorem se_SG (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [83#u8, 71#u8] p)) =
      ok (decide (String.ofList (strS acr) = "SG")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_SG]; simp [litS, Array.to_slice, Array.make]

theorem se_SI (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [83#u8, 73#u8] p)) =
      ok (decide (String.ofList (strS acr) = "SI")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_SI]; simp [litS, Array.to_slice, Array.make]

theorem se_SO (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [83#u8, 79#u8] p)) =
      ok (decide (String.ofList (strS acr) = "SO")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_SO]; simp [litS, Array.to_slice, Array.make]

theorem se_ST (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [83#u8, 84#u8] p)) =
      ok (decide (String.ofList (strS acr) = "ST")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_ST]; simp [litS, Array.to_slice, Array.make]

theorem se_SV2 (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 3#usize [83#u8, 86#u8, 50#u8] p)) =
      ok (decide (String.ofList (strS acr) = "SV2")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_SV2]; simp [litS, Array.to_slice, Array.make]

theorem se_SY (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [83#u8, 89#u8] p)) =
      ok (decide (String.ofList (strS acr) = "SY")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_SY]; simp [litS, Array.to_slice, Array.make]

theorem se_TC (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [84#u8, 67#u8] p)) =
      ok (decide (String.ofList (strS acr) = "TC")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_TC]; simp [litS, Array.to_slice, Array.make]

theorem se_TD (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [84#u8, 68#u8] p)) =
      ok (decide (String.ofList (strS acr) = "TD")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_TD]; simp [litS, Array.to_slice, Array.make]

theorem se_TP (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [84#u8, 80#u8] p)) =
      ok (decide (String.ofList (strS acr) = "TP")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_TP]; simp [litS, Array.to_slice, Array.make]

theorem se_TR (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [84#u8, 82#u8] p)) =
      ok (decide (String.ofList (strS acr) = "TR")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_TR]; simp [litS, Array.to_slice, Array.make]

theorem se_WD (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [87#u8, 68#u8] p)) =
      ok (decide (String.ofList (strS acr) = "WD")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_WD]; simp [litS, Array.to_slice, Array.make]

theorem se_WG (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [87#u8, 71#u8] p)) =
      ok (decide (String.ofList (strS acr) = "WG")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_WG]; simp [litS, Array.to_slice, Array.make]

theorem se_WU (acr : Slice U32) (hs : ValidStr acr) (p) :
    beatmap.dotnet.str_eq acr (Array.to_slice (Array.make 2#usize [87#u8, 85#u8] p)) =
      ok (decide (String.ofList (strS acr) = "WU")) := by
  rw [beatmap.dotnet.str_eq_refines acr hs]; simp only [ofList_eq_lit, lit_WU]; simp [litS, Array.to_slice, Array.make]

theorem ite_ok_true_or (c d : Prop) [Decidable c] [Decidable d] :
    (if c then ok true else ok (decide d) : Result Bool) = ok (decide (c ∨ d)) := by
  by_cases h : c <;> simp [h]

theorem ite_ok_true_false (c : Prop) [Decidable c] :
    (if c then ok true else ok false : Result Bool) = ok (decide c) := by
  by_cases h : c <;> simp [h]

theorem beatmap.mod_settings.has_no_settings_refines (acr : Slice U32) (hs : ValidStr acr) :
    beatmap.mod_settings.has_no_settings acr = ok (decide (String.ofList (strS acr) ∈ noSettingsAcr)) := by
  unfold beatmap.mod_settings.has_no_settings
  simp only [lift, bind_ok, se_AC acr hs, se_AD acr hs, se_AL acr hs, se_AP acr hs, se_AS acr hs, se_AT acr hs, se_BL acr hs, se_BM acr hs, se_BR acr hs, se_BU acr hs, se_CL acr hs, se_CN acr hs, se_DA acr hs, se_DC acr hs, se_DF acr hs, se_DP acr hs, se_DT acr hs, se_EZ acr hs, se_FL acr hs, se_FR acr hs, se_GR acr hs, se_HD acr hs, se_HR acr hs, se_HT acr hs, se_MG acr hs, se_MR acr hs, se_MU acr hs, se_NC acr hs, se_NF acr hs, se_NS acr hs, se_PF acr hs, se_RD acr hs, se_RP acr hs, se_RX acr hs, se_SD acr hs, se_SG acr hs, se_SI acr hs, se_SO acr hs, se_ST acr hs, se_SV2 acr hs, se_SY acr hs, se_TC acr hs, se_TD acr hs, se_TP acr hs, se_TR acr hs, se_WD acr hs, se_WG acr hs, se_WU acr hs]
  simp only [decide_eq_true_eq, ite_ok_true_or, ite_ok_true_false]
  congr 1
  simp only [noSettingsAcr, List.mem_cons, List.not_mem_nil, or_false]

set_option linter.overlappingInstances false in
theorem ite_R (c : Prop) [i1 : Decidable c] [i2 : Decidable c] {a b : Result U32} {n m : Nat}
    (ha : ∃ r, a = ok r ∧ r.val = n) (hb : ∃ r, b = ok r ∧ r.val = m) :
    ∃ r, (@ite _ c i1 a b) = ok r ∧ r.val = (@ite _ c i2 n m) := by
  by_cases h : c
  · rw [@if_pos _ i1 h, @if_pos _ i2 h]; exact ha
  · rw [@if_neg _ i1 h, @if_neg _ i2 h]; exact hb

theorem beatmap.mod_settings.table_index_refines (acr : Slice U32) (hs : ValidStr acr) :
    ∃ r, beatmap.mod_settings.table_index acr = ok r ∧ r.val = tableIdx (String.ofList (strS acr)) := by
  unfold beatmap.mod_settings.table_index
  simp only [lift, bind_ok, se_AC acr hs, se_AD acr hs, se_AL acr hs, se_AP acr hs, se_AS acr hs, se_AT acr hs, se_BL acr hs, se_BM acr hs, se_BR acr hs, se_BU acr hs, se_CL acr hs, se_CN acr hs, se_DA acr hs, se_DC acr hs, se_DF acr hs, se_DP acr hs, se_DT acr hs, se_EZ acr hs, se_FL acr hs, se_FR acr hs, se_GR acr hs, se_HD acr hs, se_HR acr hs, se_HT acr hs, se_MG acr hs, se_MR acr hs, se_MU acr hs, se_NC acr hs, se_NF acr hs, se_NS acr hs, se_PF acr hs, se_RD acr hs, se_RP acr hs, se_RX acr hs, se_SD acr hs, se_SG acr hs, se_SI acr hs, se_SO acr hs, se_ST acr hs, se_SV2 acr hs, se_SY acr hs, se_TC acr hs, se_TD acr hs, se_TP acr hs, se_TR acr hs, se_WD acr hs, se_WG acr hs, se_WU acr hs, beatmap.mod_settings.has_no_settings_refines acr hs]
  simp only [decide_eq_true_eq]
  unfold tableIdx
  generalize String.ofList (strS acr) = A
  repeat' (apply ite_R)
  all_goals exact ⟨_, rfl, rfl⟩

/-- the spec table selected by a dispatch index -/
def tableOfIdx : Nat → Option (List SettingDef)
  | 1 => some []
  | 0 => Settings.table "EZ"
  | 2 => Settings.table "HT"
  | 3 => Settings.table "DC"
  | 4 => Settings.table "SD"
  | 5 => Settings.table "PF"
  | 6 => Settings.table "DT"
  | 7 => Settings.table "NC"
  | 8 => Settings.table "HD"
  | 9 => Settings.table "FL"
  | 10 => Settings.table "AC"
  | 11 => Settings.table "TP"
  | 12 => Settings.table "DA"
  | 13 => Settings.table "CL"
  | 14 => Settings.table "RD"
  | 15 => Settings.table "MR"
  | 16 => Settings.table "WG"
  | 17 => Settings.table "GR"
  | 18 => Settings.table "DF"
  | 19 => Settings.table "WU"
  | 20 => Settings.table "WD"
  | 21 => Settings.table "BR"
  | 22 => Settings.table "AD"
  | 23 => Settings.table "MU"
  | 24 => Settings.table "NS"
  | 25 => Settings.table "MG"
  | 26 => Settings.table "RP"
  | 27 => Settings.table "AS"
  | 28 => Settings.table "DP"
  | 29 => Settings.table "BM"
  | _ => none

theorem table_none (A : String) (h_EZ : A ≠ "EZ") (h_HT : A ≠ "HT") (h_DC : A ≠ "DC") (h_SD : A ≠ "SD") (h_PF : A ≠ "PF") (h_DT : A ≠ "DT") (h_NC : A ≠ "NC") (h_HD : A ≠ "HD") (h_FL : A ≠ "FL") (h_AC : A ≠ "AC") (h_TP : A ≠ "TP") (h_DA : A ≠ "DA") (h_CL : A ≠ "CL") (h_RD : A ≠ "RD") (h_MR : A ≠ "MR") (h_WG : A ≠ "WG") (h_GR : A ≠ "GR") (h_DF : A ≠ "DF") (h_WU : A ≠ "WU") (h_WD : A ≠ "WD") (h_BR : A ≠ "BR") (h_AD : A ≠ "AD") (h_MU : A ≠ "MU") (h_NS : A ≠ "NS") (h_MG : A ≠ "MG") (h_RP : A ≠ "RP") (h_AS : A ≠ "AS") (h_DP : A ≠ "DP") (h_BM : A ≠ "BM") (h_NF : A ≠ "NF") (h_HR : A ≠ "HR") (h_TC : A ≠ "TC") (h_BL : A ≠ "BL") (h_ST : A ≠ "ST") (h_AL : A ≠ "AL") (h_SG : A ≠ "SG") (h_AT : A ≠ "AT") (h_CN : A ≠ "CN") (h_RX : A ≠ "RX") (h_AP : A ≠ "AP") (h_SO : A ≠ "SO") (h_TR : A ≠ "TR") (h_SI : A ≠ "SI") (h_FR : A ≠ "FR") (h_BU : A ≠ "BU") (h_SY : A ≠ "SY") (h_TD : A ≠ "TD") (h_SV2 : A ≠ "SV2") :
    Settings.table A = none := by
  unfold Settings.table
  split <;> first | rfl | contradiction

theorem table_of_idx (A : String) : Settings.table A = tableOfIdx (tableIdx A) := by
  unfold tableIdx
  by_cases h_EZ : A = "EZ"
  · rw [if_pos h_EZ]; subst h_EZ; rfl
  rw [if_neg h_EZ]
  by_cases hm : A ∈ noSettingsAcr
  · rw [if_pos hm]
    simp only [noSettingsAcr, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> rfl
  rw [if_neg hm]
  by_cases h_HT : A = "HT"
  · rw [if_pos h_HT]; subst h_HT; rfl
  rw [if_neg h_HT]
  by_cases h_DC : A = "DC"
  · rw [if_pos h_DC]; subst h_DC; rfl
  rw [if_neg h_DC]
  by_cases h_SD : A = "SD"
  · rw [if_pos h_SD]; subst h_SD; rfl
  rw [if_neg h_SD]
  by_cases h_PF : A = "PF"
  · rw [if_pos h_PF]; subst h_PF; rfl
  rw [if_neg h_PF]
  by_cases h_DT : A = "DT"
  · rw [if_pos h_DT]; subst h_DT; rfl
  rw [if_neg h_DT]
  by_cases h_NC : A = "NC"
  · rw [if_pos h_NC]; subst h_NC; rfl
  rw [if_neg h_NC]
  by_cases h_HD : A = "HD"
  · rw [if_pos h_HD]; subst h_HD; rfl
  rw [if_neg h_HD]
  by_cases h_FL : A = "FL"
  · rw [if_pos h_FL]; subst h_FL; rfl
  rw [if_neg h_FL]
  by_cases h_AC : A = "AC"
  · rw [if_pos h_AC]; subst h_AC; rfl
  rw [if_neg h_AC]
  by_cases h_TP : A = "TP"
  · rw [if_pos h_TP]; subst h_TP; rfl
  rw [if_neg h_TP]
  by_cases h_DA : A = "DA"
  · rw [if_pos h_DA]; subst h_DA; rfl
  rw [if_neg h_DA]
  by_cases h_CL : A = "CL"
  · rw [if_pos h_CL]; subst h_CL; rfl
  rw [if_neg h_CL]
  by_cases h_RD : A = "RD"
  · rw [if_pos h_RD]; subst h_RD; rfl
  rw [if_neg h_RD]
  by_cases h_MR : A = "MR"
  · rw [if_pos h_MR]; subst h_MR; rfl
  rw [if_neg h_MR]
  by_cases h_WG : A = "WG"
  · rw [if_pos h_WG]; subst h_WG; rfl
  rw [if_neg h_WG]
  by_cases h_GR : A = "GR"
  · rw [if_pos h_GR]; subst h_GR; rfl
  rw [if_neg h_GR]
  by_cases h_DF : A = "DF"
  · rw [if_pos h_DF]; subst h_DF; rfl
  rw [if_neg h_DF]
  by_cases h_WU : A = "WU"
  · rw [if_pos h_WU]; subst h_WU; rfl
  rw [if_neg h_WU]
  by_cases h_WD : A = "WD"
  · rw [if_pos h_WD]; subst h_WD; rfl
  rw [if_neg h_WD]
  by_cases h_BR : A = "BR"
  · rw [if_pos h_BR]; subst h_BR; rfl
  rw [if_neg h_BR]
  by_cases h_AD : A = "AD"
  · rw [if_pos h_AD]; subst h_AD; rfl
  rw [if_neg h_AD]
  by_cases h_MU : A = "MU"
  · rw [if_pos h_MU]; subst h_MU; rfl
  rw [if_neg h_MU]
  by_cases h_NS : A = "NS"
  · rw [if_pos h_NS]; subst h_NS; rfl
  rw [if_neg h_NS]
  by_cases h_MG : A = "MG"
  · rw [if_pos h_MG]; subst h_MG; rfl
  rw [if_neg h_MG]
  by_cases h_RP : A = "RP"
  · rw [if_pos h_RP]; subst h_RP; rfl
  rw [if_neg h_RP]
  by_cases h_AS : A = "AS"
  · rw [if_pos h_AS]; subst h_AS; rfl
  rw [if_neg h_AS]
  by_cases h_DP : A = "DP"
  · rw [if_pos h_DP]; subst h_DP; rfl
  rw [if_neg h_DP]
  by_cases h_BM : A = "BM"
  · rw [if_pos h_BM]; subst h_BM; rfl
  rw [if_neg h_BM]
  have h_NF : A ≠ "NF" := fun h => hm (by simp [noSettingsAcr, h])
  have h_HR : A ≠ "HR" := fun h => hm (by simp [noSettingsAcr, h])
  have h_TC : A ≠ "TC" := fun h => hm (by simp [noSettingsAcr, h])
  have h_BL : A ≠ "BL" := fun h => hm (by simp [noSettingsAcr, h])
  have h_ST : A ≠ "ST" := fun h => hm (by simp [noSettingsAcr, h])
  have h_AL : A ≠ "AL" := fun h => hm (by simp [noSettingsAcr, h])
  have h_SG : A ≠ "SG" := fun h => hm (by simp [noSettingsAcr, h])
  have h_AT : A ≠ "AT" := fun h => hm (by simp [noSettingsAcr, h])
  have h_CN : A ≠ "CN" := fun h => hm (by simp [noSettingsAcr, h])
  have h_RX : A ≠ "RX" := fun h => hm (by simp [noSettingsAcr, h])
  have h_AP : A ≠ "AP" := fun h => hm (by simp [noSettingsAcr, h])
  have h_SO : A ≠ "SO" := fun h => hm (by simp [noSettingsAcr, h])
  have h_TR : A ≠ "TR" := fun h => hm (by simp [noSettingsAcr, h])
  have h_SI : A ≠ "SI" := fun h => hm (by simp [noSettingsAcr, h])
  have h_FR : A ≠ "FR" := fun h => hm (by simp [noSettingsAcr, h])
  have h_BU : A ≠ "BU" := fun h => hm (by simp [noSettingsAcr, h])
  have h_SY : A ≠ "SY" := fun h => hm (by simp [noSettingsAcr, h])
  have h_TD : A ≠ "TD" := fun h => hm (by simp [noSettingsAcr, h])
  have h_SV2 : A ≠ "SV2" := fun h => hm (by simp [noSettingsAcr, h])
  rw [table_none A h_EZ h_HT h_DC h_SD h_PF h_DT h_NC h_HD h_FL h_AC h_TP h_DA h_CL h_RD h_MR h_WG h_GR h_DF h_WU h_WD h_BR h_AD h_MU h_NS h_MG h_RP h_AS h_DP h_BM h_NF h_HR h_TC h_BL h_ST h_AL h_SG h_AT h_CN h_RX h_AP h_SO h_TR h_SI h_FR h_BU h_SY h_TD h_SV2]; rfl


theorem tableOfIdx_ge (n : Nat) (h : 30 ≤ n) : tableOfIdx n = none := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 30 := ⟨n - 30, by omega⟩
  rfl

theorem beatmap.mod_settings.table_refines (acr : Slice U32) (hs : ValidStr acr) :
    ∃ r, beatmap.mod_settings.table acr = ok r ∧
      r.map (fun v => v.val.map sdS) = Settings.table (String.ofList (strS acr)) := by
  obtain ⟨i, hi, hiv⟩ := beatmap.mod_settings.table_index_refines acr hs
  rw [table_of_idx]
  generalize tableIdx (String.ofList (strS acr)) = n at hiv
  unfold beatmap.mod_settings.table
  rw [hi, bind_ok]
  split
  all_goals try (simp only [names_u32_mk_val, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hiv; subst hiv; simp only [tableOfIdx])
  all_goals first
    | (exact ⟨_, rfl, rfl⟩)
    | (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_ez_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_ht_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_dc_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_sd_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_pf_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_dt_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_nc_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_hd_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_fl_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_ac_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_tp_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_da_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_cl_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_rd_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_mr_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_wg_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_gr_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_df_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_wu_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_wd_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_br_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_ad_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_mu_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_ns_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_mg_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_rp_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_as_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_dp_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩) |
      (obtain ⟨v, hv, hvv⟩ := beatmap.mod_settings.table_bm_refines; rw [hv, bind_ok, hvv]; exact ⟨_, rfl, rfl⟩)
    | skip
  simp only [names_u32_eq_iff, names_u32_mk_val, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, imp_false] at *
  rw [tableOfIdx_ge n (by omega)]
  exact ⟨_, rfl, rfl⟩

end OsuProofs
