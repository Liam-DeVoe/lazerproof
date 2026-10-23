/-
`net::osutk` leftovers: the row helper of `Matrix3.Mult` (the spec's local `row`).
-/
import OsuProofs.Net.OsuTK
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Net.OsuTK

namespace OsuProofs
open OsuImpl

/-- Helper (spec: the local `row` of `Matrix3.mult`). -/
theorem net.osutk.m3_row_refines (a : net.osutk.Vector3) (r : net.osutk.Matrix3) :
    net.osutk.m3_row a r = ok (v3I ⟨a.x * r.row0.x + a.y * r.row1.x + a.z * r.row2.x,
      a.x * r.row0.y + a.y * r.row1.y + a.z * r.row2.y, a.x * r.row0.z + a.y * r.row1.z + a.z * r.row2.z⟩) := by
  simp [net.osutk.m3_row, v3I]

end OsuProofs
