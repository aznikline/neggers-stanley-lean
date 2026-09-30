import NeggersStanley.Definitions
import NeggersStanley.Laguerre

set_option autoImplicit false

namespace NeggersStanley

/-- Transitive predecessor sets for Stembridge's naturally labelled
17-element example 14. Bit i describes label i+1 in the paper. -/
def predecessorMask (j : Fin 17) : ℕ :=
  ![0, 0, 1, 3, 5, 15, 21, 63, 85, 255, 343, 1023,
    1375, 4095, 5503, 12287, 49151] j

def witness : LabeledPoset 17 where
  lt i j := (predecessorMask j).testBit i.val
  irrefl := by decide +kernel
  trans := by decide +kernel

theorem witness_naturally_labeled : witness.NaturallyLabeled := by
  unfold LabeledPoset.NaturallyLabeled
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem witness_counts : descentCounts witness =
    [0,1,32,336,1420,2534,1946,658,86,3,0,0,0,0,0,0,0,0,0] := by
  decide +kernel

#print axioms witness_counts

end NeggersStanley
