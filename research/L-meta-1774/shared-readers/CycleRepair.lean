import GuardedCycle
import Omit

namespace PEqualNP.Research.GuardedReaders.Cycle

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover

def repairChoices (i : Fin (plan false false false).count) : Route :=
  if i.val = 0 then .left else if i.val = 1 then .right else .omit

def repaired : Circuit := attach 8 prefixGates Fin.val ((plan false false false).patch repairChoices 8 9 id)

/-- The first and second observers use opposite parents; the last observer keeps only
its alternative input. This removes the shared AND and the last observer's OR. -/
theorem repaired_spec : Monotone2 repaired ∧ circuitFun 8 repaired = graphFun G ∅ ∧
    repaired.size + 2 = C.size := by
  have criteria := patch_criterion G prefixGates Fin.val (plan false false false) repairChoices 8 9
    (fun a => a.isLt) (by simp [prefixGates,Monotone2])
  refine ⟨criteria.1,criteria.2.2.mpr ?_,criteria.2.1⟩
  decide +kernel

end PEqualNP.Research.GuardedReaders.Cycle
