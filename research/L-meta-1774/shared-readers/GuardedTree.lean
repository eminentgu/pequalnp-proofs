import Guarded
import SharedMask

namespace PEqualNP.Research.GuardedReaders.Tree

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover
open PEqualNP.Research.SharedMask (G C)

def prefixGates : List Gate := [⟨.or,[0,2]⟩,⟨.or,[1,3]⟩]

/-- The first observer uses `b ∨ d` and the second uses `a ∨ c`. The final OR
sees the two guarded results. All prefix wires continue to be available. -/
def guardedPlan : Readers (Fin 8) :=
  .reader false 0 4 <| .reader true (.some 3) (.some 5) <|
  .finish <| .gate false (.some .none) .none (.output .none)

def improved := attach 6 prefixGates Fin.val (guardedPlan.rerouted 6 7)

theorem recoversOriginal : attach 6 prefixGates Fin.val (guardedPlan.original 6 7) = C := rfl

theorem economical : Monotone2 improved ∧ circuitFun 6 improved = graphFun G ∅ ∧
    improved.size + 1 = C.size := by
  rw [← recoversOriginal]
  apply shared_gate_exchange G prefixGates Fin.val guardedPlan 6 7
  · intro a; exact a.isLt
  · simp [prefixGates, Monotone2]
  · exact SharedMask.computes.1
  · simp only [guardedPlan, Readers.guarded]
    decide +kernel

theorem exactSize : improved.size = 7 := rfl

end PEqualNP.Research.GuardedReaders.Tree
