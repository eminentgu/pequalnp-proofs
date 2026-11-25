import RowGraph
import PEqualNP.MetaComplexity.L104
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace VertexPeel.ReusedExample
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.Core
open VertexPeel.ZeroFold VertexPeel.RowCharge VertexPeel.RowGraph

set_option maxRecDepth 100000
set_option maxHeartbeats 0
attribute [local instance] gateOpDecEq
abbrev G := edgeGraph 10 [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9)]
abbrev R : Finset (Fin 10) := {1,3,6,8}
def C : Circuit :=
  ⟨[⟨.or,[0,2]⟩,⟨.and,[1,10]⟩,⟨.or,[5,7]⟩,⟨.and,[6,12]⟩,⟨.or,[11,13]⟩,
    ⟨.or,[2,4]⟩,⟨.and,[3,15]⟩,⟨.or,[7,9]⟩,⟨.and,[8,17]⟩,⟨.or,[16,18]⟩,
    ⟨.or,[14,19]⟩],20⟩

theorem size : C.size = 11 := rfl
theorem legal : IsAO2 10 C := by decide +kernel
theorem correct : circuitFun 10 C = graphFun G ∅ := by
  funext x
  exact (by decide +kernel : ∀ x : Fin 10 → Bool, circuitFun 10 C x = graphFun G ∅ x) x

theorem forest : G.IsAcyclic :=
  SimpleGraph.IsAcyclic.anti (by
    apply SimpleGraph.le_iff_adj.mpr
    decide +kernel) (SimpleGraph.isAcyclic_pathGraph 10)

theorem minimum : IsMinimalMonoCircuit 10 C := by
  refine ⟨by simp [Monotone2,C],?_⟩
  intro E valid eq
  have agree := eq.trans correct
  have legalE : FanInTwo E := by
    intro g hg
    obtain ⟨op,fan⟩ := valid g hg
    refine ⟨?_,fan⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢
    tauto
  have small : HasCircuitSize 10
      (fun x : Fin 10 → Bool => decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) E.size := by
    refine ⟨E,legalE,le_rfl,?_⟩
    intro x
    simpa [circuitFun,graphFun] using congrFun agree x
  have cover : ∀ T : Finset (Fin 10), (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) → 4 ≤ T.card := by
    decide +kernel
  have bound := PEqualNP.MetaComplexity.L104 10 4 E.size G forest (by decide) cover small
  have edges : G.edgeFinset.card = 8 := by decide +kernel
  rw [size]
  omega

private theorem witnessRow (u v t : Fin 10)
    (base : wval C (rowBase G R u) 20 = false)
    (yes0 : v ∈ hits C (rowBase G R u) (pairInput u) (G.neighborFinset u) 14)
    (no1 : v ∉ hits C (rowBase G R u) (pairInput u) (G.neighborFinset u) 19)
    (yes1 : t ∈ hits C (rowBase G R u) (pairInput u) (G.neighborFinset u) 19)
    (no0 : t ∉ hits C (rowBase G R u) (pairInput u) (G.neighborFinset u) 14) :
    10 ∈ rowGates G R C u := by
  classical
  apply Finset.mem_filter.mpr
  exact ⟨by decide,⟨by decide,rfl⟩,base,fun incl => no1 (incl yes0),fun incl => no0 (incl yes1)⟩

/-- Both neighbors of row 2 and both neighbors of row 7 are split by the same final OR. -/
theorem twoRows : 10 ∈ rowGates G R C 2 ∧ 10 ∈ rowGates G R C 7 := by
  constructor
  · apply witnessRow 2 1 3 <;> decide +kernel
  · apply witnessRow 7 6 8 <;> decide +kernel

end VertexPeel.ReusedExample
