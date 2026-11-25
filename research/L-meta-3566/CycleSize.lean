import PEqualNP.Outside.L_meta_579
import PEqualNP.Library.Helpers.PeelableSanity
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

namespace VertexPeel.CycleSize

open PEqualNP.CircuitLowerBounds PEqualNP.Library.Peel
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private abbrev pentagon := SimpleGraph.fromRel fun i j : Fin 5 => j.val = (i.val + 1) % 5
private abbrev hexagon := SimpleGraph.fromRel fun i j : Fin 6 => j.val = (i.val + 1) % 6

private theorem size_bound {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (mono : Monotone2 C) (correct : circuitFun n C = graphFun G ∅) :
    HasCircuitSize n (Helpers.Forest.F G ∅) C.size := by
  refine ⟨C,?_,le_rfl,?_⟩
  · intro g hg
    obtain ⟨op,fan⟩ := mono g hg
    refine ⟨?_,fan⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢
    tauto
  · intro x
    simpa [Helpers.Forest.F,circuitFun,graphFun] using congrFun correct x

private theorem pentagonGirth (v : Fin 5) (p : pentagon.Walk v v) (cycle : p.IsCycle) :
    5 ≤ p.length := by
  have lo := cycle.three_le_length
  by_contra! short
  have h0 := p.adj_getVert_succ (i := 0) (by omega)
  have h1 := p.adj_getVert_succ (i := 1) (by omega)
  have h2 := p.adj_getVert_succ (i := 2) (by omega)
  by_cases three : p.length = 3
  · have noTri : ∀ a b c : Fin 5, pentagon.Adj a b → pentagon.Adj b c → ¬pentagon.Adj c a := by decide
    have end3 : p.getVert 3 = p.getVert 0 := by rw [← three,p.getVert_length,p.getVert_zero]
    change pentagon.Adj (p.getVert 2) (p.getVert 3) at h2
    exact noTri _ _ _ h0 h1 (end3 ▸ h2)
  · have four : p.length = 4 := by omega
    have h3 := p.adj_getVert_succ (i := 3) (by omega)
    have noSquare : ∀ a b c d : Fin 5, a ≠ c → b ≠ d → pentagon.Adj a b →
        pentagon.Adj b c → pentagon.Adj c d → ¬pentagon.Adj d a := by decide
    have ne02 : p.getVert 0 ≠ p.getVert 2 := by
      intro e
      have : 0 = 2 := cycle.getVert_injOn' (by simp) (by simp; omega) e
      contradiction
    have ne13 : p.getVert 1 ≠ p.getVert 3 := by
      intro e
      have : 1 = 3 := cycle.getVert_injOn' (by simp; omega) (by simp; omega) e
      contradiction
    have end4 : p.getVert 4 = p.getVert 0 := by rw [← four,p.getVert_length,p.getVert_zero]
    change pentagon.Adj (p.getVert 3) (p.getVert 4) at h3
    exact noSquare _ _ _ _ ne02 ne13 h0 h1 h2 (end4 ▸ h3)

/-- The five-cycle requires at least seven gates. -/
theorem cycle5_size (C : Circuit) (mono : Monotone2 C)
    (correct : circuitFun 5 C = graphFun (SimpleGraph.cycleGraph 5) ∅) : 7 ≤ C.size := by
  have same : ∀ i j, (SimpleGraph.cycleGraph 5).Adj i j ↔ pentagon.Adj i j := by decide
  have equivalent : graphFun (SimpleGraph.cycleGraph 5) ∅ = graphFun pentagon ∅ := by
    funext x
    simp only [graphFun,same]
  have computes := correct.trans equivalent
  have degrees : ∀ v : Fin 5, (pentagon.neighborSet v).ncard ≤ 3 := by
    intro v
    rw [Set.ncard_eq_toFinset_card']
    change pentagon.degree v ≤ 3
    exact (by decide : ∀ u : Fin 5, pentagon.degree u ≤ 3) v
  have bound := PEqualNP.Outside.L_meta_579 5 3 C.size pentagon ∅ degrees pentagonGirth
    (by
      intro X hasEdge
      by_cases empty : X = ∅
      · subst X
        exact Or.inr ⟨0,1,2,3,4,0,by decide⟩
      · apply Or.inl
        exact (by decide : ∀ X : Finset (Fin 5), X ≠ ∅ →
          (∃ i j, (delVerts pentagon X).Adj i j) → GoodLeaf (delVerts pentagon X)) X empty hasEdge)
    (fun _ _ _ => Finset.notMem_empty _) (Or.inr ⟨0,1,by decide⟩) (by decide) (size_bound pentagon C mono computes)
  have edgeCount : pentagon.edgeSet.ncard = 5 := by
    rw [Set.ncard_eq_toFinset_card']
    decide
  simp only [Finset.card_empty,zero_add,edgeCount] at bound
  omega

/-- The six-cycle requires at least eight gates. -/
theorem cycle6_size (C : Circuit) (mono : Monotone2 C)
    (correct : circuitFun 6 C = graphFun (SimpleGraph.cycleGraph 6) ∅) : 8 ≤ C.size := by
  have same : ∀ i j, (SimpleGraph.cycleGraph 6).Adj i j ↔ hexagon.Adj i j := by decide
  have equivalent : graphFun (SimpleGraph.cycleGraph 6) ∅ = graphFun hexagon ∅ := by
    funext x
    simp only [graphFun,same]
  have computes := correct.trans equivalent
  have bound := Scratch.a1_peelable 6 hexagon ∅ Scratch.row_cycle6
    (fun _ _ _ => Finset.notMem_empty _) C.size (size_bound hexagon C mono computes)
  have edgeCount : hexagon.edgeSet.ncard = 6 := by
    rw [Set.ncard_eq_toFinset_card']
    decide
  obtain ⟨T,covers,hT⟩ := Loc.tau_attained hexagon
  have three : 3 ≤ T.card := (by decide : ∀ T : Finset (Fin 6),
    (∀ i j, hexagon.Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card) T covers
  simp only [Loc.Phi1,Finset.card_empty,zero_add,edgeCount] at bound
  omega

end VertexPeel.CycleSize
