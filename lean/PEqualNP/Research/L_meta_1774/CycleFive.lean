import PEqualNP.Research.L_meta_1774.Peelable
import PEqualNP.Outside.L_meta_579

namespace PEqualNP.Outside.L_meta_1774

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.Library.Peel
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private abbrev pentagon := SimpleGraph.fromRel fun i j : Fin 5 => j.val = (i.val + 1) % 5

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
      have : 0 = 2 := cycle.getVert_injOn' (by simp <;> omega) (by simp <;> omega) e
      contradiction
    have ne13 : p.getVert 1 ≠ p.getVert 3 := by
      intro e
      have : 1 = 3 := cycle.getVert_injOn' (by simp <;> omega) (by simp <;> omega) e
      contradiction
    have end4 : p.getVert 4 = p.getVert 0 := by rw [← four,p.getVert_length,p.getVert_zero]
    change pentagon.Adj (p.getVert 3) (p.getVert 4) at h3
    exact noSquare _ _ _ _ ne02 ne13 h0 h1 h2 (end4 ▸ h3)

/-- The five-cycle admits a four-internal-vertex run with the same exterior endpoint at both ends. -/
theorem cycleFiveDescent (C : Circuit) (mono : Monotone2 C) :
    let G := SimpleGraph.fromRel fun i j : Fin 5 => j.val = (i.val + 1) % 5
    circuitFun 5 C = graphFun G ∅ → 0 < (disjointOwners G C).ncard →
    ∃ D : Circuit, Monotone2 D ∧ circuitFun 5 D = graphFun G ∅ ∧ D.size ≤ C.size ∧
      (∀ j < D.size, (gateAt D j).op = GateOp.and → ∃ u v, G.Adj u v ∧ Owns 5 D j u v) ∧
      (disjointOwners G D).ncard < (disjointOwners G C).ncard := by
  intros G correct positive
  change circuitFun 5 C = graphFun pentagon ∅ at correct
  have degrees : ∀ v : Fin 5, (pentagon.neighborSet v).ncard ≤ 3 := by
    intro v
    rw [Set.ncard_eq_toFinset_card']
    change pentagon.degree v ≤ 3
    exact (by decide : ∀ u : Fin 5, pentagon.degree u ≤ 3) v
  have allowed : FanInTwo C := by
    intro g hg
    obtain ⟨op,fan⟩ := mono g hg
    refine ⟨?_,fan⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢
    tauto
  have small : HasCircuitSize 5 (Helpers.Forest.F pentagon ∅) C.size := by
    refine ⟨C,allowed,le_rfl,?_⟩
    intro x
    simpa [Helpers.Forest.F,circuitFun,graphFun] using congrFun correct x
  have bound := PEqualNP.Outside.L_meta_579 5 3 C.size pentagon ∅ degrees pentagonGirth
    (by
      intro X hasEdge
      by_cases empty : X = ∅
      · subst X
        exact Or.inr ⟨0,1,2,3,4,0,by decide⟩
      · apply Or.inl
        exact (by decide : ∀ X : Finset (Fin 5), X ≠ ∅ →
          (∃ i j, (delVerts pentagon X).Adj i j) → GoodLeaf (delVerts pentagon X)) X empty hasEdge)
    (fun _ _ _ => Finset.notMem_empty _) (Or.inr ⟨0,1,by decide⟩) (by decide) small
  have cover : CoverPromise.IsVertexCover pentagon ({0,2,4} : Finset (Fin 5)) := by
    unfold CoverPromise.IsVertexCover
    decide
  have card : ({0,2,4} : Finset (Fin 5)).card = 3 := by decide
  simp only [Finset.card_empty, zero_add] at bound
  exact coveredDescent pentagon C {0,2,4} cover (by omega) positive

end PEqualNP.Outside.L_meta_1774
