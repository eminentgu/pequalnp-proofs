import PEqualNP.Research.L_meta_1774.CoveredOwnership
import PEqualNP.MetaComplexity.L104

/-! Ownership descent on every forest, using the proved forest circuit lower bound. -/

namespace PEqualNP.Outside.L_meta_1774

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem forestDescent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (forest : G.IsAcyclic) (C : Circuit) (mono : Monotone2 C)
    (correct : circuitFun n C = graphFun G ∅) (positive : 0 < (disjointOwners G C).ncard) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
      (∀ j < D.size, (gateAt D j).op = GateOp.and → ∃ u v, G.Adj u v ∧ Owns n D j u v) ∧
      (disjointOwners G D).ncard < (disjointOwners G C).ncard := by
  classical
  have hasEdge : ∃ a b, G.Adj a b := by
    by_contra! empty
    have noOwners : disjointOwners G C = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro j ⟨a,b,c,d,ab,-⟩
      exact empty a b ab
    simp [noOwners] at positive
  let coverSize (k : ℕ) := ∃ T : Finset (Fin n), CoverPromise.IsVertexCover G T ∧ T.card = k
  have existsSize : ∃ k, coverSize k := ⟨_,Finset.univ,fun i _ _ => Or.inl (Finset.mem_univ i),rfl⟩
  obtain ⟨T,cover,size⟩ := Nat.find_spec existsSize
  have least : ∀ U : Finset (Fin n), CoverPromise.IsVertexCover G U → Nat.find existsSize ≤ U.card :=
    fun U hU => Nat.find_min' existsSize ⟨U,hU,rfl⟩
  have allowed : FanInTwo C := by
    intro g hg
    obtain ⟨op, fan⟩ := mono g hg
    refine ⟨?_,fan⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢
    tauto
  have small : HasCircuitSize n
      (fun x : Fin n → Bool => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) C.size := by
    refine ⟨C,allowed,le_rfl,?_⟩
    intro x
    simpa [circuitFun,graphFun] using congrFun correct x
  have bound := PEqualNP.MetaComplexity.L104 n (Nat.find existsSize) C.size G forest hasEdge least small
  have edges : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  exact coveredDescent G C T cover (by omega) positive

end PEqualNP.Outside.L_meta_1774
