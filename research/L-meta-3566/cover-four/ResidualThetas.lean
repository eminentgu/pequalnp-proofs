import ResidualGraphs
import PEqualNP.Outside.L_meta_615

namespace VertexPeel.CoverFourResidual

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.Helpers.PermInputs PEqualNP.Outside.L615Aux.Theta
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem thetaTransfer {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p q r t : ℕ) (ρ : Fin n → Fin (p+q+r+2))
    (hp : p=0 → 1≤q ∧ 1≤r) (hq : q=0 → 1≤p ∧ 1≤r) (hr : r=0 → 1≤p ∧ 1≤q)
    (hpq : p+q≠2) (hpr : p+r≠2) (hqr : q+r≠2)
    (cov : ∃ S : Finset (Fin (p+q+r+2)), (∀ u v : Fin (p+q+r+2),
      (u.val,v.val) ∈ thetaEdges p q r → u ∈ S ∨ v ∈ S) ∧ S.card = t)
    (minCov : ∀ S : Finset (Fin (p+q+r+2)), (∀ u v : Fin (p+q+r+2),
      (u.val,v.val) ∈ thetaEdges p q r → u ∈ S ∨ v ∈ S) → t ≤ S.card)
    (matchEdges : ∀ x : Fin (p+q+r+2) → Bool, graphFun G ∅ (x ∘ ρ) = true ↔
      ∃ u v : Fin (p+q+r+2), (u.val,v.val) ∈ thetaEdges p q r ∧ x u = true ∧ x v = true) :
    Lower G (p+q+r+2+t) := by
  intro C mono correct
  let D := relabel n (p+q+r+2) ρ C
  have legalD : Monotone2 D := by
    intro g hg
    obtain ⟨g0, mem, rfl⟩ := List.mem_map.mp hg
    exact ⟨(mono g0 mem).1, by simpa [relGate] using (mono g0 mem).2⟩
  apply (theta_exact p q r t C.size hp hq hr hpq hpr hqr cov minCov).mp
  refine ⟨D, legalD, by simp [D, relabel, Circuit.size], ?_⟩
  intro x
  have sim : circuitFun _ D x = circuitFun n C (x ∘ ρ) :=
    (rel_fold n _ ρ C.gates _ _ (rel_init n _ ρ x)).2.2 C.output
  change circuitFun _ D x = true ↔ _
  rw [sim,correct]
  exact matchEdges x

private def θ2 : Fin 7 → Fin 7 := ![0,2,4,6,3,5,1]
theorem lower2 : Lower (graph 2) 11 := by
  apply thetaTransfer (graph 2) 1 2 2 4 θ2 <;> decide +kernel

private def θ8 : Fin 8 → Fin 8 := ![0,3,5,7,2,4,6,1]
theorem lower8 : Lower (graph 8) 12 := by
  apply thetaTransfer (graph 8) 2 2 2 4 θ8 <;> decide +kernel

private def θ11 : Fin 8 → Fin 8 := ![0,1,3,6,2,4,5,7]
theorem lower11 : Lower (graph 11) 12 := by
  apply thetaTransfer (graph 11) 0 3 3 4 θ11 <;> decide +kernel

private def θ12 : Fin 8 → Fin 8 := ![0,3,1,6,2,4,5,7]
theorem lower12 : Lower (graph 12) 12 := by
  apply thetaTransfer (graph 12) 1 2 3 4 θ12 <;> decide +kernel

private def θ14 : Fin 9 → Fin 9 := ![0,1,4,7,2,3,5,6,8]
theorem lower14 : Lower (graph 14) 13 := by
  apply thetaTransfer (graph 14) 1 3 3 4 θ14 <;> decide +kernel

end VertexPeel.CoverFourResidual
