import ResidualGraphs
import PEqualNP.Outside.L_meta_8493
import PEqualNP.Outside.L_meta_550
import PEqualNP.Outside.L_meta_1007
import PEqualNP.Outside.L_meta_723

namespace VertexPeel.CoverFourResidual

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
    PEqualNP.EdgeOwnership
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def ρ4 : Fin 8 → Fin 8 := ![0,4,5,7,3,1,2,6]
private def fn4 (x : Fin 8 → Bool) := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6) || (x 6 && x 7)

theorem lower4 : Lower (graph 4) 11 := by
  apply lowerTransfer (graph 4) ρ4 fn4
  · decide +kernel
  · exact PEqualNP.Outside.L_meta_8493

private def ρ10 : Fin 8 → Fin 8 := ![0,4,2,5,7,6,1,3]
private def fn10 (x : Fin 8 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 0 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 0 && x 7)

theorem lower10 : Lower (graph 10) 11 := by
  apply lowerTransfer (graph 10) ρ10 fn10
  · decide +kernel
  · exact PEqualNP.Outside.L_meta_550

private def ρ13 : Fin 8 → Fin 8 := ![1,4,7,2,0,5,6,3]
private def fn13 (x : Fin 8 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)

theorem lower13 : Lower (graph 13) 13 := by
  apply lowerTransfer (graph 13) ρ13 fn13
  · decide +kernel
  · intro s small
    by_contra! short
    apply PEqualNP.Outside.L_meta_1007
    obtain ⟨C,allowed,size,eval⟩ := small
    exact ⟨C,allowed,by omega,eval⟩

open PEqualNP.MetaComplexity.Helpers.PermInputs

private theorem renameCircuit {n : ℕ} (r : Fin n → Fin n) (C : Circuit) (mono : Monotone2 C) :
    ∃ D : Circuit, Monotone2 D ∧ D.size = C.size ∧
      ∀ x : Fin n → Bool, circuitFun n D x = circuitFun n C (x ∘ r) := by
  refine ⟨relabel n n r C, ?_, by simp [relabel, Circuit.size], ?_⟩
  · intro g hg
    obtain ⟨g0, mem, rfl⟩ := List.mem_map.mp hg
    exact ⟨(mono g0 mem).1, by simpa [relGate] using (mono g0 mem).2⟩
  · intro x
    exact (rel_fold n n r C.gates _ _ (rel_init n n r x)).2.2 C.output

private def rename : Fin 10 → Fin 10 := ![0,1,2,3,4,5,7,6,8,9]

private def arcs : List (ℕ × ℕ) :=
  [(0,4),(4,1),(0,5),(5,2),(0,6),(6,3),(1,7),(7,2),(1,8),(8,3),(2,9),(9,3)]

private theorem edgesMatch : ∀ x : Fin 10 → Bool, graphFun (graph 16) ∅ (x ∘ rename) = true ↔
    ∃ u v : Fin 10, (u.val, v.val) ∈ arcs ∧ x u = true ∧ x v = true := by
  decide +kernel

/-- Row 16 is the once-subdivided complete graph on four vertices. -/
theorem lower16 (C : Circuit) (mono : Monotone2 C)
    (correct : circuitFun 10 C = graphFun (graph 16) ∅) : 15 ≤ C.size := by
  obtain ⟨D, legal, size, sim⟩ := renameCircuit rename C mono
  rw [← size]
  apply PEqualNP.Outside.L_meta_723 D legal
  intro x
  change circuitFun 10 D x = true ↔ _
  rw [sim, correct]
  exact edgesMatch x

end VertexPeel.CoverFourResidual
