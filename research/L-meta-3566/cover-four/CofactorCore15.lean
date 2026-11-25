import ResidualGraphs

namespace VertexPeel.CoverFourResidual
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.Helpers.PermInputs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private abbrev G15 : SimpleGraph (Fin 9) := graph 15
private abbrev G11 : SimpleGraph (Fin 8) := graph 11
private abbrev G12 : SimpleGraph (Fin 8) := graph 12

private instance : DecidableRel G15.Adj :=
  inferInstanceAs (DecidableRel (PEqualNP.EdgeOwnership.edgeGraph 9 (table 15).2).Adj)
private instance : DecidableRel G11.Adj :=
  inferInstanceAs (DecidableRel (PEqualNP.EdgeOwnership.edgeGraph 8 (table 11).2).Adj)
private instance : DecidableRel G12.Adj :=
  inferInstanceAs (DecidableRel (PEqualNP.EdgeOwnership.edgeGraph 8 (table 12).2).Adj)

private def ρ (z : Fin 9) : Fin 9 → Fin 8 :=
  ![![0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0],
    ![1,0,3,2,0,6,5,4,7],
    ![0,1,3,2,6,0,4,5,7],
    ![1,0,2,3,5,4,0,6,7],
    ![0,1,2,3,4,5,6,0,7],
    ![0,1,2,3,4,5,6,7,0]] z

private theorem core11 : ∀ x : Fin 8 → Bool,
    graphFun G15 ∅ (Function.update (x ∘ ρ 8) 8 false) = graphFun G11 ∅ x := by
  decide +kernel

private theorem core12 : ∀ z : Fin 9, 4 ≤ z.val → z ≠ 8 → ∀ x : Fin 8 → Bool,
    graphFun G15 ∅ (Function.update (x ∘ ρ z) z false) = graphFun G12 ∅ x := by
  intro z hz he
  have cases : ∀ i : Fin 9, 4 ≤ i.val → i ≠ 8 → i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by decide
  rcases cases z hz he with rfl | rfl | rfl | rfl <;> decide +kernel

/-- Fixing any of the five subdivision vertices to false costs at least twelve gates. -/
theorem falseCofactorOfLower (lb11 : Lower (graph 11) 12) (lb12 : Lower (graph 12) 12)
    (z : Fin 9) (hz : 4 ≤ z.val) (C : Circuit) (mono : Monotone2 C)
    (correct : ∀ x : Fin 9 → Bool, circuitFun 9 C x =
      graphFun G15 ∅ (Function.update x z false)) : 12 ≤ C.size := by
  let D := relabel 9 8 (ρ z) C
  have legal : Monotone2 D := by
    intro g hg
    obtain ⟨g0,mem,rfl⟩ := List.mem_map.mp hg
    exact ⟨(mono g0 mem).1, by simpa [relGate] using (mono g0 mem).2⟩
  have sim (x : Fin 8 → Bool) : circuitFun 8 D x =
      graphFun G15 ∅ (Function.update (x ∘ ρ z) z false) :=
    ((rel_fold 9 8 (ρ z) C.gates _ _ (rel_init 9 8 (ρ z) x)).2.2 C.output).trans (correct _)
  have bound : 12 ≤ D.size := by
    by_cases he : z = 8
    · subst z
      exact lb11 D legal (funext fun x => (sim x).trans (core11 x))
    · exact lb12 D legal (funext fun x => (sim x).trans (core12 z hz he x))
  simpa [D,relabel,Circuit.size] using bound

end VertexPeel.CoverFourResidual
#print axioms VertexPeel.CoverFourResidual.falseCofactorOfLower
