import PEqualNP.Research.L_meta_1774.CoveredOwnership
import PEqualNP.Library.Helpers.PeelableSanity

/-! Ownership descent on project-peelable graphs, including cyclic instances. -/

namespace PEqualNP.Outside.L_meta_1774

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.Library.Peel
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

/-- Each induced subgraph containing an edge admits the project's good leaf or six-vertex run. -/
theorem peelableDescent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (peelable : Peelable G) (C : Circuit) (mono : Monotone2 C)
    (correct : circuitFun n C = graphFun G ∅) (positive : 0 < (disjointOwners G C).ncard) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
      (∀ j < D.size, (gateAt D j).op = GateOp.and → ∃ u v, G.Adj u v ∧ Owns n D j u v) ∧
      (disjointOwners G D).ncard < (disjointOwners G C).ncard := by
  classical
  obtain ⟨T,cover,card⟩ := Loc.tau_attained G
  have allowed : FanInTwo C := by
    intro g hg
    obtain ⟨op,fan⟩ := mono g hg
    refine ⟨?_,fan⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢
    tauto
  have small : HasCircuitSize n (Helpers.Forest.F G ∅) C.size := by
    refine ⟨C,allowed,le_rfl,?_⟩
    intro x
    simpa [Helpers.Forest.F,circuitFun,graphFun] using congrFun correct x
  have bound := Scratch.a1_peelable n G ∅ peelable (fun _ _ _ => Finset.notMem_empty _) C.size small
  simp only [Loc.Phi1, Finset.card_empty, zero_add] at bound
  exact coveredDescent G C T cover (by omega) positive

/-- The girth-seven and separated-branch-vertices criterion implies peelability. -/
theorem separatedDescent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (girth : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 7 ≤ p.length)
    (separated : ∀ u v : Fin n, u ≠ v → 3 ≤ G.degree u → 3 ≤ G.degree v →
      ∀ p : G.Walk u v, 7 ≤ p.length)
    (C : Circuit) (mono : Monotone2 C) (correct : circuitFun n C = graphFun G ∅)
    (positive : 0 < (disjointOwners G C).ncard) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
      (∀ j < D.size, (gateAt D j).op = GateOp.and → ∃ u v, G.Adj u v ∧ Owns n D j u v) ∧
      (disjointOwners G D).ncard < (disjointOwners G C).ncard := by
  have neighbors (u : Fin n) : (G.neighborSet u).ncard = G.degree u := by
    rw [Set.ncard_eq_toFinset_card']
    rfl
  apply peelableDescent G (Scratch.peelable_of_T7 ⟨girth,?_⟩) C mono correct positive
  intro u v huv hu hv
  exact separated u v huv (by rwa [neighbors] at hu) (by rwa [neighbors] at hv)

/-- The six-cycle supplies a cyclic example outside the girth-seven criterion. -/
theorem cycleSixDescent (C : Circuit) (mono : Monotone2 C) :
    let G := SimpleGraph.fromRel fun i j : Fin 6 => j.val = (i.val + 1) % 6
    circuitFun 6 C = graphFun G ∅ → 0 < (disjointOwners G C).ncard →
    ∃ D : Circuit, Monotone2 D ∧ circuitFun 6 D = graphFun G ∅ ∧ D.size ≤ C.size ∧
      (∀ j < D.size, (gateAt D j).op = GateOp.and → ∃ u v, G.Adj u v ∧ Owns 6 D j u v) ∧
      (disjointOwners G D).ncard < (disjointOwners G C).ncard := by
  intros G correct positive
  exact peelableDescent G Scratch.row_cycle6 C mono correct positive

end PEqualNP.Outside.L_meta_1774
