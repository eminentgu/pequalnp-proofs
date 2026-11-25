import OrderedForest

namespace VertexPeel.OrderedMatching
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.CoverPromise PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover VertexPeel.CoverCircuit PEqualNP.Core PEqualNP.EdgeOwnership
open VertexPeel.AndSeparation VertexPeel.RowGraph VertexPeel.RowCharge
open PEqualNP.CircuitLowerBounds PEqualNP.ReadTwo PEqualNP.Outside.L_meta_1774
variable {n : ℕ}

private theorem same_card {V : Type*} (F : SimpleGraph V) (a b : Fintype F.edgeSet) :
    (@SimpleGraph.edgeFinset _ F a).card = (@SimpleGraph.edgeFinset _ F b).card := by
  rw [Subsingleton.elim a b]

/-- One feedback edge suffices for the induced-subgraph sparsity bound, including isolates. -/
theorem feedback_sparse (G : SimpleGraph (Fin n)) (e : Sym2 (Fin n))
    (forestAfter : (G.deleteEdges {e}).IsAcyclic) : Pseudoforest.Sparse G := by
  classical
  intro S
  let H := G.deleteEdges {e}
  let part (F : SimpleGraph (Fin n)) := {w : Sym2 (Fin n) | w ∈ F.edgeSet ∧ ∀ v ∈ w, v ∈ S}
  have induced (F : SimpleGraph (Fin n)) : (part F).ncard = (F.induce (S : Set _)).edgeSet.ncard := by
    have eq : part F = (↑(F.edgeFinset ∩ S.sym2) : Set (Sym2 (Fin n))) := by
      ext t
      change (t ∈ F.edgeSet ∧ ∀ v ∈ t, v ∈ S) ↔ t ∈ F.edgeFinset ∩ S.sym2
      rw [Finset.mem_inter, Finset.mem_sym2_iff]
      simp only [SimpleGraph.mem_edgeFinset]
    rw [eq,Set.ncard_coe_finset,← SimpleGraph.coe_edgeFinset,Set.ncard_coe_finset]
    have m := F.map_edgeFinset_induce (s := (S : Set (Fin n)))
    have c := (congrArg Finset.card m).symm
    simp only [Finset.card_map,Finset.toFinset_coe] at c
    exact c.trans (same_card _ _ _)
  change (part G).ncard ≤ S.card
  by_cases emp : S = ∅
  · subst S
    have none : part G = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro w h
      induction w using Sym2.inductionOn with
      | _ a b => exact (Finset.notMem_empty a) (h.2 a (by simp))
    simp [none]
  have nz := Finset.nonempty_iff_ne_empty.mpr emp
  have : Nonempty (↑S : Set (Fin n)) := by obtain ⟨v,hv⟩ := nz; exact ⟨⟨v,hv⟩⟩
  have count := (forestAfter.induce (S : Set _)).ncard_edgeSet_add_one_le_card
  rw [← induced H] at count
  have sub : part G ⊆ insert e (part H) := by
    intro w hw
    by_cases eq : w=e
    · exact Or.inl eq
    refine Or.inr ⟨?_,hw.2⟩
    change w ∈ (G.deleteEdges {e}).edgeSet
    rw [SimpleGraph.edgeSet_deleteEdges]
    exact ⟨hw.1,by simpa using eq⟩
  have bounds := (Set.ncard_le_ncard sub).trans (Set.ncard_insert_le _ _)
  simpa using bounds.trans count

/-- If a pendant neighbor breaks every cycle, the full cover bound holds on a C4-free
bipartite graph with at most one feedback edge. -/
theorem pendant_feedback_numerical (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (sq : NoFourCycle G)
    (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v)
    (e : Sym2 (Fin n)) (fe : (G.deleteEdges {e}).IsAcyclic) {l p : Fin n}
    (lp : G.Adj l p) (sole : ∀ u, G.Adj l u → u=p) (fp : (G.deleteIncidenceSet p).IsAcyclic) :
    StableExtension.Numerical G (Loc.tau G) :=
  by exact @numerical n _ G _ sq (feedback_sparse G e fe) (leaf_cycle G lp sole fp bip)

theorem pendant_feedback_ownership (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (sq : NoFourCycle G)
    (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v)
    (e : Sym2 (Fin n)) (fe : (G.deleteEdges {e}).IsAcyclic) {l p : Fin n}
    (lp : G.Adj l p) (sole : ∀ u, G.Adj l u → u=p) (fp : (G.deleteIncidenceSet p).IsAcyclic) :
    StepAt G := ownership G sq (feedback_sparse G e fe) (leaf_cycle G lp sole fp bip)

theorem pendant_feedback_vertex (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (sq : NoFourCycle G)
    (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v)
    (e : Sym2 (Fin n)) (fe : (G.deleteEdges {e}).IsAcyclic) {l p : Fin n}
    (lp : G.Adj l p) (sole : ∀ u, G.Adj l u → u=p) (fp : (G.deleteIncidenceSet p).IsAcyclic)
    (many : 2 ≤ G.edgeFinset.card) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C →
      circuitFun n C = graphFun G ∅ → SavesAt G z C :=
  vertex_deletion G sq (feedback_sparse G e fe) (leaf_cycle G lp sole fp bip) many

#print axioms feedback_sparse
#print axioms pendant_feedback_ownership
#print axioms pendant_feedback_vertex
end VertexPeel.OrderedMatching
