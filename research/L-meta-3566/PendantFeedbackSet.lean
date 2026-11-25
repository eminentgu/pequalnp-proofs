import OrderedForest

namespace VertexPeel.OrderedMatching
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.CoverPromise PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover VertexPeel.CoverCircuit PEqualNP.Core PEqualNP.EdgeOwnership
open VertexPeel.AndSeparation VertexPeel.RowGraph VertexPeel.RowCharge
open PEqualNP.CircuitLowerBounds PEqualNP.ReadTwo PEqualNP.Outside.L_meta_1774
variable {n : ℕ}

/-- Isolate a set of vertices on the original input type. -/
def cutSet (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj u v := G.Adj u v ∧ u ∉ S ∧ v ∉ S
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ e => e.1.ne rfl⟩

/-- Every member of a feedback-vertex set has a private leaf outside that set.
The graph may have arbitrarily many cycles and arbitrary density. -/
theorem oriented_of_pendant_feedback (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (c : Fin n → Bool) (proper : ∀ u v, G.Adj u v → c u ≠ c v)
    (privateLeaf : ∀ v∈S, ∃ a∉S, G.Adj a v ∧ ∀ u, G.Adj a u → u=v)
    (feedback : (cutSet G S).IsAcyclic) : Oriented G c (Loc.tau G) := by
  classical
  induction S using Finset.induction_on generalizing G with
  | empty =>
    have eq : cutSet G ∅ = G := by ext a b; change (G.Adj a b ∧ a ∉ (∅:Finset _) ∧ b ∉ (∅:Finset _)) ↔ _; simp
    exact forest G (eq ▸ feedback) c proper
  | @insert p S out ih =>
    obtain ⟨l,_,lp,sole⟩ := privateLeaf p (Finset.mem_insert_self _ _)
    apply oriented_step lp sole c proper
    apply ih _ (fun _ _ e => proper _ _ (G.deleteIncidenceSet_le p e))
    · intro q hq
      obtain ⟨a,away,aq,only⟩ := privateLeaf q (Finset.mem_insert_of_mem hq)
      refine ⟨a,fun ha => away (Finset.mem_insert_of_mem ha),SimpleGraph.deleteIncidenceSet_adj.mpr ⟨aq,?_,?_⟩,?_⟩
      · intro ap; exact away (ap ▸ Finset.mem_insert_self _ _)
      · intro qp; exact out (qp ▸ hq)
      · intro u e; exact only _ (G.deleteIncidenceSet_le p e)
    · refine feedback.anti ?_
      intro u v e
      obtain ⟨uv,us,vs⟩ := e
      obtain ⟨orig,up,vp⟩ := SimpleGraph.deleteIncidenceSet_adj.mp uv
      exact ⟨orig,by simpa only [Finset.mem_insert,not_or] using And.intro up us,
        by simpa only [Finset.mem_insert,not_or] using And.intro vp vs⟩

/-- In every bipartite graph with such a feedback set, every correct binary
monotone circuit has at least one physical AND per vertex of a minimum cover. -/
theorem and_of_pendant_feedback (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n))
    (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v)
    (leaf : ∀ v∈S, ∃ a∉S, G.Adj a v ∧ ∀ u, G.Adj a u → u=v) (feedback : (cutSet G S).IsAcyclic)
    (C : Circuit) (ao : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅) :
    Loc.tau G ≤ (andCone (n:=n) C C.output).card := by
  obtain ⟨c,col⟩ := bip
  exact and_lower G ((oriented_of_pendant_feedback G S c col leaf feedback).witness col) C ao ok

/-- The full edge-plus-cover lower bound with arbitrarily many components and cycles. -/
theorem numerical_of_pendant_feedback (G : SimpleGraph (Fin n)) [base : DecidableRel G.Adj]
    (sq : NoFourCycle G) (sp : Pseudoforest.Sparse G) (S : Finset (Fin n))
    (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v)
    (leaf : ∀ v∈S, ∃ a∉S, G.Adj a v ∧ ∀ u, G.Adj a u → u=v) (feedback : (cutSet G S).IsAcyclic) :
    StableExtension.Numerical G (Loc.tau G) := by
  obtain ⟨c,col⟩ := bip
  exact @numerical n _ G base sq sp ((oriented_of_pendant_feedback G S c col leaf feedback).witness col)

#print axioms and_of_pendant_feedback
#print axioms numerical_of_pendant_feedback
end VertexPeel.OrderedMatching
