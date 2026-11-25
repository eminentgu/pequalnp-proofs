import ThreeGatePeel
import Leaves

namespace VertexPeel.PendantPathPeel
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
    PEqualNP.TopForm PEqualNP.MetaComplexity.CoverPromise
open ThreeGatePeel CoverCircuit Leaves

/-- Any finite simple graph with a leaf adjoining a vertex of degree two
    satisfies the exact conclusion of L-meta-3566, even if its core is arbitrary. -/
theorem peel_pendant_path (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {a b : Fin n} (edge : G.Adj a b) (leaf : G.degree a = 1) (joint : G.degree b = 2) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C →
      circuitFun n C = graphFun G ∅ → SavesAt G z C := by
  classical
  have only (t : Fin n) (h : G.Adj a t) : t=b := by
    have one : (G.neighborFinset a).card ≤ 1 := by simpa using leaf.le
    exact Finset.card_le_one.mp one t ((G.mem_neighborFinset _ _).mpr h)
      b ((G.mem_neighborFinset _ _).mpr edge)
  have other : ∃ c : Fin n, G.Adj b c ∧ c ≠ a := by
    by_contra! none
    have sub : G.neighborFinset b ⊆ {a} := by
      intro u hu
      exact Finset.mem_singleton.mpr (none u ((G.mem_neighborFinset _ _).mp hu))
    have size := Finset.card_le_card sub
    simp [joint] at size
  obtain ⟨c,bc,ca⟩ := other
  by_cases survives : ∃ u v, G.Adj u v ∧ u≠b ∧ v≠b
  · refine ⟨b,by omega,?_⟩
    intro C ao cor
    obtain ⟨D,dao,dc,save⟩ := cut_joint G C ao cor edge bc ca only survives
    refine ⟨D,dao,dc.trans ?_,by omega,fun _ => by omega⟩
    funext x
    simp [graphFun,SimpleGraph.deleteIncidenceSet]
  · have stable : CoverStable G a := by
      intro S cover
      refine ⟨{b},?_,?_⟩
      · intro u v uv
        by_cases ub : u=b
        · exact Or.inl (Finset.mem_singleton.mpr ub)
        · exact Or.inr (Finset.mem_singleton.mpr (by
            by_contra vb
            exact survives ⟨u,v,uv,ub,vb⟩))
      · have hit := cover b c (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨bc,edge.ne.symm,ca⟩)
        have pos := Finset.card_pos.mpr (hit.elim (fun m => ⟨b,m⟩) (fun m => ⟨c,m⟩))
        simpa using pos
    exact ⟨a,by omega,stableLeaf G a leaf stable⟩

end VertexPeel.PendantPathPeel

#print axioms VertexPeel.PendantPathPeel.peel_pendant_path
#print axioms VertexPeel.ThreeGatePeel.cut_joint
#print axioms VertexPeel.MixedFold.compile
