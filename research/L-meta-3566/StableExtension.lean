import Leaves
import PEqualNP.Outside.L_meta_1527
import PEqualNP.Research.L_meta_1774.CoveredOwnership

namespace VertexPeel.StableExtension

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.MetaComplexity.CoverPromise PEqualNP.EdgeOwnership PEqualNP.TopForm
  PEqualNP.Outside.L_meta_1774

/-- The circuit size plus one bounds the edge count plus the given integer. -/
def Numerical {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∀ [_inst : DecidableRel G.Adj] (C : Circuit), Monotone2 C → circuitFun n C = graphFun G ∅ →
    G.edgeFinset.card + k ≤ C.size + 1

abbrev Lower {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) := Numerical G T.card

def Minimum {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  IsVertexCover G T ∧ ∀ S, IsVertexCover G S → T.card ≤ S.card

/-- In the common ambient vertex set, the new leaf was an isolate before the step. -/
def AddLeaf {n : ℕ} (T : Finset (Fin n)) (H G : SimpleGraph (Fin n)) : Prop :=
  ∃ a u : Fin n, u ∈ T ∧ G.Adj a u ∧ (∀ v, G.Adj a v → v = u) ∧ G.deleteIncidenceSet a = H

abbrev Extends {n : ℕ} (T : Finset (Fin n)) := Relation.ReflTransGen (AddLeaf T)

theorem step_minimum {n : ℕ} {T : Finset (Fin n)} {H G : SimpleGraph (Fin n)}
    (old : Minimum H T) (step : AddLeaf T H G) : Minimum G T := by
  obtain ⟨a,u,inT,edge,only,rfl⟩ := step
  refine ⟨?_,?_⟩
  · intro i j ij
    by_cases ia : i=a
    · subst i; exact Or.inr ((only j ij) ▸ inT)
    by_cases ja : j=a
    · subst j; exact Or.inl ((only i ij.symm) ▸ inT)
    exact old.1 i j (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨ij,ia,ja⟩)
  · intro S cover
    exact old.2 S (fun i j ij => cover i j (SimpleGraph.deleteIncidenceSet_adj.mp ij).1)

/-- Reinstating one leaf preserves any constant offset in the edge lower bound, regardless of
the membership of either endpoint in any particular cover. -/
theorem step_numerical {n k : ℕ} {G : SimpleGraph (Fin n)} {a u : Fin n}
    (edge : G.Adj a u) (only : ∀ v, G.Adj a v → v = u)
    (old : Numerical (G.deleteIncidenceSet a) k) : Numerical G k := by
  intro inst C mono correct
  classical
  obtain ⟨A,ao,acorr,asmall⟩ : ∃ A : Circuit, IsAO2 n A ∧ circuitFun n A = graphFun G ∅ ∧ A.size ≤ C.size := by
    apply PEqualNP.Outside.L_meta_1527 n G inst C mono
    intro x
    change circuitFun n C x = true ↔ _
    rw [correct]
    simp [graphFun]
  obtain ⟨D,dao,dev,save⟩ := Leaves.oneGate G a u edge.symm A ao acorr
  have dcorr : circuitFun n D = graphFun (G.deleteIncidenceSet a) ∅ := by
    rw [dev,SidePeel.restrict_correct G A acorr a]
    funext x; simp [graphFun]
  have dmono : Monotone2 D := by
    intro g hg
    exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using dao.1 g hg,(dao.2.2 g hg).le⟩
  have bound := old D dmono dcorr
  have onlyOne : G.neighborFinset a = {u} := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_singleton]
    exact ⟨only v,fun h => h ▸ edge⟩
  have deg : G.degree a = 1 := by rw [← G.card_neighborFinset_eq_degree,onlyOne]; simp
  have oneEdge : 0 < G.edgeFinset.card := Finset.card_pos.mpr ⟨s(a,u), by simpa using edge⟩
  rw [G.card_edgeFinset_deleteIncidenceSet,deg] at bound
  omega

theorem step_lower {n : ℕ} {T : Finset (Fin n)} {H G : SimpleGraph (Fin n)}
    (old : Lower H T) (step : AddLeaf T H G) : Lower G T := by
  obtain ⟨a,u,_,edge,only,rfl⟩ := step
  exact step_numerical edge only old

theorem closure {n : ℕ} {T : Finset (Fin n)} {H G : SimpleGraph (Fin n)}
    (additions : Extends T H G) (cover : Minimum H T) (bound : Lower H T) :
    Minimum G T ∧ Lower G T := by
  induction additions with
  | refl => exact ⟨cover,bound⟩
  | tail _ step ih => exact ⟨step_minimum ih.1 step,step_lower ih.2 step⟩

/-- The full ownership descent, even for nonminimum or initially nonproductive sources. -/
theorem descent {n : ℕ} {T : Finset (Fin n)} {H G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (additions : Extends T H G) (cover : Minimum H T) (bound : Lower H T) (C : Circuit)
    (mono : Monotone2 C) (correct : circuitFun n C = graphFun G ∅)
    (positive : 0 < (disjointOwners G C).ncard) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
      (∀ j < D.size, (gateAt D j).op = GateOp.and → ∃ u v, G.Adj u v ∧ Owns n D j u v) ∧
      (disjointOwners G D).ncard < (disjointOwners G C).ncard := by
  obtain ⟨minG,lowG⟩ := closure additions cover bound
  have h := lowG C mono correct
  have edgeCount : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  exact coveredDescent G C T minG.1 (by omega) positive

end VertexPeel.StableExtension
