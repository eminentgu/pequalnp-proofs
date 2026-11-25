import OrderedMatching
import ForestExtension

namespace VertexPeel.OrderedMatching

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.CoverPromise PEqualNP.TopForm
variable {n k : ℕ} {G : SimpleGraph (Fin n)}

/-- An ordered matching with its two sides prescribed by a coloring. -/
def Oriented (G : SimpleGraph (Fin n)) (c : Fin n → Bool) (k : ℕ) : Prop :=
  ∃ a b : Fin k → Fin n, (∀ i, G.Adj (a i) (b i)) ∧
    (∀ i, c (a i) = false ∧ c (b i) = true) ∧ (∀ i j, i < j → ¬G.Adj (a i) (b j))

theorem Oriented.witness {c} (orientation : Oriented G c k) (proper : ∀ u v, G.Adj u v → c u ≠ c v) :
    Witness G k := by
  obtain ⟨a,b,ab,col,ord⟩ := orientation
  exact ⟨a,b,ab,fun i j e => proper _ _ e ((col i).1.trans (col j).1.symm),ord⟩

private theorem flip {c} (old : Oriented G c k) : Oriented G (fun p => !(c p)) k := by
  obtain ⟨a,b,ab,col,ord⟩ := old
  refine ⟨fun i => b i.rev,fun i => a i.rev,fun i => (ab _).symm,?_,?_⟩
  · intro i; simp [(col i.rev).1,(col i.rev).2]
  · intro i j lt e
    exact ord _ _ (Fin.rev_lt_rev.mpr lt) e.symm

/-- Deleting a leaf neighbor isolates both endpoints and drops the cover number by one. -/
theorem tau_leaf {l p : Fin n} (lp : G.Adj l p) (sole : ∀ u, G.Adj l u → u=p) :
    Loc.tau G = Loc.tau (G.deleteIncidenceSet p)+1 := by
  classical
  let H := G.deleteIncidenceSet p
  obtain ⟨S,c,s⟩ := Loc.tau_attained H
  have up : IsVertexCover G (insert p S) := by
    intro a b ab
    by_cases ap : a=p
    · exact Or.inl (ap ▸ Finset.mem_insert_self _ _)
    by_cases bp : b=p
    · exact Or.inr (bp ▸ Finset.mem_insert_self _ _)
    exact (c a b (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨ab,ap,bp⟩)).imp
      Finset.mem_insert_of_mem Finset.mem_insert_of_mem
  have upper := (Loc.tau_le G _ up).trans (Finset.card_insert_le _ _)
  obtain ⟨T,t,sz⟩ := Loc.tau_attained G
  have removable (v : Fin n) (hv : v∈T) (off : ∀ w, ¬H.Adj v w) : Loc.tau H < T.card := by
    have cov : IsVertexCover H (T.erase v) := by
      intro a b edge
      have av : a≠v := fun eq => off b (eq ▸ edge)
      have bv : b≠v := fun eq => off a (eq ▸ edge.symm)
      exact (t _ _ (G.deleteIncidenceSet_le p edge)).imp (fun h => Finset.mem_erase.mpr ⟨av,h⟩)
        (fun h => Finset.mem_erase.mpr ⟨bv,h⟩)
    exact (Loc.tau_le H _ cov).trans_lt (Finset.card_erase_lt_of_mem hv)
  have lower : Loc.tau H < T.card := by
    rcases t _ _ lp with hl|hp
    · apply removable l hl
      intro w edge
      obtain ⟨lw,_,wp⟩ := SimpleGraph.deleteIncidenceSet_adj.mp edge
      exact wp (sole _ lw)
    · apply removable p hp
      exact fun w e => (SimpleGraph.deleteIncidenceSet_adj.mp e).2.1 rfl
  change Loc.tau G = Loc.tau H+1
  omega

private theorem prepend {l p : Fin n} {c : Fin n → Bool}
    (lp : G.Adj l p) (sole : ∀ u, G.Adj l u → u=p) (cl : c l=false) (cp : c p=true)
    (old : Oriented (G.deleteIncidenceSet p) c k) : Oriented G c (k+1) := by
  obtain ⟨a,b,ab,col,ord⟩ := old
  have keep (i : Fin k) := SimpleGraph.deleteIncidenceSet_adj.mp (ab i)
  refine ⟨Fin.cons l a,Fin.cons p b,?_,?_,?_⟩
  · intro i
    exact Fin.cases lp (fun j => (keep j).1) i
  · intro i
    exact Fin.cases ⟨cl,cp⟩ col i
  · intro i
    refine Fin.cases ?_ (fun u => ?_) i
    · intro j
      refine Fin.cases (by simp) (fun v _ e => (keep v).2.2 (sole _ e)) j
    · intro j
      refine Fin.cases (by simp) (fun v uv e => ?_) j
      exact ord u v (Fin.succ_lt_succ_iff.mp uv)
        (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨e,(keep u).2.1,(keep v).2.2⟩)

theorem oriented_step {l p : Fin n} (lp : G.Adj l p) (sole : ∀ u, G.Adj l u → u=p)
    (c : Fin n → Bool) (proper : ∀ u v, G.Adj u v → c u ≠ c v)
    (old : Oriented (G.deleteIncidenceSet p) c (Loc.tau (G.deleteIncidenceSet p))) :
    Oriented G c (Loc.tau G) := by
  rw [tau_leaf lp sole]
  cases cl : c l with
  | false =>
    exact prepend lp sole cl (by have h := proper _ _ lp; cases cp : c p <;> simp_all) old
  | true =>
    have cp : c p=false := by have h := proper _ _ lp; cases h : c p <;> simp_all
    have p' := prepend (c:=fun w => !(c w)) lp sole (by simp [cl]) (by simp [cp]) (flip old)
    simpa using flip p'

private theorem edge_card_inst (F : SimpleGraph (Fin n)) (i j : Fintype F.edgeSet) :
    (@SimpleGraph.edgeFinset _ F i).card = (@SimpleGraph.edgeFinset _ F j).card := by
  rw [Subsingleton.elim i j]

/-- Every forest realizes its full cover number by an ordered matching
in either prescribed bipartite orientation. -/
theorem forest (F : SimpleGraph (Fin n)) (acyc : F.IsAcyclic) (c : Fin n → Bool)
    (proper : ∀ u v, F.Adj u v → c u ≠ c v) : Oriented F c (Loc.tau F) := by
  classical
  generalize sz : F.edgeFinset.card = m
  induction m using Nat.strong_induction_on generalizing F with
  | ind m ih =>
    by_cases edges : ∃ i j, F.Adj i j
    · obtain ⟨l,p,lp,sole,_⟩ := Helpers.Forest.forest_good_leaf F acyc edges
      apply oriented_step lp sole c proper
      let H := F.deleteIncidenceSet p
      have ds := F.degree_le_card_edgeFinset p
      have pos := (F.degree_pos_iff_exists_adj p).mpr ⟨l,lp.symm⟩
      have small : H.edgeFinset.card < m := by
        change (F.deleteIncidenceSet p).edgeFinset.card < m
        rw [F.card_edgeFinset_deleteIncidenceSet]; omega
      apply ih H.edgeFinset.card small H (acyc.anti (F.deleteIncidenceSet_le p))
        (fun i j e => proper _ _ (F.deleteIncidenceSet_le p e)) (edge_card_inst _ _ _)
    · have zero := Loc.tau_le F ∅ (fun i j ij => (edges ⟨i,j,ij⟩).elim)
      simp only [Finset.card_empty,Nat.le_zero] at zero
      rw [zero]
      exact ⟨Fin.elim0,Fin.elim0,fun i => i.elim0,fun i => i.elim0,fun i => i.elim0⟩

theorem leaf_cycle (G : SimpleGraph (Fin n)) {l p : Fin n} (lp : G.Adj l p) (sole : ∀ u, G.Adj l u → u=p)
    (forestAfter : (G.deleteIncidenceSet p).IsAcyclic)
    (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v) : Witness G (Loc.tau G) := by
  obtain ⟨c,proper⟩ := bip
  exact (oriented_step lp sole c proper (forest _ forestAfter c
    (fun i j ij => proper _ _ (G.deleteIncidenceSet_le p ij)))).witness proper

#print axioms forest
#print axioms leaf_cycle
end VertexPeel.OrderedMatching
