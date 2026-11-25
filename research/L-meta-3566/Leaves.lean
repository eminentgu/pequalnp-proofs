import Equivalence
import SidePeel

namespace VertexPeel.Leaves

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.CoverPromise PEqualNP.TopForm PEqualNP.ReadK
open CoverCircuit ZeroFold SidePeel SideReaders

-- A cover of the deletion can always be replaced by an original cover of at most equal size.
abbrev CoverStable {n : ℕ} (G : SimpleGraph (Fin n)) (a : Fin n) : Prop :=
  ∀ S : Finset (Fin n), IsVertexCover (G.deleteIncidenceSet a) S →
    ∃ T : Finset (Fin n), IsVertexCover G T ∧ T.card ≤ S.card

theorem oneGate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a u : Fin n) (neighbor : G.Adj u a) (C : Circuit)
    (ao : IsAO2 n C) (correct : circuitFun n C = graphFun G ∅) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = fv C {a} C.output ∧ D.size + 1 ≤ C.size := by
  classical
  obtain ⟨x,y,agree,diff⟩ := sensitive G C correct neighbor
  obtain ⟨j,hj,_,t,ht,reads⟩ := crosses C ao {a.val} x y
    (by intro b hb; exact agree b (fun eq => hb (by simp [eq]))) diff
    (by simpa using no_raw_output G correct a)
  have teq : t = a.val := Finset.mem_singleton.mp ht
  have removed : ¬ Mg C {a} j := kill C ao _ j hj t reads (teq ▸ fv_in0 C _ a (by simp))
  obtain ⟨D,hD,ev,size⟩ := ZeroFold.compile C ao {a}
  have strict : (Finset.range C.size).filter (Mg C {a}) ⊂ Finset.range C.size := by
    apply Finset.ssubset_iff_of_subset (Finset.filter_subset _ _) |>.mpr
    exact ⟨j, Finset.mem_range.mpr hj, by simp [removed]⟩
  have card := Finset.card_lt_card strict
  simp only [Finset.card_range] at card
  exact ⟨D,hD,ev,by omega⟩

theorem stableLeaf {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : Fin n) (leaf : G.degree a = 1) (stable : CoverStable G a)
    (C : Circuit) (ao : IsAO2 n C) (correct : circuitFun n C = graphFun G ∅) : SavesAt G a C := by
  have positive : 0 < G.degree a := by omega
  obtain ⟨u,adj⟩ := (G.degree_pos_iff_exists_adj a).mp positive
  obtain ⟨D,hao,ev,size⟩ := oneGate G a u adj.symm C ao correct
  refine ⟨D,hao,ev.trans (restrict_correct G C correct a),by omega,?_⟩
  rintro ⟨S,hS,strict⟩
  obtain ⟨T,hT,small⟩ := stable S hS
  exact (Nat.not_lt_of_ge small (strict T hT)).elim

-- Two distinct leaves at the same vertex make each leaf cover-stable.
theorem sharedNeighborStable {n : ℕ} (G : SimpleGraph (Fin n)) (a b u : Fin n)
    (ab : a ≠ b) (au : G.Adj a u) (bu : G.Adj b u)
    (onlyA : ∀ v, G.Adj a v → v = u) (onlyB : ∀ v, G.Adj b v → v = u) :
    CoverStable G a := by
  classical
  intro S cover
  have residual (x y : Fin n) (h : G.Adj x y) (hx : x ≠ a) (hy : y ≠ a) :
      x ∈ S ∨ y ∈ S := cover x y ((SimpleGraph.deleteIncidenceSet_adj).mpr ⟨h,hx,hy⟩)
  by_cases hu : u ∈ S
  · refine ⟨S,?_,le_rfl⟩
    intro x y edge
    by_cases hx : x = a
    · subst x
      exact Or.inr ((onlyA y edge) ▸ hu)
    by_cases hy : y = a
    · subst y
      exact Or.inl ((onlyA x edge.symm) ▸ hu)
    exact residual x y edge hx hy
  · have hb : b ∈ S := (residual b u bu ab.symm au.ne.symm).resolve_right hu
    let T := insert u (S.erase b)
    refine ⟨T,?_,?_⟩
    · intro x y edge
      by_cases xu : x = u
      · exact Or.inl (by simp [T,xu])
      by_cases yu : y = u
      · exact Or.inr (by simp [T,yu])
      have xa : x ≠ a := fun h => yu (onlyA y (h ▸ edge))
      have ya : y ≠ a := fun h => xu (onlyA x (h ▸ edge.symm))
      have xb : x ≠ b := fun h => yu (onlyB y (h ▸ edge))
      have yb : y ≠ b := fun h => xu (onlyB x (h ▸ edge.symm))
      rcases residual x y edge xa ya with hx | hy
      · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨xb,hx⟩))
      · exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨yb,hy⟩))
    · calc
        T.card ≤ (S.erase b).card + 1 := Finset.card_insert_le _ _
        _ = S.card := Finset.card_erase_add_one hb

theorem twoLeaves {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a b u : Fin n)
    (ab : a ≠ b) (au : G.Adj a u) (bu : G.Adj b u)
    (onlyA : ∀ v, G.Adj a v → v = u) (onlyB : ∀ v, G.Adj b v → v = u) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C →
      circuitFun n C = graphFun G ∅ → SavesAt G z C := by
  classical
  have singleton : G.neighborFinset a = {u} := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_singleton]
    exact ⟨onlyA v,fun e => e ▸ au⟩
  have deg : G.degree a = 1 := by
    change (G.neighborFinset a).card = 1
    rw [singleton,Finset.card_singleton]
  exact ⟨a,by omega,stableLeaf G a deg (sharedNeighborStable G a b u ab au bu onlyA onlyB)⟩

end VertexPeel.Leaves

#print axioms VertexPeel.Leaves.stableLeaf
#print axioms VertexPeel.Leaves.twoLeaves
