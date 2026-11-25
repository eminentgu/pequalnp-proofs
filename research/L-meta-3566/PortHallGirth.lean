import PortHall
import Mathlib.Combinatorics.SimpleGraph.Girth

namespace VertexPeel.PortHall

open SimpleGraph

/-- A crown inside U produces a six-cycle whose entire support stays in U. -/
theorem six_cycle_in {n : Nat} {G : SimpleGraph (Fin n)} {U : Finset (Fin n)} (crown : SixCrownIn G U) :
    ∃ z, ∃ w : G.Walk z z, w.IsCycle ∧ w.length=6 ∧ ∀ v∈w.support, v∈U := by
  obtain ⟨X,Y,hx,hy,away,e,inside⟩ := crown
  let w : G.Walk (X 0) (X 0) :=
    .cons (e 0 1 (by decide)) (.cons (e 2 1 (by decide)).symm
      (.cons (e 2 0 (by decide)) (.cons (e 1 0 (by decide)).symm
        (.cons (e 1 2 (by decide)) (.cons (e 0 2 (by decide)).symm .nil)))))
  have inv (i j) : Y i ≠ X j := (away j i).symm
  refine ⟨X 0,w,Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_,by change 3 ≤ 6; decide⟩,rfl,?_⟩
  · simp [w,Walk.isPath_def,away,inv,hx.eq_iff,hy.eq_iff]
  · simp [w,fun i => (inside i).1,fun i => (inside i).2]

/-- Each crown extracted by the Hall obstruction is an actual Mathlib six-cycle. -/
theorem six_cycle {n : Nat} {G : SimpleGraph (Fin n)} (crown : SixCrown G) :
    ∃ z, ∃ w : G.Walk z z, w.IsCycle ∧ w.length=6 := by
  obtain ⟨X,Y,hx,hy,away,e⟩ := crown
  obtain ⟨z,w,cy,sz,_⟩ := six_cycle_in (U:=Finset.univ)
    (show SixCrownIn G _ from ⟨X,Y,hx,hy,away,e,by simp⟩)
  exact ⟨z,w,cy,sz⟩

theorem no_crown_of_girth {n : Nat} {G : SimpleGraph (Fin n)} (long : 6<G.egirth) : ¬SixCrown G := by
  intro crown
  obtain ⟨_,w,cy,sz⟩ := six_cycle crown
  have bound := cy.egirth_le_length
  rw [sz] at bound
  exact (not_le_of_gt long) bound

theorem no_four_of_girth {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (long : 4<G.egirth) : PEqualNP.TopForm.NoFourCycle G := by
  classical
  intro x y xy
  by_contra! bad
  obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp bad
  obtain ⟨xa,ya⟩ := (Finset.mem_filter.mp ha).2
  obtain ⟨xb,yb⟩ := (Finset.mem_filter.mp hb).2
  let w : G.Walk x x := .cons xa (.cons ya.symm (.cons yb (.cons xb.symm .nil)))
  have cy : w.IsCycle := Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨by
    simp [w,Walk.isPath_def,xy.symm,ab,xa.ne.symm,ya.ne.symm,yb.ne,xb.ne.symm],by change 3≤4; decide⟩
  have bound := cy.egirth_le_length
  exact (not_le_of_gt long) (show G.egirth≤4 from bound)

#print axioms no_four_of_girth
#print axioms no_crown_of_girth
end VertexPeel.PortHall
