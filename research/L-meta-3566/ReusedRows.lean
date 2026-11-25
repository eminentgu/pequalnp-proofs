import ReusedCone
import RowGraph

namespace VertexPeel.ReusedRows

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.ReadTwo PEqualNP.TopForm PEqualNP.Core
open VertexPeel.ZeroFold VertexPeel.RowCharge VertexPeel.RowGraph VertexPeel.ReusedCone

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (R : Finset (Fin n))
  (C : Circuit) (hc : IsAO2 n C)

/-- The positive neighbor probes seen at this wire on row u. -/
def seen (u : Fin n) (w : ℕ) : Finset (Fin n) :=
  (G.neighborFinset u).filter fun v => wval C (pairInput u v) w = true

include hc

theorem split_pair (u : Fin n) (j : ℕ) (hit : j ∈ rowGates G R C u) :
    ∃ v t, v ∈ seen G C u (n+j) ∧ t ∈ seen G C u (n+j) ∧ v ≠ t := by
  classical
  obtain ⟨hj,split⟩ := Finset.mem_filter.mp hit
  have valid := Finset.mem_range.mp hj
  obtain ⟨op,_,ex,ey⟩ := split
  obtain ⟨v,av,bv⟩ := Finset.not_subset.mp ex
  obtain ⟨t,bt,at'⟩ := Finset.not_subset.mp ey
  obtain ⟨a,b,hab,ha,hb,_⟩ := two n C hc j valid
  have eq0 : in0 C j = a := by simp [in0,gateAt_eq C j valid,hab]
  have eq1 : in1 C j = b := by simp [in1,gateAt_eq C j valid,hab]
  have hor : C.gates[j].op = .or := by simpa [gateAt_eq C j valid] using op.2
  have ne : v ≠ t := fun eq => bv (eq ▸ bt)
  rw [eq0] at av
  rw [eq1] at bt
  obtain ⟨sv,_,yesv⟩ := Finset.mem_filter.mp av
  obtain ⟨st,_,yest⟩ := Finset.mem_filter.mp bt
  refine ⟨v,t,Finset.mem_filter.mpr ⟨sv,?_⟩,Finset.mem_filter.mpr ⟨st,?_⟩,ne⟩
  · rw [wval_or C _ j a b valid hab ha hb hor, Bool.or_eq_true]; exact Or.inl yesv
  · rw [wval_or C _ j a b valid hab ha hb hor, Bool.or_eq_true]; exact Or.inr yest

private theorem row_off (u : Fin n) (j : ℕ) (hit : j ∈ rowGates G R C u) :
    wval C (pairInput u u) (n+j) = false := by
  classical
  have neg : wval C (rowBase G R u) (n+j) = false := (Finset.mem_filter.mp hit).2.2.1
  cases on : wval C (pairInput u u) (n+j)
  · rfl
  have ye := wire_mono C hc (x := pairInput u u) (y := rowBase G R u) (fun i hi => by
    have eq : i = u := by simpa [pairInput] using hi
    subst i
    simp [rowBase]) (n+j) on
  rw [neg] at ye
  contradiction

/-- Multiple splitting rows force every such row and every one of its hit columns
to affect the wire. Their sum is charged to the physical gates of that wire's cone. -/
theorem reused_cost (U : Finset (Fin n)) (j : ℕ) (square : NoFourCycle G)
    (separate : Disjoint U R) (neighbors : ∀ u ∈ U, G.neighborFinset u ⊆ R)
    (split : ∀ u ∈ U, j ∈ rowGates G R C u) (many : 2 ≤ U.card) :
    U.card + (U.biUnion (fun u => seen G C u (n+j))).card ≤
      (cone n C (n+j) C.size).card + 1 := by
  classical
  let V := U.biUnion (fun u => seen G C u (n+j))
  have small : (singles R C (n+j)).card ≤ 1 := by
    obtain ⟨u,hu,v,hv,ne⟩ := Finset.one_lt_card.mp (by omega : 1 < U.card)
    by_contra! large
    exact ne (rich_unique G R C hc square (split u hu) (split v hv) large)
  have allR : V ⊆ R := by
    intro v hv
    obtain ⟨u,hu,seenV⟩ := Finset.mem_biUnion.mp hv
    exact neighbors u hu (Finset.mem_filter.mp seenV).1
  have depL (u : Fin n) (hu : u ∈ U) : sensitive C (n+j) u := by
    obtain ⟨v,t,hv,ht,ne⟩ := split_pair G R C hc u j (split u hu)
    have off : ∃ z ∈ seen G C u (n+j), wval C (pairInput z z) (n+j) = false := by
      by_contra! none
      have mem (a : Fin n) (ha : a ∈ seen G C u (n+j)) : a ∈ singles R C (n+j) := by
        refine Finset.mem_filter.mpr ⟨neighbors u hu (Finset.mem_filter.mp ha).1,?_⟩
        simpa using none a ha
      exact ne (Finset.card_le_one.mp small _ (mem v hv) _ (mem t ht))
    obtain ⟨z,hz,off⟩ := off
    refine ⟨pairInput u z,pairInput z z,?_,?_⟩
    · intro i hi; simp [pairInput,hi]
    · rw [(Finset.mem_filter.mp hz).2,off]; decide
  have depR (v : Fin n) (hv : v ∈ V) : sensitive C (n+j) v := by
    obtain ⟨u,hu,seenV⟩ := Finset.mem_biUnion.mp hv
    refine ⟨pairInput u v,pairInput u u,?_,?_⟩
    · intro i hi; simp [pairInput,hi]
    · rw [(Finset.mem_filter.mp seenV).2,row_off G R C hc u j (split u hu)]; decide
  obtain ⟨u,hu⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
  have hvalid := Finset.mem_range.mp (Finset.mem_filter.mp (split u hu)).1
  have bound := sensitive_bound C hc (n+j) (by omega) (U ∪ V)
      (fun i hi => (Finset.mem_union.mp hi).elim (depL i) (depR i))
  rwa [Finset.card_union_of_disjoint (separate.mono_right allR)] at bound

end VertexPeel.ReusedRows
