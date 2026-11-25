import OrderedMatching
import WrongSupportCircuit

namespace VertexPeel.WrongSupports
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.ReadTwo
open PEqualNP.Outside.L615Aux.Wires (point)
open VertexPeel.AndSeparation (andCone)
variable {n : ℕ}

/-- A positive wire has a positive subinput using at most one more vertex
than the number of distinct physical ANDs in its entire reachable cone, including the wire itself when it is an AND. -/
theorem width_of_and_cone (C : Circuit) (hc : IsAO2 n C) (w : ℕ) :
    WitnessWidth (Active (n := n) C w) ((andCone (n := n) C w).card + 1) := by
  classical
  intro I on
  let pos := I.powerset.filter (fun V => Active C w V)
  have hI : I ∈ pos := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.Subset.refl I), on⟩
  obtain ⟨W, hW, minimum⟩ := Finset.exists_min_image pos Finset.card ⟨I, hI⟩
  obtain ⟨subW, yes⟩ := Finset.mem_filter.mp hW
  have sub := Finset.mem_powerset.mp subW
  refine ⟨W, sub, ?_, yes⟩
  by_cases tiny : W.card ≤ 1
  · omega
  have off (V : Finset (Fin n)) (inc : V ⊆ W) (ne : V ≠ W) : wval C (point V) w = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have mem : V ∈ pos := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (inc.trans sub), h⟩
    have small := Finset.card_lt_card (lt_of_le_of_ne inc ne)
    exact Nat.not_lt_of_ge (minimum V mem) small
  -- Number the elements of a smallest accepted subinput. For each index except
  -- the last, its inclusive prefix and the set with that element erased are
  -- both rejected, and together they cover the chosen subinput.
  let index : Fin W.card ≃ ↥W := (Fintype.equivFinOfCardEq (by simp)).symm
  let v (k : Fin W.card) : Fin n := (index k).val
  have inj : Function.Injective v := Subtype.val_injective.comp index.injective
  have inside (k : Fin W.card) : v k ∈ W := (index k).property
  let lift (i : Fin (W.card - 1)) : Fin W.card := ⟨i.val, by have := i.isLt; omega⟩
  let last : Fin W.card := ⟨W.card - 1, by omega⟩
  let front (i : Fin (W.card - 1)) := W.filter fun u => ∃ t : Fin W.card, t.val ≤ i.val ∧ v t = u
  let hole (i : Fin (W.card - 1)) := W.erase (v (lift i))
  have prefixOff (i) : wval C (point (front i)) w = false := by
    apply off _ (Finset.filter_subset _ _)
    intro eq
    have mem : v last ∈ front i := by
      change front i = W at eq
      rw [eq]
      exact inside last
    obtain ⟨t, le, same⟩ := (Finset.mem_filter.mp mem).2
    have idt := inj same
    have bad : last.val ≤ i.val := idt ▸ le
    exact Nat.not_le_of_gt i.isLt bad
  have holeOff (i) : wval C (point (hole i)) w = false := by
    apply off _ (Finset.erase_subset _ _)
    intro eq
    have impossible : v (lift i) ∈ W.erase (v (lift i)) := by rw [eq]; exact inside (lift i)
    exact Finset.notMem_erase _ _ impossible
  -- Every earlier prefix lies below both later rejected inputs. The staircase
  -- lemma assigns a distinct AND gate in the cone to each such pair.
  have count := OrderedMatching.staircase C hc w
    (fun i => point (front i)) (fun i => point (hole i)) (fun _ => point W)
    prefixOff holeOff (fun _ => yes) (by
      intro i u hu
      have mem : u ∈ W := of_decide_eq_true hu
      by_cases hit : u = v (lift i)
      · exact Or.inl (decide_eq_true (Finset.mem_filter.mpr ⟨mem, lift i, le_rfl, hit.symm⟩))
      · exact Or.inr (decide_eq_true (Finset.mem_erase.mpr ⟨hit, mem⟩))) (by
      intro i j ij u hu
      obtain ⟨mem, t, le, same⟩ := Finset.mem_filter.mp (show u ∈ front i from of_decide_eq_true hu)
      constructor
      · exact decide_eq_true (Finset.mem_filter.mpr ⟨mem, t, le.trans (Fin.le_of_lt ij), same⟩)
      · apply decide_eq_true
        refine Finset.mem_erase.mpr ⟨?_, mem⟩
        intro eq
        have et := inj (same.trans eq)
        have contra : j.val ≤ i.val := by simpa only [et, lift] using le
        exact (Nat.not_le_of_gt ij) contra)
  omega

#print axioms width_of_and_cone
end VertexPeel.WrongSupports
