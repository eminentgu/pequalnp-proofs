import MixedFold
import PivotAND

namespace VertexPeel.PivotAND

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.ReadTwo VertexPeel.MixedFold
variable {n : ℕ}

open Classical in
theorem physical_count (C : Circuit) :
    (physical C).card = (C.gates.filter (fun g => decide (g.op = .and))).length := by
  classical
  have prefixCount (k : ℕ) (hk : k ≤ C.gates.length) :
      ((Finset.range k).filter (isAnd C)).card =
        ((C.gates.take k).filter (fun g => decide (g.op = .and))).length := by
    induction k with
    | zero => simp
    | succ k ih =>
      have before : k < C.gates.length := by omega
      have eq := ih before.le
      rw [List.take_succ_eq_append_getElem before,List.filter_append]
      by_cases h : C.gates[k].op = .and
      · have is : isAnd C k := ⟨before,by rwa [ZeroFold.gateAt_eq C k before]⟩
        simp [Finset.range_add_one,Finset.filter_insert,is,h,eq]
      · have no : ¬isAnd C k := fun h' => h (by simpa [ZeroFold.gateAt_eq C k before] using h'.2)
        simp [Finset.range_add_one,Finset.filter_insert,no,h,eq]
  simpa [physical,Circuit.size] using prefixCount C.gates.length le_rfl

open Classical in
/-- The compiled list has exactly one physical AND per new AND-valued source
gate, even when an old wire occurs repeatedly or outside the output cone. -/
theorem compile_counted (C : Circuit) (ao : IsAO2 n C) (r : Restr n)
    (raw : ∀ i : Fin n, Const (val C r i.val) ∨ val C r i.val = fun x => x i)
    (nonconst : ¬Const (val C r C.output)) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = val C r C.output ∧
      D.size ≤ ((Finset.range C.size).filter (New C r)).card ∧
      (physical D).card = ((Finset.range C.size).filter (fun j => New C r j ∧ isAnd C j)).card := by
  classical
  obtain ⟨gs,legal,size,count,rep⟩ := compile_prefix_counted C ao r raw C.size le_rfl
  have valid : C.output < n+C.size := by
    by_contra! far
    exact nonconst ⟨false,funext fun x => ZeroFold.wval_past C _ _ far⟩
  obtain ⟨w,_,ew⟩ := (rep _ valid).resolve_left nonconst
  exact ⟨⟨gs,w⟩,legal,ew.symm,size,(physical_count _).trans count⟩

/-- A physical AND with an operand already active on the singleton x becomes
either a constant or a copy when the restriction sets x to true. -/
theorem not_new_of_lit (C : Circuit) (ao : IsAO2 n C) (r : Restr n) (x : Fin n)
    (keeps : ∀ z, r z x = true) {j : ℕ} (on : lit C x j) : ¬ New C r j := by
  obtain ⟨hand,active⟩ := on
  have hj : j<C.gates.length := hand.1
  obtain ⟨a,b,inputs,_,_,_⟩ := ZeroFold.two n C ao j hand.1
  have le (z : Fin n → Bool) : ∀ u, unit x u = true → r z u = true := by
    intro u hu
    have eq : u=x := by simpa [unit] using hu
    exact eq ▸ keeps z
  have which : ∃ w ∈ C.gates[j].inputs, wval C (unit x) w = true := by
    rcases active with left|right
    · exact ⟨a,by simp [inputs],by simpa [in0,ZeroFold.gateAt_eq C j hand.1,inputs] using left⟩
    · exact ⟨b,by simp [inputs],by simpa [in1,ZeroFold.gateAt_eq C j hand.1,inputs] using right⟩
  obtain ⟨w,read,on⟩ := which
  exact kill C ao r hand.1 read ⟨true,funext (fun z => RowGraph.wire_mono C ao (le z) w on)⟩

/-- The AND count of the restricted circuit drops by at least the number of
distinct AND positions certified by the singleton, with no fanout restriction. -/
theorem compile_lit (C : Circuit) (ao : IsAO2 n C) (r : Restr n)
    (raw : ∀ i : Fin n, Const (val C r i.val) ∨ val C r i.val = fun z => z i)
    (nonconst : ¬Const (val C r C.output))
    (x : Fin n) (keeps : ∀ z, r z x = true)
    (L : Finset ℕ) (all : ∀ j ∈ L, lit C x j) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = val C r C.output ∧
      (physical D).card + L.card ≤ (physical C).card := by
  classical
  obtain ⟨D,legal,correct,_,count⟩ := compile_counted C ao r raw nonconst
  let A := (Finset.range C.size).filter (fun j => New C r j ∧ isAnd C j)
  have dis : Disjoint A L := Finset.disjoint_left.mpr (fun {j} hj hL =>
    not_new_of_lit C ao r x keeps (all j hL) (Finset.mem_filter.mp hj).2.1)
  have sub : A∪L ⊆ physical C := by
    intro j hj
    rcases Finset.mem_union.mp hj with act|mem
    · obtain ⟨valid,_,hand⟩ := Finset.mem_filter.mp act
      exact Finset.mem_filter.mpr ⟨valid,hand⟩
    · have hand := (all j mem).1
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hand.1,hand⟩
  refine ⟨D,legal,correct,?_⟩
  calc
    (physical D).card + L.card = A.card + L.card := by rw [count]
    _ = (A∪L).card := (Finset.card_union_of_disjoint dis).symm
    _ ≤ _ := Finset.card_le_card sub

#print axioms compile_counted
#print axioms compile_lit
end VertexPeel.PivotAND
