import ReusedCone

namespace VertexPeel.RowCharge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.Core
  PEqualNP.ReadTwo VertexPeel.ZeroFold VertexPeel.ReusedCone

/-- Distinct physical OR gates feeding w, including the gate producing w itself. -/
noncomputable def orAncestors (n : Nat) (C : Circuit) (w : Nat) : Finset Nat := by
  classical
  exact (cone n C w C.size).filter (isOr C)

private theorem zero_wire {n : Nat} (C : Circuit) (ao : IsAO2 n C) (w : Nat) :
    wval C (fun _ : Fin n => false) w=false := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases input : w<n
    · exact wval_in C _ ⟨w,input⟩
    by_cases past : n+C.gates.length≤w
    · exact wval_past C _ _ past
    obtain ⟨j,rfl⟩ : ∃ j, w=n+j := ⟨w-n,by omega⟩
    have hj : j<C.gates.length := by omega
    obtain ⟨a,b,reads,ha,hb,op⟩ := two n C ao j hj
    rw [wval_gate C _ j a b hj reads ha hb,ih a ha,ih b hb]
    rcases op with hand|hor
    · simp [hand,GateOp.eval]
    · simp [hor,GateOp.eval]

/-- A wire active on k distinct singleton inputs has at least k−1 distinct
physical OR ancestors, with shared subcircuits counted only once. -/
theorem singleton_or_ancestors {n : Nat} (C : Circuit) (ao : IsAO2 n C) (w : Nat)
    (S : Finset (Fin n)) (on : ∀ v ∈ S, wval C (fun i => decide (i=v)) w=true) :
    S.card ≤ (orAncestors n C w).card+1 := by
  classical
  by_cases valid : w<n+C.size
  · let zero : Fin n → Bool := fun _ => false
    let one (v i : Fin n) := decide (i=v)
    let R := Reaches n C w
    have closed (j) (hj : j<C.size) (r : R (n+j)) (u) (hu : u∈C.gates[j].inputs) : R u :=
      r.tail ⟨j,hj,rfl,by simpa [gateAt_eq C j hj] using hu⟩
    have bound := union_within C zero one S ao (by intros; simpa [one] using ‹one _ _=true›)
      R closed C.size le_rfl {w} (by simpa using valid)
      (by simpa [R] using (Relation.ReflTransGen.refl : Reaches n C w w))
    have hit : hits C zero one S w=S := Finset.filter_true_of_mem
      (fun v hv => ⟨zero_wire C ao w,on v hv⟩)
    simp only [Finset.singleton_biUnion,Finset.card_singleton,hit] at bound
    refine bound.trans (Nat.add_le_add_right (Finset.card_le_card ?_) 1)
    intro j hj
    obtain ⟨charge,reach⟩ := Finset.mem_filter.mp hj
    obtain ⟨index,split⟩ := Finset.mem_filter.mp charge
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨index,reach⟩,split.1⟩
  · have empty : S=∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro v hv
      have bad := on v hv
      rw [wval_past C _ _ (by change n+C.size≤w; omega)] at bad
      contradiction)
    simp [empty]

#print axioms singleton_or_ancestors
end VertexPeel.RowCharge
