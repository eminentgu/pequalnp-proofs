import ZeroFold

namespace VertexPeel.RowCharge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK PEqualNP.ReadTwo PEqualNP.Core
open VertexPeel.ZeroFold

variable {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n → Fin n → Bool) (S : Finset (Fin n))

/-- Positive tests distinguished from a single negative test by this physical wire. -/
def hits (w : ℕ) : Finset (Fin n) :=
  S.filter fun v => wval C x w = false ∧ wval C (p v) w = true

/-- A false OR gate whose two operands each distinguish a test missed by the other. -/
def splits (j : ℕ) : Prop :=
  isOr C j ∧ wval C x (n+j) = false ∧
    ¬ hits C x p S (in0 C j) ⊆ hits C x p S (in1 C j) ∧
    ¬ hits C x p S (in1 C j) ⊆ hits C x p S (in0 C j)

noncomputable def charged (t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range t).filter (splits C x p S)

private theorem operands {j : ℕ} (hj : j < C.gates.length) {a b : ℕ}
    (hab : C.gates[j].inputs = [a,b]) : in0 C j = a ∧ in1 C j = b := by
  simp [in0, in1, gateAt_eq C j hj, hab]

private theorem children (hc : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) :
    ∃ K : Finset ℕ, (∀ k ∈ K, k < n+j) ∧
      hits C x p S (n+j) ⊆ K.biUnion (hits C x p S) ∧
      K.card ≤ 1 + (if j ∈ charged C x p S (j+1) then 1 else 0) := by
  classical
  obtain ⟨a,b,hab,ha,hb,hop⟩ := two n C hc j hj
  let H := hits C x p S
  have one (k : ℕ) (hk : k < n+j) (h : H (n+j) ⊆ H k) :
      ∃ K : Finset ℕ, (∀ w ∈ K, w < n+j) ∧ H (n+j) ⊆ K.biUnion H ∧
        K.card ≤ 1 + (if j ∈ charged C x p S (j+1) then 1 else 0) :=
    ⟨{k}, by simpa, by simpa using h, by simp⟩
  by_cases base : wval C x (n+j) = false
  · rcases hop with hand|hor
    · have e := wval_and C x j a b hj hab ha hb hand
      have drop (k : ℕ) (hk : wval C x k = false)
          (pos : ∀ v, wval C (p v) (n+j) = true → wval C (p v) k = true) : H (n+j) ⊆ H k := by
        intro v hv
        obtain ⟨hs,_,hp⟩ := Finset.mem_filter.mp hv
        exact Finset.mem_filter.mpr ⟨hs,hk,pos v hp⟩
      cases hax : wval C x a with
      | false => exact one a ha (drop a hax (fun v hv => by
                   rw [wval_and C (p v) j a b hj hab ha hb hand, Bool.and_eq_true] at hv
                   exact hv.1))
      | true =>
        have hbx : wval C x b = false := by simpa [hax,base] using e.symm
        exact one b hb (drop b hbx (fun v hv => by
          rw [wval_and C (p v) j a b hj hab ha hb hand, Bool.and_eq_true] at hv
          exact hv.2))
    · have e := wval_or C x j a b hj hab ha hb hor
      have zeros : wval C x a = false ∧ wval C x b = false := by
        simpa [base] using e.symm
      have cover : H (n+j) ⊆ H a ∪ H b := by
        intro v hv
        obtain ⟨hs,_,hp⟩ := Finset.mem_filter.mp hv
        rw [wval_or C (p v) j a b hj hab ha hb hor, Bool.or_eq_true] at hp
        exact hp.elim (fun h => Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hs,zeros.1,h⟩))
          (fun h => Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hs,zeros.2,h⟩))
      by_cases ab : H a ⊆ H b
      · exact one b hb (cover.trans (Finset.union_subset ab (fun _ h => h)))
      by_cases ba : H b ⊆ H a
      · exact one a ha (cover.trans (Finset.union_subset (fun _ h => h) ba))
      obtain ⟨h0,h1⟩ := operands C hj hab
      have mem : j ∈ charged C x p S (j+1) := by
        apply Finset.mem_filter.mpr
        exact ⟨by simp, ⟨⟨hj,by simpa [gateAt_eq C j hj] using hor⟩,base,h0 ▸ h1 ▸ ab,h0 ▸ h1 ▸ ba⟩⟩
      exact ⟨{a,b}, by simpa using And.intro ha hb, by simpa using cover,
        by simpa [mem] using Finset.card_insert_le a {b}⟩
  · apply one a ha
    intro v hv
    exact (base (Finset.mem_filter.mp hv).2.1).elim

/-- Amortized over an arbitrary set of wires, so shared subcircuits count just once. -/
theorem union_bound (hc : IsAO2 n C)
    (raw : ∀ i v, v ∈ S → x i = false → p v i = true → i = v)
    (t : ℕ) (ht : t ≤ C.gates.length) (W : Finset ℕ) (hw : ∀ w ∈ W, w < n+t) :
    (W.biUnion (hits C x p S)).card ≤ (charged C x p S t).card + W.card := by
  classical
  induction t generalizing W with
  | zero =>
    apply le_trans Finset.card_biUnion_le
    have small (i : ℕ) (hi : i ∈ W) : (hits C x p S i).card ≤ 1 := by
      let a : Fin n := ⟨i,by simpa using hw i hi⟩
      apply Finset.card_le_one.mpr
      intro v hv w hw'
      have same (v : Fin n) (hv : v ∈ hits C x p S i) : a = v := by
        obtain ⟨hs,hx,hp⟩ := Finset.mem_filter.mp hv
        exact raw a v hs ((wval_in C x a) ▸ hx) ((wval_in C (p v) a) ▸ hp)
      exact (same v hv).symm.trans (same w hw')
    simpa [charged] using Finset.sum_le_sum small
  | succ t ih =>
    have ht' : t < C.gates.length := by omega
    have grow : charged C x p S (t+1) =
        if t ∈ charged C x p S (t+1) then insert t (charged C x p S t) else charged C x p S t := by
      by_cases h : splits C x p S t <;> simp [charged,Finset.range_add_one,Finset.filter_insert,h]
    have fresh : t ∉ charged C x p S t := by simp [charged]
    by_cases used : n+t ∈ W
    · obtain ⟨K,prior,covers,arity⟩ := children C x p S hc t ht'
      let rest := W.erase (n+t)
      have hrest : ∀ w ∈ rest, w < n+t := by
        intro w h
        obtain ⟨hne,hin⟩ := Finset.mem_erase.mp h
        have := hw w hin
        omega
      have sub : W.biUnion (hits C x p S) ⊆ (rest ∪ K).biUnion (hits C x p S) := by
        intro v hv
        obtain ⟨w,hin,hv⟩ := Finset.mem_biUnion.mp hv
        by_cases eq : w = n+t
        · subst w
          obtain ⟨u,hu,hv⟩ := Finset.mem_biUnion.mp (covers hv)
          exact Finset.mem_biUnion.mpr ⟨u,Finset.mem_union_right _ hu,hv⟩
        · exact Finset.mem_biUnion.mpr ⟨w,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hin⟩),hv⟩
      have old := ih (Nat.le_of_lt ht') (rest ∪ K) (fun w hw' =>
        (Finset.mem_union.mp hw').elim (hrest w) (prior w))
      have u := Finset.card_union_le rest K
      have sz : rest.card + 1 = W.card := Finset.card_erase_add_one used
      have small := Finset.card_le_card sub
      rw [grow]
      split_ifs with h <;> simp [h,fresh] at arity ⊢ <;> omega
    · have old := ih (Nat.le_of_lt ht') W (fun w hin => by
        have := hw w hin
        have hne : w ≠ n+t := fun eq => used (eq ▸ hin)
        omega)
      rw [grow]
      split_ifs <;> simp [fresh] <;> omega

/-- A single negative test and k distinct positive probes require at least k−1 splitting ORs. -/
theorem output_bound (hc : IsAO2 n C)
    (raw : ∀ i v, v ∈ S → x i = false → p v i = true → i = v)
    (hx : circuitFun n C x = false) (hp : ∀ v ∈ S, circuitFun n C (p v) = true) :
    S.card ≤ (charged C x p S C.size).card + 1 := by
  classical
  by_cases hw : C.output < n+C.gates.length
  · have h := union_bound C x p S hc raw C.gates.length (le_refl _) {C.output} (by simpa)
    have eq : hits C x p S C.output = S := Finset.filter_true_of_mem (fun v hv => ⟨hx,hp v hv⟩)
    simpa [eq,Circuit.size] using h
  · have empty : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro v hv
      have tr : wval C (p v) C.output = true := hp v hv
      rw [wval_past C (p v) C.output (by omega)] at tr
      contradiction)
    simp [empty]

end VertexPeel.RowCharge
