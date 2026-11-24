import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The input relabeling in the last two cases is the checked R_meta_2836_271.
set_option maxHeartbeats 1400000 in
theorem PEqualNP.Outside.R_meta_2836_412
    (monotone : let f := fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 e))
      let bank := fun (k : Fin 9) (x : Fin 9 → Bool) =>
        let p := k = 0 ∨ k = 4
        List.ofFn (if p then Function.update x k false else x) ++
          [if p then x 0 || x 4 else false, if p then x k || x (if k = 0 then 3 else 1) else x 0 || x 4 || x k]
      ∀ (k : Fin 9) (C : Circuit), FanInTwo C → C.size ≤ 13 →
        (∀ h ∈ C.gates, h.op ≠ GateOp.not) → (∀ x, C.eval (bank k x) = f x) → False)
    (pinTwo : let f := fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 e))
      let bank := fun (k : Fin 9) (x : Fin 9 → Bool) =>
        let p := k = 0 ∨ k = 4
        List.ofFn (if p then Function.update x k false else x) ++
          [if p then x 0 || x 4 else false, if p then x k || x (if k = 0 then 3 else 1) else x 0 || x 4 || x k]
      let q := fun x : Fin 9 → Bool => f (Function.update (Function.update x 0 false) 4 false)
      ∀ (k : Fin 9) (C : Circuit), FanInTwo C → C.size ≤ 13 →
        (∃ h ∈ C.gates, h.op = GateOp.not) → (∀ x, C.eval (bank k x) = f x) →
        ∃ D : Circuit, FanInTwo D ∧ D.gates.countP (fun h => h.op.ctorIdx != GateOp.not.ctorIdx) ≤ 10 ∧ (∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = q x))
    (thetaBound : let f := fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 e))
      let q := fun x : Fin 9 → Bool => f (Function.update (Function.update x 0 false) 4 false)
      ∀ D : Circuit, FanInTwo D ∧ D.gates.countP (fun h => h.op.ctorIdx != GateOp.not.ctorIdx) ≤ 10 ∧ (∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = q x) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : (Fin (9 : ℕ) → Bool) → Bool := fun (x2 : Fin (9 : ℕ) → Bool) => x2 (0 : Fin (9 : ℕ)) && x2 (1 : Fin (9 : ℕ)) || x2 (1 : Fin (9 : ℕ)) && x2 (2 : Fin (9 : ℕ)) || x2 (2 : Fin (9 : ℕ)) && x2 (3 : Fin (9 : ℕ)) || x2 (3 : Fin (9 : ℕ)) && x2 (4 : Fin (9 : ℕ)) || x2 (4 : Fin (9 : ℕ)) && x2 (0 : Fin (9 : ℕ)) || x2 (0 : Fin (9 : ℕ)) && x2 (5 : Fin (9 : ℕ)) || x2 (1 : Fin (9 : ℕ)) && x2 (6 : Fin (9 : ℕ)) || x2 (2 : Fin (9 : ℕ)) && x2 (7 : Fin (9 : ℕ)) || x2 (3 : Fin (9 : ℕ)) && x2 (8 : Fin (9 : ℕ)) || x2 (5 : Fin (9 : ℕ)) && x2 (7 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ)) && x2 (8 : Fin (9 : ℕ)) || x2 (8 : Fin (9 : ℕ)) && x2 (5 : Fin (9 : ℕ));   PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (13 : ℕ) → ((∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn (Function.update x5 (0 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))]) = x2 x5) ∨ (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn (Function.update x5 (4 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (4 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ))]) = x2 x5) ∨ (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn (Function.update x5 (4 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (4 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ))]) = x2 x5) ∨ ∃ (x5 : Fin (9 : ℕ)), x5 ≠ (0 : Fin (9 : ℕ)) ∧ x5 ≠ (4 : Fin (9 : ℕ)) ∧ ∀ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x6 ++ [Bool.false, x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) || x6 x5]) = x2 x6) → False := by
  intro C f hfan hsize cases
  let graph := fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 e))
  let bank := fun (k : Fin 9) (x : Fin 9 → Bool) =>
        let p := k = 0 ∨ k = 4
        List.ofFn (if p then Function.update x k false else x) ++
          [if p then x 0 || x 4 else false, if p then x k || x (if k = 0 then 3 else 1) else x 0 || x 4 || x k]
  have graphEq (x : Fin 9 → Bool) : graph x = f x := by
    change (x 0 && x 1 || (x 1 && x 2 || (x 2 && x 3 || (x 3 && x 4 || (x 4 && x 0 || (x 0 && x 5 || (x 1 && x 6 || (x 2 && x 7 || (x 3 && x 8 || (x 5 && x 7 || (x 6 && x 8 || (x 8 && x 5 || false)))))))))))) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
    simp only [Bool.or_assoc, Bool.or_false]
  have forbid (k : Fin 9) (D : Circuit) (hf : FanInTwo D) (hs : D.size ≤ 13)
      (hg : ∀ x, D.eval (bank k x) = graph x) : False := by
    by_cases h : ∀ g ∈ D.gates, g.op ≠ GateOp.not
    · exact monotone k D hf hs h hg
    · push_neg at h
      have witness := pinTwo k D hf hs h hg
      exact thetaBound witness.choose witness.choose_spec
  have noFirst (D : Circuit) (hf : FanInTwo D) (hs : D.size ≤ 13)
      (hg : ∀ x : Fin 9 → Bool, D.eval (List.ofFn (Function.update x 0 false) ++ [x 0 || x 4, x 0 || x 3]) = f x) : False := by
    apply forbid 0 D hf hs
    intro x
    exact (hg x).trans (graphEq x).symm
  have noSecond (D : Circuit) (hf : FanInTwo D) (hs : D.size ≤ 13)
      (hg : ∀ x : Fin 9 → Bool, D.eval (List.ofFn (Function.update x 4 false) ++ [x 0 || x 4, x 4 || x 1]) = f x) : False := by
    apply forbid 4 D hf hs
    intro x
    exact (hg x).trans (graphEq x).symm
  have noTriple (k : Fin 9) (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 6)
      (D : Circuit) (hf : FanInTwo D) (hs : D.size ≤ 13)
      (hg : ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [false, x 0 || x 4 || x k]) = f x) : False := by
    have hn : ¬(k = 0 ∨ k = 4) := by
      rcases hk with h|h|h|h <;> subst k <;> decide
    apply forbid k D hf hs
    intro x
    simpa only [bank, if_neg hn] using (hg x).trans (graphEq x).symm
  apply cases.elim (noFirst C hfan hsize)
  intro rest
  apply rest.elim (noSecond C hfan hsize)
  intro remain
  let σ : Fin 9 → Fin 9 := ![0, 5, 8, 3, 4, 1, 7, 6, 2]
  let ρ (i : ℕ) : ℕ := if h : i < 9 then (σ ⟨i,h⟩).val else i
  have ρ_small (i : ℕ) (hi : i < 9) : ρ i < 9 := by simp [ρ, hi]
  have ρ_fix (i : ℕ) (hi : 9 ≤ i) : ρ i = i := by simp [ρ, Nat.not_lt.mpr hi]
  have sym (x : Fin 9 → Bool) : f (x ∘ σ) = f x := by
    change (x 0 && x 5 || x 5 && x 8 || x 8 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 1 || x 5 && x 7 || x 8 && x 6 || x 3 && x 2 || x 1 && x 6 || x 7 && x 2 || x 2 && x 1) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
    simp only [Bool.and_comm, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]
  have upd (x : Fin 9 → Bool) :
      Function.update (x ∘ σ) 4 false = Function.update x 4 false ∘ σ := by
    funext i
    fin_cases i <;> rfl
  let renameGate (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩
  let D : Circuit := ⟨C.gates.map renameGate, ρ C.output⟩
  have fanD : FanInTwo D := by
    intro g hg
    change g ∈ C.gates.map renameGate at hg
    obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hg
    obtain ⟨hop,hlen⟩ := hfan h hh
    exact ⟨hop, by simpa only [renameGate, List.length_map] using hlen⟩
  have sizeD : D.size ≤ 13 := by
    change (C.gates.map renameGate).length ≤ 13
    rw [List.length_map]
    exact hsize
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have last (w : List Bool) (a : Bool) : (w ++ [a]).getD w.length false = a := by
    simp [List.getD_eq_getElem?_getD]
  have old (w : List Bool) (a : Bool) (i : ℕ) (h : i ≠ w.length) :
      (w ++ [a]).getD i false = w.getD i false := by
    by_cases hi : i < w.length
    · exact List.getD_append _ _ _ _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  have simulate (gs : List Gate) (w z : List Bool) (len : w.length = z.length)
      (enough : 9 ≤ w.length) (eq : ∀ i, w.getD i false = z.getD (ρ i) false) :
      ∀ i, (gs.foldl step w).getD i false =
        ((gs.map renameGate).foldl step z).getD (ρ i) false := by
    induction gs generalizing w z with
    | nil => exact eq
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons]
      apply ih
      · simp only [step, List.length_append, List.length_cons, List.length_nil, len]
      · simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      intro i
      have pins : g.inputs.map (fun j => w.getD j false) =
          (g.inputs.map ρ).map (fun j => z.getD j false) := by
        rw [List.map_map]
        exact List.map_congr_left (fun j _ => eq j)
      by_cases hi : i = w.length
      · rw [hi, ρ_fix _ enough]
        conv_rhs => rw [len]
        simp only [step, renameGate, last]
        rw [pins]
      · have hj : ρ i ≠ z.length := by
          intro he
          by_cases small : i < 9
          · have lt := ρ_small i small
            omega
          · rw [ρ_fix i (by omega)] at he
            omega
        simp only [step, renameGate]
        rw [old _ _ _ hi, old _ _ _ hj, eq]
  have transfer (x : Fin 9 → Bool) (a b : Bool) :
      C.eval (List.ofFn (x ∘ σ) ++ [a,b]) = D.eval (List.ofFn x ++ [a,b]) := by
    apply simulate
    · simp
    · simp
    intro i
    by_cases hi : i < 9
    · have hr := ρ_small i hi
      rw [List.getD_append _ _ _ _ (by simpa using hi),
          List.getD_append _ _ _ _ (by simpa using hr)]
      rw [List.getD_eq_getElem _ _ (by simpa using hi),
          List.getD_eq_getElem _ _ (by simpa using hr)]
      simp only [List.getElem_ofFn, ρ, dif_pos hi, Function.comp_apply]
    · rw [ρ_fix i (by omega),
          List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_lt hi),
          List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_lt hi)]
      simp only [List.length_ofFn]
  rcases remain with third | fourth
  · apply noSecond D fanD sizeD
    intro x
    change D.eval (List.ofFn (Function.update x 4 false) ++ [x 0 || x 4, x 4 || x 1]) = f x
    rw [← transfer (Function.update x 4 false)]
    have h := third (x ∘ σ)
    rw [upd x] at h
    exact h.trans (sym x)
  · obtain ⟨k,h0,h4,h⟩ := fourth
    have reps : (k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 6) ∨
        (σ k = 1 ∨ σ k = 2 ∨ σ k = 3 ∨ σ k = 6) := by
      fin_cases k <;> first | exact (h0 rfl).elim | exact (h4 rfl).elim | decide
    rcases reps with own | swapped
    · exact noTriple k own C hfan hsize h
    · apply noTriple (σ k) swapped D fanD sizeD
      intro x
      rw [← transfer x]
      exact (h (x ∘ σ)).trans (sym x)
