import Mathlib.Data.List.GetD
import Mathlib.Tactic.Push
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The first child is the previously checked step L-meta-2913.
-- The second child ranges over bounded addresses and outputs of genuine gates.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3277_99
  (known : ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     x1 = [] ∨ x1.headD (10 : ℕ) = (0 : ℕ) ∨ (9 : ℕ) ≤ x1.headD (10 : ℕ) →       ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.FanInTwo x4 →           x4.size ≤ (13 : ℕ) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];               x4.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))))
  (search : ∀ j ∈ ([1,2,3,4,6] : List (Fin 9)), ∀ D : Circuit,
    FanInTwo D → D.size ≤ 13 → (∀ g ∈ D.gates, ∀ p ∈ g.inputs, p ≤ 24) →
    (∀ g ∈ D.gates, g.op = .not → g.inputs.length ≤ 1) →
    11 ≤ D.output → D.output < 11 + D.size →
    (∃ g ∈ D.gates, 10 ∈ g.inputs) → (∃ g ∈ D.gates, j.val ∈ g.inputs) →
    ∃ x : Fin 9 → Bool, D.eval ((List.ofFn x ++ [!x 0]) ++ [x j && !x 0]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
  ∀ x1 ∈ [((1 : Fin (12 : ℕ)), (9 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (9 : Fin (12 : ℕ))), ((3 : Fin (12 : ℕ)), (9 : Fin (12 : ℕ))), ((4 : Fin (12 : ℕ)), (9 : Fin (12 : ℕ))), ((6 : Fin (12 : ℕ)), (9 : Fin (12 : ℕ)))],   ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x6 : Fin (9 : ℕ) → Bool),           have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];           have x8 : Fin (12 : ℕ) → Bool := fun (x8 : Fin (12 : ℕ)) => if x8 = (11 : Fin (12 : ℕ)) then Bool.true else x7.getD (↑x8) Bool.false;           x3.eval (x7 ++ [x8 x1.1 && x8 x1.2]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  classical
  let F := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let seed (j : Fin 9) (x : Fin 9 → Bool) := (List.ofFn x ++ [!x 0]) ++ [x j && !x 0]
  have lens (j : Fin 9) (x : Fin 9 → Bool) : (seed j x).length = 11 := by simp [seed]
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]
  have lengthRun (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      change (gs.foldl step (step w g)).length = _
      rw [ih (step w g)]
      simp [step]
      omega
  have inputRead (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
      (gs.foldl step w).getD k false = w.getD k false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (gs.foldl step (step w g)).getD k false = _
      rw [ih (step w g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hk
  have ignoreRead (q : ℕ) (gs : List Gate) (u v : List Bool) (len : u.length = v.length)
      (agree : ∀ k, k ≠ q → u.getD k false = v.getD k false)
      (unused : ∀ g ∈ gs, q ∉ g.inputs) :
      ∀ k, k ≠ q → (gs.foldl step u).getD k false = (gs.foldl step v).getD k false := by
    induction gs generalizing u v with
    | nil => exact agree
    | cons g gs ih =>
      have vals : g.inputs.map (fun k => u.getD k false) =
          g.inputs.map (fun k => v.getD k false) := by
        apply List.map_congr_left
        intro k hk
        exact agree k (fun e => unused g (by simp) (e ▸ hk))
      apply ih (step u g) (step v g) (by simp [step,len]) _ (fun h hh => unused h (by simp [hh]))
      intro k hk
      by_cases lt : k < u.length
      · simpa only [step,List.getD_append _ _ _ _ lt,
          List.getD_append _ _ _ _ (show k < v.length by omega)] using agree k hk
      · simp only [step, List.getD_append_right _ _ _ _ (show u.length ≤ k by omega),
          List.getD_append_right _ _ _ _ (show v.length ≤ k by omega),len,vals]
  let trim (g : Gate) := g.inputs.take
    (bif GateOp.rec false false true (fun _ => false) false g.op then 1 else g.inputs.length)
  have trimLen (g : Gate) : (trim g).length ≤ g.inputs.length := by
    cases g with
    | mk op ins => cases op <;> simp [trim]
  have trimValue (g : Gate) (w : List Bool) :
      g.op.eval ((trim g).map fun k => w.getD k false) = g.op.eval (g.inputs.map fun k => w.getD k false) := by
    cases g with
    | mk op ins =>
      cases op <;> simp [trim]
      cases ins <;> rfl
  let cap (g : Gate) : Gate := ⟨g.op, (trim g).map (fun k => min k 24)⟩
  have norm (gs : List Gate) (w : List Bool) (budget : gs.length + w.length ≤ 24) :
      (gs.map cap).foldl step w = gs.foldl step w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      have samestep : step w (cap g) = step w g := by
        have vals : (trim g).map (fun k => w.getD (min k 24) false) =
            (trim g).map (fun k => w.getD k false) := by
          apply List.map_congr_left
          intro k hk
          by_cases le : k ≤ 24
          · simp [Nat.min_eq_left le]
          · rw [Nat.min_eq_right (by omega), List.getD_eq_default _ _ (by omega),
              List.getD_eq_default _ _ (by omega)]
        simp only [step,cap,List.map_map,Function.comp_def,vals,trimValue]
      change (gs.map cap).foldl step (step w (cap g)) = gs.foldl step (step w g)
      rw [samestep]
      apply ih
      simp only [List.length_cons] at budget
      simp [step]
      omega
  have direct : ∀ j ∈ ([1,2,3,4,6] : List (Fin 9)), ∀ k : Fin 11, ∃ v : Fin 10,
      let x := fun i : Fin 9 => decide (i.val = v.val)
      (seed j x).getD k.val false ≠ F x := by decide
  have pairs : ∀ j ∈ ([1,2,3,4,6] : List (Fin 9)), ∃ a : Fin 9,
      let x := fun i : Fin 9 => decide (i = 0 ∨ i = a)
      let y := fun i : Fin 9 => decide (i = 0 ∨ i = a ∨ i = j)
      F x ≠ F y ∧ ∀ k : Fin 11, k.val ≠ j.val → (seed j x).getD k.val false = (seed j y).getD k.val false := by decide
  have aux (j : Fin 9) (hj : j ∈ [1,2,3,4,6]) (C : Circuit) (fan : FanInTwo C) (small : C.size ≤ 13) :
      ∃ x : Fin 9 → Bool, C.eval (seed j x) ≠ F x := by
    by_contra! all
    let D : Circuit := ⟨C.gates.map cap,C.output⟩
    have Dsize : D.size = C.size := by
      change (C.gates.map cap).length = C.gates.length
      exact List.length_map ..
    have Dfan : FanInTwo D := by
      intro g hg
      obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hg
      obtain ⟨hop,hl⟩ := fan h hh
      exact ⟨hop,by simpa only [cap,List.length_map] using (trimLen h).trans hl⟩
    have unary : ∀ g ∈ D.gates, g.op = .not → g.inputs.length ≤ 1 := by
      intro g hg hop
      obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hg
      change h.op = .not at hop
      simp [cap,trim,hop]
    have bound : ∀ g ∈ D.gates, ∀ p ∈ g.inputs, p ≤ 24 := by
      intro g hg p hp
      obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hg
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
      exact Nat.min_le_right _ _
    have correct (x : Fin 9 → Bool) : D.eval (seed j x) = F x := by
      have hN := norm C.gates (seed j x) (by rw [lens]; change C.gates.length ≤ 13 at small; omega)
      change ((C.gates.map cap).foldl step (seed j x)).getD C.output false = _
      rw [hN]
      exact all x
    have low : 11 ≤ D.output := by
      by_contra! h
      obtain ⟨v,hv⟩ := direct j hj ⟨D.output,h⟩
      let x := fun i : Fin 9 => decide (i.val = v.val)
      apply hv
      exact (inputRead D.gates (seed j x) D.output (by rw [lens]; omega)).symm.trans (correct x)
    have high : D.output < 11 + D.size := by
      by_contra! h
      let x := fun _ : Fin 9 => true
      have cx := correct x
      change (D.gates.foldl step (seed j x)).getD D.output false = F x at cx
      have past : (D.gates.foldl step (seed j x)).length ≤ D.output := by
        rw [lengthRun, lens j x]
        exact h
      rw [List.getD_eq_default _ _ past] at cx
      exact Bool.false_ne_true cx
    have use10 : ∃ g ∈ D.gates, 10 ∈ g.inputs := by
      by_contra! hn
      obtain ⟨x,hx⟩ := known [] (by decide) (Or.inl rfl) D Dfan (Dsize ▸ small)
      let w := List.ofFn x ++ [!x 0]
      have lw : w.length = 10 := by simp [w]
      change D.eval (w ++ [true]) ≠ F x at hx
      apply hx
      refine Eq.trans ?_ (correct x)
      apply ignoreRead 10 D.gates (w ++ [true]) (seed j x) (by simp [seed,w]) _ hn _ (by omega)
      intro k hk
      change (w ++ [true]).getD k false = (w ++ [x j && !x 0]).getD k false
      by_cases h : k < w.length
      · rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ h]
      · rw [List.getD_eq_default _ _ (by simpa [lw] using (show 11 ≤ k by omega)),
          List.getD_eq_default _ _ (by simpa [lw] using (show 11 ≤ k by omega))]
    have usej : ∃ g ∈ D.gates, j.val ∈ g.inputs := by
      by_contra! hn
      obtain ⟨a,sep,agreement⟩ := pairs j hj
      let x := fun i : Fin 9 => decide (i = 0 ∨ i = a)
      let y := fun i : Fin 9 => decide (i = 0 ∨ i = a ∨ i = j)
      apply sep
      change F x = F y
      rw [← correct x,← correct y]
      apply ignoreRead j.val D.gates (seed j x) (seed j y) (by rw [lens,lens]) _ hn _ (by omega)
      intro k hk
      by_cases h : k < 11
      · exact agreement ⟨k,h⟩ hk
      · rw [List.getD_eq_default _ _ (by rw [lens]; omega),List.getD_eq_default _ _ (by rw [lens]; omega)]
    obtain ⟨x,hx⟩ := search j hj D Dfan (Dsize ▸ small) bound unary low high use10 usej
    exact hx (correct x)
  intro p hp C hf hs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact aux 1 (by decide) C hf hs
  · exact aux 2 (by decide) C hf hs
  · exact aux 3 (by decide) C hf hs
  · exact aux 4 (by decide) C hf hs
  · exact aux 6 (by decide) C hf hs
