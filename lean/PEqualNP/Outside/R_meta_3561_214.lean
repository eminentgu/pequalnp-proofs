import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The first two premises are the checked leaves L_meta_1922 and L_meta_2960.
set_option maxHeartbeats 1700000 in
theorem PEqualNP.Outside.R_meta_3561_214
    (raw : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5;         x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →       (15 : ℕ) ≤ x1.size)
    (theta : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x1 = fun (x3 : Fin (7 : ℕ) → Bool) => [((0 : Fin (7 : ℕ)), (1 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (2 : Fin (7 : ℕ))), ((0 : Fin (7 : ℕ)), (4 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((2 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((3 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((4 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((6 : Fin (7 : ℕ)), (3 : Fin (7 : ℕ)))].any fun (x4 : Fin (7 : ℕ) × Fin (7 : ℕ)) => x3 x4.1 && x3 x4.2) → (11 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x5 : ℕ) => Bool.true) Bool.true x4.op) x1.gates)
    (signed : let edge := fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 e))
      ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
        (∃ g ∈ C.gates, g.op = GateOp.not) →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn (Function.update x 4 false) ++ [x 0 || x 4, x 4 || x 1]) = edge x) →
        ∃ D : Circuit, FanInTwo D ∧ (circuitFun 7 D = fun (x3 : Fin (7 : ℕ) → Bool) => [((0 : Fin (7 : ℕ)), (1 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (2 : Fin (7 : ℕ))), ((0 : Fin (7 : ℕ)), (4 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((2 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((3 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((4 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((6 : Fin (7 : ℕ)), (3 : Fin (7 : ℕ)))].any fun (x4 : Fin (7 : ℕ) × Fin (7 : ℕ)) => x3 x4.1 && x3 x4.2) ∧
          List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x5 : ℕ) => Bool.true) Bool.true x4.op) D.gates ≤ 10) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (13 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn (Function.update x5 (4 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (4 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ))]) = x1 x5) → False := by
  let rows : List Nat := [3,6,12,17,24,33,42,50,66,69,104,116,132,138,160,201,208,261,264,276,288,320,385,402]
  let positives : List Nat := [3,6,12,17,24,33,66,132,160,264,288,320]
  let bits (r : Nat) : Fin 9 → Bool := fun i => r.testBit i.val
  let edge (x : Fin 9 → Bool) :=
    ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any fun e =>
      x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 e)
  let bank (k : Fin 9) (x : Fin 9 → Bool) :=
    let p := k = 0 ∨ k = 4
    List.ofFn (if p then Function.update x k false else x) ++
      [if p then x 0 || x 4 else false, if p then x k || x (if k = 0 then 3 else 1) else x 0 || x 4 || x k]
  let source (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 4]
  let From1922 : Prop := ∀ C : Circuit, Monotone2 C →
    (∀ r ∈ rows, C.eval (source (bits r)) = decide (r ∈ positives)) → 15 ≤ C.size
  let Uniform : Prop := ∀ (k : Fin 9) (C : Circuit), FanInTwo C → C.size ≤ 13 →
    (∀ h ∈ C.gates, h.op ≠ GateOp.not) → (∀ x, C.eval (bank k x) = edge x) → False

  let blank (k : Fin 9) : Nat := if k = 0 ∨ k = 4 then k.val else 9
  let redirect (k : Fin 9) (i : Nat) := if i = blank k then 24 else i
  let orGate (k : Fin 9) : Gate := ⟨.or, if k = 0 then [0,3] else if k = 4 then [4,1] else [9,k.val]⟩
  let rename (k : Fin 9) (g : Gate) : Gate := ⟨g.op,g.inputs.map (redirect k)⟩
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let restore (k : Fin 9) (C : Circuit) : Circuit :=
    ⟨orGate k :: C.gates.map (rename k), redirect k C.output⟩

  have blank_lt (k : Fin 9) : blank k < 11 := by unfold blank; split <;> omega
  have at_last (w : List Bool) (v : Bool) : (w ++ [v]).getD w.length false = v := by simp
  have at_old (w : List Bool) (v : Bool) (i : Nat) (h : i ≠ w.length) :
      (w ++ [v]).getD i false = w.getD i false := by
    by_cases hi : i < w.length
    · exact List.getD_append _ _ _ _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

  have simulation (k : Fin 9) (gs : List Gate) (w z : List Bool)
      (len : w.length = z.length) (enough : 11 ≤ w.length) (bound : w.length + gs.length ≤ 24)
      (eq : ∀ i, w.getD i false = z.getD (redirect k i) false) :
      ∀ i, (gs.foldl step w).getD i false = ((gs.map (rename k)).foldl step z).getD (redirect k i) false := by
    induction gs generalizing w z with
    | nil => exact eq
    | cons g gs ih =>
      simp only [List.map_cons,List.foldl_cons]
      have lengthW : (step w g).length = w.length + 1 := by simp [step]
      have lengthZ : (step z (rename k g)).length = z.length + 1 := by simp [step]
      have before : w.length < 24 := by simp only [List.length_cons] at bound; omega
      apply ih _ _ (by omega) (by omega) (by simp only [List.length_cons] at bound; omega)
      intro i
      have pins : g.inputs.map (fun j => w.getD j false) =
          (g.inputs.map (redirect k)).map (fun j => z.getD j false) := by
        rw [List.map_map]; exact List.map_congr_left (fun j _ => eq j)
      by_cases h : i = w.length
      · subst i
        have rid : redirect k w.length = z.length := by
          have lt := blank_lt k
          unfold redirect
          rw [if_neg (show w.length ≠ blank k by omega)]
          exact len
        rw [rid]
        change (w ++ [_]).getD w.length false = (z ++ [_]).getD z.length false
        simp only [at_last]
        simpa only [rename] using congrArg g.op.eval pins
      · have h' : redirect k i ≠ z.length := by unfold redirect; split <;> omega
        simp only [step,rename]
        rw [at_old _ _ _ h,at_old _ _ _ h',eq]

  have rows_ok : ∀ r ∈ rows, edge (bits r) = decide (r ∈ positives) := by decide +kernel
  have initial : ∀ k : Fin 9, ∀ r ∈ rows, ∀ i : Fin 11,
      (bank k (bits r)).getD i.val false =
        (step (source (bits r)) (orGate k)).getD (redirect k i.val) false := by decide +kernel

  have transport (raw : From1922) : Uniform := by
    intro k C fan sz noNot correct
    let D := restore k C
    have hmono : Monotone2 D := by
      intro g hg
      change g ∈ orGate k :: C.gates.map (rename k) at hg
      rcases List.mem_cons.mp hg with rfl | h
      · refine ⟨Or.inr rfl,?_⟩
        by_cases a : k = 0 <;> by_cases b : k = 4 <;> simp [orGate,a,b]
      · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
        obtain ⟨op,num⟩ := fan a ha
        refine ⟨?_,by simpa [rename] using num⟩
        rcases op with a | b | c
        · exact Or.inl a
        · exact Or.inr b
        · exact False.elim (noNot _ ha c)
    have eval (r : Nat) (hr : r ∈ rows) : D.eval (source (bits r)) = decide (r ∈ positives) := by
      let w := bank k (bits r)
      let z := step (source (bits r)) (orGate k)
      have hw : w.length = 11 := by simp [w,bank]
      have hz : z.length = 11 := by simp [z,step,source]
      have rel (i : Nat) : w.getD i false = z.getD (redirect k i) false := by
        by_cases hi : i < 11
        · exact initial k r hr ⟨i,hi⟩
        · have ri : redirect k i = i := by
            have lt := blank_lt k
            simp [redirect,show i ≠ blank k by omega]
          rw [ri,List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
      have sim := simulation k C.gates w z (by omega) (by omega)
        (by change C.gates.length ≤ 13 at sz; omega) rel C.output
      exact sim.symm.trans ((correct (bits r)).trans (rows_ok r hr))
    have lo := raw D hmono eval
    change 15 ≤ (orGate k :: C.gates.map (rename k)).length at lo
    simp only [List.length_cons,List.length_map] at lo
    change C.gates.length ≤ 13 at sz
    omega
  intro f C fan sz correct
  have graphEq (x : Fin 9 → Bool) : edge x = f x := by
    change (x 0 && x 1 || (x 1 && x 2 || (x 2 && x 3 || (x 3 && x 4 || (x 4 && x 0 || (x 0 && x 5 || (x 1 && x 6 || (x 2 && x 7 || (x 3 && x 8 || (x 5 && x 7 || (x 6 && x 8 || (x 8 && x 5 || false)))))))))))) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
    simp only [Bool.or_assoc, Bool.or_false]
  have exactBank (x : Fin 9 → Bool) : C.eval (List.ofFn (Function.update x 4 false) ++ [x 0 || x 4, x 4 || x 1]) = edge x :=
    (correct x).trans (graphEq x).symm
  by_cases pure : ∀ g ∈ C.gates, g.op ≠ GateOp.not
  · exact transport raw 4 C fan sz pure exactBank
  · push_neg at pure
    have witness := signed C fan sz pure exactBank
    have upper := witness.choose_spec.2.2
    have lower := theta witness.choose witness.choose_spec.1 witness.choose_spec.2.1
    omega
