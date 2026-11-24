import Mathlib
import PEqualNP.Defs

/-! The bypass and final-gate primitives and their lemmas below are extracted
from the merged upstream L_meta_1485. -/
namespace PEqualNP.Research2583.SafeOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2

lemma val_prefix {n : ℕ} {C D : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
    (hmC : m ≤ C.gates.length) (hmD : m ≤ D.gates.length)
    (hg : ∀ k < m, gateAt D k = gateAt C k) : ∀ u, u < n + m → val D x u = val C x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases hun : u < n
    · rw [val_input hx hun, val_input hx hun]
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < m := by omega
      rw [val_gate hx (by omega), val_gate hx (by omega), hg k hk]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + k
      · rw [ite_eq_left hi, ite_eq_left hi]; exact ih i hi (by omega)
      · rw [ite_eq_right hi, ite_eq_right hi]

def aliasWire (w i u : ℕ) : ℕ := if u = w then i else if w < u then u - 1 else u

def aliasGate (w i : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire w i)⟩

def bypass (n : ℕ) (C : Circuit) (r i : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (fun k =>
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1))),
    aliasWire (n + r) i C.output⟩

lemma bypass_length (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).gates.length = C.gates.length - 1 := by simp [bypass]

lemma bypass_output (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).output = aliasWire (n + r) i C.output := rfl

lemma gateAt_bypass {n : ℕ} {C : Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
    gateAt (bypass n C r i) k =
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1)) := by
  have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
  rw [gateAt_eq hk']
  simp [bypass]

lemma bypass_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
    (hr : r < C.gates.length) : ∀ u, u < n + r → val (bypass n C r i) x u = val C x u := by
  apply val_prefix hx (by omega) (by rw [bypass_length]; omega)
  intro k hk
  rw [gateAt_bypass (by omega), ite_eq_left hk]

lemma aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp [aliasWire]

lemma aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
  unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_right (by omega)]

lemma aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
  unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_left hu]

lemma bypass_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : (∃ k, k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs) →
      R (val C x (n + r)) (val C x i)) :
    ∀ u, u ≠ n + r → R (val C x u) (val (bypass n C r i) x (aliasWire (n + r) i u)) := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hne
    by_cases hlt : u < n + r
    · rw [aliasWire_lt_self hlt, bypass_val_lt hx hr u hlt]; exact hrefl _
    · rw [aliasWire_gt_self (by omega)]
      by_cases hge : n + C.gates.length ≤ u
      · rw [val_ge hx hge, val_ge hx (by rw [bypass_length]; omega)]; exact hrefl _
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + (k + 1) := ⟨u - n - 1, by omega⟩
        have hk1 : k + 1 < C.gates.length := by omega
        have hkr : ¬ k < r := by omega
        have e : n + (k + 1) - 1 = n + k := by omega
        rw [e, val_gate hx hk1, val_gate hx (by rw [bypass_length]; omega),
          gateAt_bypass (by omega), ite_eq_right hkr]
        simp only [aliasGate, List.map_map]
        refine hmono _ (hAO _ hk1) _ _ _ ?_
        intro i' hi'
        simp only [Function.comp_apply]
        by_cases h1 : i' = n + r
        · subst h1
          rw [aliasWire_self, ite_eq_left (by omega)]
          have hgi : (if i < n + k then val (bypass n C r i) x i else false) = val C x i := by
            rcases hi with hi | hi
            · rw [ite_eq_left (by omega), bypass_val_lt hx hr i hi]
            · rw [ite_eq_right (by omega), val_ge hx hi]
          rw [hgi]
          exact hR ⟨k + 1, hk1, hi'⟩
        · by_cases h2 : i' < n + r
          · rw [aliasWire_lt_self h2, ite_eq_left (by omega), ite_eq_left (by omega),
              bypass_val_lt hx hr i' h2]
            exact hrefl _
          · by_cases h3 : i' < n + (k + 1)
            · have key := ih i' h3 h1
              rw [aliasWire_gt_self (by omega)] at key
              rw [aliasWire_gt_self (by omega), ite_eq_left h3, ite_eq_left (by omega)]
              exact key
            · rw [aliasWire_gt_self (by omega), ite_eq_right h3, ite_eq_right (by omega)]
              exact hrefl _

lemma bypass_eval_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : R (val C x (n + r)) (val C x i)) :
    R (C.eval x) ((bypass n C r i).eval x) := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  by_cases h : C.output = n + r
  · have hgi : val (bypass n C r i) x i = val C x i := by
      rcases hi with hi | hi
      · exact bypass_val_lt hx hr i hi
      · rw [val_ge hx hi, val_ge hx (by rw [bypass_length]; omega)]
    rw [h, aliasWire_self, hgi]; exact hR
  · exact bypass_rel hrefl hmono hx hAO hr hi (fun _ => hR) _ h

lemma bypass_eval_eq {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : val C x (n + r) = val C x i) :
    (bypass n C r i).eval x = C.eval x :=
  (bypass_eval_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi hR).symm

lemma bypass_eval_unread {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hout : C.output ≠ n + r)
    (hno : ∀ k < C.gates.length, n + r ∉ (gateAt C k).inputs) :
    (bypass n C r i).eval x = C.eval x := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  exact (bypass_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi
    (fun ⟨k, hk, hm⟩ => absurd hm (hno k hk)) _ hout).symm

lemma bypass_AO {n : ℕ} {C : Circuit} {r i : ℕ} (hr : r < C.gates.length)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
    ∀ k < (bypass n C r i).gates.length,
      (gateAt (bypass n C r i) k).op = GateOp.and ∨
        (gateAt (bypass n C r i) k).op = GateOp.or := by
  intro k hk
  rw [bypass_length] at hk
  rw [gateAt_bypass hk]
  split_ifs with h
  · exact hAO k (by omega)
  · exact hAO (k + 1) (by omega)

lemma bypass_mem {n : ℕ} {C : Circuit} {r i : ℕ} :
    ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧
      g.inputs.length = g'.inputs.length := by
  intro g hg
  simp only [bypass, List.mem_map, List.mem_range] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  split_ifs with h
  · exact ⟨gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
  · exact ⟨gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp [aliasGate]⟩

lemma aliasWire_lt {w i u m : ℕ} (hi : i < w) (hwm : w ≤ m) (hu : u < m + 1) :
    aliasWire w i u < m := by
  unfold aliasWire; split_ifs <;> omega

lemma bypass_readsBack {n : ℕ} {C : Circuit} {r i : ℕ} (hi : i < n + r)
    (hRB : ∀ k < C.gates.length, ∀ u ∈ (gateAt C k).inputs, u < n + k) :
    ∀ k < (bypass n C r i).gates.length,
      ∀ u ∈ (gateAt (bypass n C r i) k).inputs, u < n + k := by
  intro k hk u hu
  rw [bypass_length] at hk
  rw [gateAt_bypass hk] at hu
  split_ifs at hu with h
  · exact hRB k (by omega) u hu
  · simp only [aliasGate, List.mem_map] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    have := hRB (k + 1) (by omega) u' hu'
    exact aliasWire_lt hi (by omega) (by omega)

def addTop (n : ℕ) (C : Circuit) (g : Gate) : Circuit :=
  ⟨C.gates ++ [g], n + C.gates.length⟩

lemma addTop_length (n : ℕ) (C : Circuit) (g : Gate) :
    (addTop n C g).gates.length = C.gates.length + 1 := by simp [addTop]

lemma addTop_eval {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) (g : Gate) :
    (addTop n C g).eval x = g.op.eval (g.inputs.map fun i => val C x i) := by
  have hl : (C.gates.foldl stepWire x).length = n + C.gates.length := by
    rw [foldl_length, hx]
  simp only [Circuit.eval, addTop, wires_eq_foldl, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  rw [← hl]
  simp [stepWire, List.getD_eq_getElem?_getD, val, wires_eq_foldl]

lemma gateAt_addTop_lt {n : ℕ} {C : Circuit} {g : Gate} {k : ℕ} (hk : k < C.gates.length) :
    gateAt (addTop n C g) k = gateAt C k := by
  simp [gateAt, addTop, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma gateAt_addTop_len {n : ℕ} {C : Circuit} {g : Gate} :
    gateAt (addTop n C g) C.gates.length = g := by
  simp [gateAt, addTop, List.getD_eq_getElem?_getD]

lemma addTop_readsBack {n : ℕ} {C : Circuit} {g : Gate}
    (hg : ∀ u ∈ g.inputs, u < n + C.gates.length)
    (hRB : ∀ k < C.gates.length, ∀ u ∈ (gateAt C k).inputs, u < n + k) :
    ∀ k < (addTop n C g).gates.length, ∀ u ∈ (gateAt (addTop n C g) k).inputs, u < n + k := by
  intro k hk u hu
  rw [addTop_length] at hk
  by_cases h : k < C.gates.length
  · rw [gateAt_addTop_lt h] at hu; exact hRB k h u hu
  · have hkk : k = C.gates.length := by omega
    subst hkk
    rw [gateAt_addTop_len] at hu
    exact hg u hu

lemma addTop_mem {n : ℕ} {C : Circuit} {g : Gate} :
    ∀ g' ∈ (addTop n C g).gates, g' ∈ C.gates ∨ g' = g := by
  intro g' hg'
  simpa [addTop] using hg'

open PEqualNP.MetaComplexity PEqualNP.TopForm

/-- Delete the OR at index r, redirect every use of its result to its second
operand, then place an OR with its first operand on the output. -/
def promote (n : Nat) (C : Circuit) (r u v : Nat) : Circuit :=
  let D := bypass n C r v
  addTop n D ⟨.or,[D.output,u]⟩

lemma promoted_eq (n : Nat) (C : Circuit) {r u v : Nat} (hr : r < C.gates.length)
    (earlier : u < n+r) (x : Fin n → Bool) :
    circuitFun n (promote n C r u v) x =
      (circuitFun n (bypass n C r v) x || val C (List.ofFn x) u) := by
  change (addTop n _ _).eval (List.ofFn x) = _
  rw [addTop_eval (by simp)]
  change (val (bypass n C r v) (List.ofFn x) (bypass n C r v).output ||
      (val (bypass n C r v) (List.ofFn x) u || false)) = _
  rw [Bool.or_false,bypass_val_lt (by simp) hr u earlier]
  rfl

/-- The exact condition for exposing the tapped wire at the output. Its value
is preserved because the tapped wire precedes the gate being deleted. -/
theorem promotion_iff (n : Nat) (C : Circuit) (ao : IsAO2 n C) {r u v : Nat}
    (hr : r < C.gates.length) (gor : gateAt C r = ⟨.or,[u,v]⟩) :
    circuitFun n (promote n C r u v) = circuitFun n C ↔
      ∀ x : Fin n → Bool, val C (List.ofFn x) u = true → circuitFun n C x = true := by
  have before := ao.2.1 r hr
  rw [gor] at before
  have hu := before u (by simp)
  have hv := before v (by simp)
  have ops (j : Nat) (hj : j < C.gates.length) := ao.1 _ (gateAt_mem hj)
  constructor
  · intro eq x tap
    have h := congrFun eq x
    rw [promoted_eq n C hr hu x,tap,Bool.or_true] at h
    exact h.symm
  · intro safe
    funext x
    rw [promoted_eq n C hr hu x]
    cases tap : val C (List.ofFn x) u with
    | true => rw [Bool.or_true,safe x tap]
    | false =>
      rw [Bool.or_false]
      apply bypass_eval_eq (by simp) ops hr (Or.inl hv)
      rw [val_gate (by simp) hr, gor]
      simp [GateOp.eval,hu,hv,tap]

lemma promotion_size (n : Nat) (C : Circuit) {r u v : Nat} (hr : r < C.gates.length) :
    (promote n C r u v).size = C.size := by
  change (addTop n (bypass n C r v) _).gates.length = C.gates.length
  rw [addTop_length, bypass_length]; omega

lemma promotion_AO2 (n : Nat) (C : Circuit) (ao : IsAO2 n C) {r u v : Nat}
    (hr : r < C.gates.length) (gor : gateAt C r = ⟨.or,[u,v]⟩)
    (hout : C.output < n + C.gates.length) : IsAO2 n (promote n C r u v) := by
  have before := ao.2.1 r hr
  rw [gor] at before
  have hu := before u (by simp)
  have hv := before v (by simp)
  let D := bypass n C r v
  let g : Gate := ⟨.or,[D.output,u]⟩
  have source (a : Gate) (h : a ∈ D.gates) := @bypass_mem n C r v a h
  have dlen : D.gates.length = C.gates.length - 1 := bypass_length _ _ _ _
  have finalPins : ∀ w ∈ g.inputs, w < n+D.gates.length := by
    intro w hw; change w ∈ [D.output,u] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rw [dlen]
    rcases hw with rfl|rfl
    · change aliasWire (n+r) v C.output < _
      apply aliasWire_lt hv (by omega) (by omega)
    · omega
  refine ⟨?_,addTop_readsBack finalPins (bypass_readsBack hv ao.2.1),?_⟩
  · intro a h; rcases addTop_mem a h with h|rfl
    · obtain ⟨b,hb,op,_⟩ := source a h
      rw [op]; exact ao.1 _ hb
    · exact Or.inr rfl
  · intro a h; rcases addTop_mem a h with h|rfl
    · obtain ⟨b,hb,_,arity⟩ := source a h
      rw [arity]; exact ao.2.2 _ hb
    · rfl

/-- A circuit with an accepting input has a valid output address, as required
when an old output is used as a new gate operand. -/
lemma valid_output_of_accepts (n : Nat) (C : Circuit) {x : Fin n → Bool}
    (h : circuitFun n C x = true) : C.output < n + C.gates.length := by
  by_contra! bad
  have e := val_ge (C:=C) (x:=List.ofFn x) (by simp : (List.ofFn x).length = n) bad
  change val C (List.ofFn x) C.output = true at h
  rw [e] at h; contradiction

/-- With a unique old reader, the retained wire is used only by the new top
OR. Other gates can still share ancestors of the retained wire. -/
theorem no_earlier_readers (n : Nat) (C : Circuit) {r u v : Nat} (hr : r < C.gates.length)
    (before : u < n+r) (diff : v ≠ u)
    (only : ∀ j < C.gates.length, u ∈ (gateAt C j).inputs → j = r) :
    ∀ k < C.gates.length-1, u ∉ (gateAt (promote n C r u v) k).inputs := by
  intro k hk seen
  have short : k < (bypass n C r v).gates.length := by rw [bypass_length]; exact hk
  rw [promote, gateAt_addTop_lt short, gateAt_bypass hk] at seen
  split_ifs at seen with pre
  · have e := only k (by omega) seen; omega
  · obtain ⟨w,hw,he⟩ := List.mem_map.mp seen
    have wEq : w = u := by
      unfold aliasWire at he
      split_ifs at he <;> omega
    subst w
    have e := only (k+1) (by omega) hw; omega

#print axioms promotion_iff
#print axioms promotion_AO2
#print axioms no_earlier_readers
end PEqualNP.Research2583.SafeOr
