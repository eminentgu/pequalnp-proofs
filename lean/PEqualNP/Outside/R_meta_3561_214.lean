import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The first two premises are the checked leaves L_meta_1922 and L_meta_2960.
set_option maxHeartbeats 1700000 in
theorem PEqualNP.Outside.R_meta_3561_214
    (raw : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5;         x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →       (15 : ℕ) ≤ x1.size)
    (theta : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x1 = fun (x3 : Fin (7 : ℕ) → Bool) => [((0 : Fin (7 : ℕ)), (1 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (2 : Fin (7 : ℕ))), ((0 : Fin (7 : ℕ)), (4 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((2 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((3 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((4 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((6 : Fin (7 : ℕ)), (3 : Fin (7 : ℕ)))].any fun (x4 : Fin (7 : ℕ) × Fin (7 : ℕ)) => x3 x4.1 && x3 x4.2) → (11 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x5 : ℕ) => Bool.true) Bool.true x4.op) x1.gates) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (13 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn (Function.update x5 (4 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (4 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ))]) = x1 x5) → False := by
  let rows : List Nat := [3,6,12,17,24,33,42,50,66,69,104,116,132,138,160,201,208,261,264,276,288,320,385,402]
  let positives : List Nat := [3,6,12,17,24,33,66,132,160,264,288,320]
  let bits (r : Nat) : Fin 9 → Bool := fun i => r.testBit i.val
  let edge (x : Fin 9 → Bool) :=
    ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any fun e =>
      x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 e)
  have signed : let edge := fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 e))
      ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
        (∃ g ∈ C.gates, g.op = GateOp.not) →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn (Function.update x 4 false) ++ [x 0 || x 4, x 4 || x 1]) = edge x) →
        ∃ D : Circuit, FanInTwo D ∧ (circuitFun 7 D = fun (x3 : Fin (7 : ℕ) → Bool) => [((0 : Fin (7 : ℕ)), (1 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (2 : Fin (7 : ℕ))), ((0 : Fin (7 : ℕ)), (4 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((2 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((3 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((4 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((6 : Fin (7 : ℕ)), (3 : Fin (7 : ℕ)))].any fun (x4 : Fin (7 : ℕ) × Fin (7 : ℕ)) => x3 x4.1 && x3 x4.2) ∧
          List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x5 : ℕ) => Bool.true) Bool.true x4.op) D.gates ≤ 10 := by
    clear raw theta rows positives bits
    let WireState := Sum Bool Nat
    let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

    have wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
        wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
      simp [wiresFrom, List.foldl_append]

    have wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
        ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
      induction gs with
      | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
      | cons g gs ih =>
        intro w
        obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
        have : wiresFrom (g :: gs) w
            = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
        rw [this, ht]; simp

    have length_wiresFrom (gs : List Gate) (w : List Bool) :
        (wiresFrom gs w).length = w.length + gs.length := by
      obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
      rw [ht]; simp [hl]

    let Ok (g : Gate) : Prop :=
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

    have getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
        (L ++ [S]).getD j d = L.getD j d := by
      by_cases hj : j < L.length
      · exact List.getD_append _ _ _ _ hj
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

    have getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
      simp

    let readStat (w : List Bool) (s : WireState) : Bool :=
      Sum.casesOn s (fun c => c) (fun j => w.getD j false)

    let validStat (m : ℕ) (s : WireState) : Prop :=
      Sum.casesOn s (fun _ => True) (fun j => j < m)

    let simpNot (m : ℕ) (xs : List WireState) : Option Gate × WireState :=
      List.casesOn (motive := fun _ => Option Gate × WireState) xs (none, .inl true) fun s _ =>
        Sum.casesOn s (fun c => (none, .inl (!c))) (fun j => (some ⟨GateOp.not,[j]⟩, .inr m))

    let simpAnd (m : ℕ) (xs : List WireState) : Option Gate × WireState :=
      List.casesOn (motive := fun _ => Option Gate × WireState) xs (none,.inl true) fun a rest =>
        List.casesOn (motive := fun _ => Option Gate × WireState) rest (none, a) fun b more =>
          List.casesOn (motive := fun _ => Option Gate × WireState) more
            (Sum.casesOn (motive := fun _ => Option Gate × WireState) a
              (fun c => Sum.casesOn b (fun d => (none,.inl (c && d))) (fun j => (none,bif c then .inr j else .inl false)))
              (fun j => Sum.casesOn b (fun c => (none,bif c then .inr j else .inl false)) (fun k => (some ⟨.and,[j,k]⟩,.inr m))))
            (fun _ _ => (none,.inl false))

    let simpOr (m : ℕ) (xs : List WireState) : Option Gate × WireState :=
      List.casesOn (motive := fun _ => Option Gate × WireState) xs (none,.inl false) fun a rest =>
        List.casesOn (motive := fun _ => Option Gate × WireState) rest (none, a) fun b more =>
          List.casesOn (motive := fun _ => Option Gate × WireState) more
            (Sum.casesOn (motive := fun _ => Option Gate × WireState) a
              (fun c => Sum.casesOn b (fun d => (none,.inl (c || d))) (fun j => (none,bif c then .inl true else .inr j)))
              (fun j => Sum.casesOn b (fun c => (none,bif c then .inl true else .inr j)) (fun k => (some ⟨.or,[j,k]⟩,.inr m))))
            (fun _ _ => (none,.inl false))

    let simplify (op : GateOp) (m : ℕ) (pins : List WireState) : Option Gate × WireState :=
      GateOp.rec (motive := fun _ => Option Gate × WireState)
        (simpAnd m pins) (simpOr m pins) (simpNot m pins) (fun _ => (none,.inl false)) (none,.inl false) op

    have simplify_ok (op : GateOp) (m : ℕ) (ins : List WireState) :
        ∀ g ∈ (simplify op m ins).1, Ok g := by
      intro g hg
      cases op <;> simp only [simplify] at hg
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
          simp [simpAnd] at hg <;> (subst hg; simp [Ok])
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
          simp [simpOr] at hg <;> (subst hg; simp [Ok])
      · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
          simp [simpNot] at hg <;> (subst hg; simp [Ok])
      · simp at hg
      · simp at hg

    have simplify_count (op : GateOp) (m : ℕ) (ins : List WireState)
        (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
        (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
        (simplify op m ins).1 = none := by
      obtain ⟨c, hc⟩ := hc
      rcases hop with rfl | rfl | rfl
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
          simp_all [simplify, simpAnd]
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
          simp_all [simplify, simpOr]
      · have := hnot rfl
        rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

    have evalAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
    have evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
    have evalNot (xs : List Bool) : GateOp.not.eval xs = !(xs.headD false) := rfl

    have simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
        (w : List Bool) (ins : List WireState) (hlen : ins.length ≤ 2)
        (hv : ∀ s ∈ ins, validStat w.length s) :
        validStat (w.length + (simplify op w.length ins).1.toList.length) ((simplify op w.length ins).2) ∧
        readStat (wiresFrom (simplify op w.length ins).1.toList w) ((simplify op w.length ins).2)
          = op.eval (ins.map (readStat w)) := by
      rcases hop with rfl | rfl | rfl
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
        · simp [simplify, simpAnd, validStat, readStat, evalAnd, evalOr, evalNot]
        · cases a <;> simp_all [simplify, simpAnd, validStat, readStat, evalAnd, evalOr, evalNot, wiresFrom]
        · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
            simp_all [simplify, simpAnd, validStat, readStat, evalAnd, evalOr, evalNot, wiresFrom]
        · simp at hlen
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
        · simp [simplify, simpOr, validStat, readStat, evalAnd, evalOr, evalNot]
        · cases a <;> simp_all [simplify, simpOr, validStat, readStat, evalAnd, evalOr, evalNot, wiresFrom]
        · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
            simp_all [simplify, simpOr, validStat, readStat, evalAnd, evalOr, evalNot, wiresFrom]
        · simp at hlen
      · rcases ins with _ | ⟨a, l⟩
        · simp [simplify, simpNot, validStat, readStat, evalAnd, evalOr, evalNot]
        · cases a <;> simp_all [simplify, simpNot, validStat, readStat, evalAnd, evalOr, evalNot, wiresFrom]

    let elimStep (n : ℕ) (acc : List WireState × List Gate) (g : Gate) : List WireState × List Gate :=
      (acc.1 ++ [(simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
        acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

    let elim (n : ℕ) (gs : List Gate) (acc : List WireState × List Gate) : List WireState × List Gate :=
      gs.foldl (elimStep n) acc

    have getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
        (L ++ [S]).getD k d = S := by
      subst h; simp

    have elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List WireState × List Gate,
        (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
      induction gs with
      | nil => intro acc h; exact h
      | cons g gs ih =>
        intro acc h
        apply ih (elimStep n acc g)
        intro g' hg'
        rcases List.mem_append.1 hg' with h1 | h1
        · exact h g' h1
        · exact simplify_ok _ _ _ g' (by simpa using h1)

    have validStat_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : WireState, validStat m s → validStat m' s := by
      intro s hs
      cases s with
      | inl c => trivial
      | inr j => exact lt_of_lt_of_le hs h

    have readStat_append (w t : List Bool) : ∀ s : WireState, validStat w.length s →
        readStat (w ++ t) s = readStat w s := by
      intro s hs
      cases s with
      | inl c => rfl
      | inr j => exact List.getD_append _ _ _ _ hs

    let Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List WireState × List Gate) : Prop :=
      acc.1.length = w.length ∧ ∀ i : ℕ,
        validStat (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
        readStat (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

    have inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
        ∀ (w : List Bool) (acc : List WireState × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
          Inv n y (wiresFrom gs w) (elim n gs acc) := by
      induction gs with
      | nil => intro w acc _ h; exact h
      | cons g gs ih =>
        intro w acc hok h
        apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
          (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        obtain ⟨hl, hi⟩ := h
        set w' := wiresFrom acc.2 y with hw'
        have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
        set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
        have hgok := hok g List.mem_cons_self
        have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
          (by
            intro s hs
            obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
            rw [lw']; exact (hi a).1)
        rw [lw'] at hs
        set r := simplify g.op (n + acc.2.length) ins with hr
        have hvals : ins.map (readStat w') = g.inputs.map fun i => w.getD i false := by
          rw [hins, List.map_map]
          apply List.map_congr_left
          intro a _
          exact (hi a).2
        have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
          rw [wiresFrom_append]
        obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
        refine ⟨by simp [elimStep, hl], ?_⟩
        intro i
        show validStat (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
          readStat (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
        rw [hnew, List.length_append, ← Nat.add_assoc]
        by_cases hil : i = acc.1.length
        · subst hil
          rw [getD_snoc_eq, hl, getD_snoc_eq]
          exact ⟨hs.1, by rw [hs.2, hvals]⟩
        · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
          refine ⟨validStat_mono (by omega) _ (hi i).1, ?_⟩
          rw [ht, readStat_append _ _ _ (by rw [lw']; exact (hi i).1)]
          exact (hi i).2
    let charged (g : Gate) : Bool :=
      GateOp.rec (motive := fun _ => Bool) true true false (fun _ => true) true g.op

    let cost (gs : List Gate) : ℕ := gs.countP charged

    let weight (g : Gate) : ℕ := if charged g then 1 else 0

    have cost_append (gs hs : List Gate) : cost (gs ++ hs) = cost gs + cost hs := by
      simp [cost]

    have cost_cons (g : Gate) (gs : List Gate) : cost (g :: gs) = weight g + cost gs := by
      cases e : charged g <;> simp [weight, cost, e, Nat.add_comm]

    let statPins (acc : List WireState × List Gate) (g : Gate) : List WireState :=
      g.inputs.map fun i => acc.1.getD i (.inl false)

    let result (n : ℕ) (acc : List WireState × List Gate) (g : Gate) :=
      simplify g.op (n + acc.2.length) (statPins acc g)

    let evaluate (g : Gate) (w : List Bool) : Bool :=
      g.op.eval (g.inputs.map fun i => w.getD i false)

    have option_le_one (o : Option Gate) : cost o.toList ≤ 1 := by
      cases o with
      | none => decide
      | some g => cases e : charged g <;> simp [cost, e]

    have not_cost (m : ℕ) (ins : List WireState) :
        cost (simpNot m ins).1.toList = 0 := by
      cases ins with
      | nil => rfl
      | cons s rest => cases s <;> rfl

    have step_bound (n : ℕ) (a : List WireState × List Gate) (g : Gate) :
        cost (result n a g).1.toList ≤ weight g := by
      obtain ⟨op,pins⟩ := g
      cases op <;> try exact option_le_one _
      exact le_of_eq (not_cost _ _)

    have step_cost (n : ℕ) (a : List WireState × List Gate) (g : Gate) :
        cost (elimStep n a g).2 = cost a.2 + cost (result n a g).1.toList := cost_append _ _

    let Tracked (l r : List Bool) (stats : List WireState) : Prop :=
      stats.length = l.length ∧ stats.length = r.length ∧
        ∀ i, l.getD i false = r.getD i false ∨ ∃ b, stats.getD i (.inl false) = .inl b

    have one_value (n : ℕ) (a : List WireState × List Gate) (g : Gate) (l r : List Bool)
        (hg : Ok g) (track : Tracked l r a.1)
        (kept : cost (result n a g).1.toList = weight g) :
        evaluate g l = evaluate g r ∨ ∃ b, (result n a g).2 = .inl b := by
      by_cases same : ∀ i ∈ g.inputs, l.getD i false = r.getD i false
      · exact Or.inl (congrArg g.op.eval (List.map_congr_left same))
      by_cases hn : g.op = GateOp.not
      · rcases g with ⟨op,pins⟩
        change op = GateOp.not at hn
        subst op
        cases pins with
        | nil => exact Or.inl rfl
        | cons i rest =>
          rcases track.2.2 i with h | ⟨b,h⟩
          · left; simpa [evaluate,evalAnd, evalOr, evalNot] using congrArg Bool.not h
          · right
            refine ⟨!b,?_⟩
            change (simpNot (n + a.2.length) (a.1.getD i (.inl false) :: rest.map (fun j => a.1.getD j (.inl false)))).2 = _
            rw [h]
      · push Not at same
        obtain ⟨i,hi,neq⟩ := same
        obtain ⟨b,hb⟩ := (track.2.2 i).resolve_left neq
        have skip : (result n a g).1 = none := by
          apply simplify_count g.op _ _ hg.1
          · simpa [statPins] using hg.2
          · exact fun h => (hn h).elim
          · exact ⟨b,List.mem_map.mpr ⟨i,hi,hb⟩⟩
        have w : weight g = 1 := by
          obtain ⟨op,pins⟩ := g
          cases op <;> simp_all [weight,charged]
        rw [skip,w] at kept
        contradiction

    have track_snoc (l r : List Bool) (stats : List WireState) (x y : Bool) (z : WireState)
        (h : Tracked l r stats) (v : x = y ∨ ∃ b, z = .inl b) :
        Tracked (l ++ [x]) (r ++ [y]) (stats ++ [z]) := by
      refine ⟨by simp [h.1],by simp [h.2.1],?_⟩
      intro i
      by_cases hi : i = stats.length
      · subst i
        rw [getD_snoc_len _ _ _ _ h.1.symm, getD_snoc_len _ _ _ _ h.2.1.symm, getD_snoc_eq]
        exact v
      · rw [getD_snoc_ne _ _ _ _ (h.1 ▸ hi), getD_snoc_ne _ _ _ _ (h.2.1 ▸ hi),
            getD_snoc_ne _ _ _ _ hi]
        exact h.2.2 i

    have elim_cost (n : ℕ) (gs : List Gate) (a : List WireState × List Gate) :
        cost (elim n gs a).2 ≤ cost a.2 + cost gs := by
      induction gs generalizing a with
      | nil => simp [elim,cost]
      | cons g gs ih =>
        change cost (elim n gs (elimStep n a g)).2 ≤ _
        have h := ih (elimStep n a g)
        rw [step_cost] at h
        rw [cost_cons]
        have := step_bound n a g
        omega

    have track_if_no_saving (n : ℕ) (gs : List Gate) (a : List WireState × List Gate) (l r : List Bool)
        (ok : ∀ g ∈ gs, Ok g) (tracked : Tracked l r a.1)
        (eqCost : cost (elim n gs a).2 = cost a.2 + cost gs) :
        Tracked (wiresFrom gs l) (wiresFrom gs r) (elim n gs a).1 := by
      induction gs generalizing a l r with
      | nil => exact tracked
      | cons g gs ih =>
        change cost (elim n gs (elimStep n a g)).2 = _ at eqCost
        rw [cost_cons] at eqCost
        have bound := elim_cost n gs (elimStep n a g)
        rw [step_cost] at bound
        have single := step_bound n a g
        have kept : cost (result n a g).1.toList = weight g := by omega
        apply ih (elimStep n a g) (l ++ [evaluate g l]) (r ++ [evaluate g r])
          (fun h mem => ok h (List.mem_cons_of_mem _ mem))
        · exact track_snoc _ _ _ _ _ _ tracked (one_value n a g l r (ok g List.mem_cons_self) tracked kept)
        · rw [step_cost]; omega

    have pin_saves_charged (n : ℕ) (gs : List Gate) (a : List WireState × List Gate) (l r : List Bool)
        (o newOutput : ℕ) (ok : ∀ g ∈ gs, Ok g) (tracked : Tracked l r a.1)
        (diff : (wiresFrom gs l).getD o false ≠ (wiresFrom gs r).getD o false)
        (wire : (elim n gs a).1.getD o (.inl false) = .inr newOutput) :
        cost (elim n gs a).2 + 1 ≤ cost a.2 + cost gs := by
      have bound := elim_cost n gs a
      by_contra! bad
      have eqCost : cost (elim n gs a).2 = cost a.2 + cost gs := by omega
      have final := track_if_no_saving n gs a l r ok tracked eqCost
      obtain ⟨b,impossible⟩ := (final.2.2 o).resolve_left diff
      rw [wire] at impossible
      contradiction

    let assigned (labels : List WireState) (x : List Bool) : List Bool :=
      labels.map (readStat x)

    have assigned_inv (n : ℕ) (labels : List WireState) (x : List Bool) (_xn : x.length = n)
        (valid : ∀ s ∈ labels, validStat n s) :
        Inv n x (assigned labels x) (labels, []) := by
      refine ⟨by simp [assigned],?_⟩
      intro i
      by_cases hi : i < labels.length
      · have hm : i < (assigned labels x).length := by simpa [assigned] using hi
        rw [List.getD_eq_getElem labels _ hi, List.getD_eq_getElem (assigned labels x) _ hm]
        exact ⟨by simpa using valid _ (List.getElem_mem hi), by simp [assigned, wiresFrom]⟩
      · have hm : (assigned labels x).length ≤ i := by simp [assigned]; omega
        rw [List.getD_eq_default labels _ (Nat.le_of_not_gt hi), List.getD_eq_default (assigned labels x) _ hm]
        exact ⟨trivial,rfl⟩

    have pin_circuit (n : ℕ) (C : Circuit) (fan : FanInTwo C)
        (labels : List WireState) (valid : ∀ s ∈ labels, validStat n s)
        (l r : List Bool) (tracked : Tracked l r labels)
        (diff : C.eval l ≠ C.eval r)
        (vary : ∃ x y : List Bool, x.length = n ∧ y.length = n ∧
          C.eval (assigned labels x) ≠ C.eval (assigned labels y)) :
        ∃ D : Circuit, FanInTwo D ∧ cost D.gates + 1 ≤ cost C.gates ∧
          ∀ x : List Bool, x.length = n → D.eval x = C.eval (assigned labels x) := by
      let a : List WireState × List Gate := (labels,[])
      let out := elim n C.gates a
      have semantics (x : List Bool) (hx : x.length = n) :
          readStat (wiresFrom out.2 x) (out.1.getD C.output (.inl false)) =
            C.eval (assigned labels x) := by
        exact ((inv_elim n x hx C.gates (assigned labels x) a fan
          (assigned_inv n labels x hx valid)).2 C.output).2
      cases hout : out.1.getD C.output (.inl false) with
      | inl b =>
        obtain ⟨x,y,hx,hy,xy⟩ := vary
        have e₁ := semantics x hx
        have e₂ := semantics y hy
        rw [hout] at e₁ e₂
        exact (xy (e₁.symm.trans e₂)).elim
      | inr o =>
        refine ⟨⟨out.2,o⟩,elim_ok n C.gates a (by simp [a]),?_,?_⟩
        · have h := pin_saves_charged n C.gates a l r C.output o fan tracked diff hout
          simpa [a,cost, out] using h
        · intro x hx
          have h := semantics x hx
          rw [hout] at h
          exact h

    let constFlag (s : WireState) : Bool := Sum.casesOn s (fun _ => true) (fun _ => false)

    let tracksCheck (l r : List Bool) (labels : List WireState) : Bool :=
      (labels.length == l.length) && (labels.length == r.length) &&
        (List.range labels.length).all fun i =>
          (l.getD i false == r.getD i false) || constFlag (labels.getD i (.inl false))

    have of_check {l r : List Bool} {labels : List WireState} (h : tracksCheck l r labels = true) :
        Tracked l r labels := by
      simp only [tracksCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
      refine ⟨h.1.1,h.1.2,?_⟩
      intro i
      by_cases hi : i < labels.length
      · have q := h.2 i (List.mem_range.mpr hi)
        simp only [Bool.or_eq_true] at q
        rcases q with a | a
        · exact Or.inl (beq_iff_eq.mp a)
        · right
          cases e : labels.getD i (.inl false) with
          | inl b => exact ⟨b,rfl⟩
          | inr k => rw [e] at a; contradiction
      · left
        rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]

    have cost_le_length (gs : List Gate) : cost gs ≤ gs.length :=
      List.countP_le_length

    have has_not_cost (gs : List Gate) (h : ∃ g ∈ gs, g.op = GateOp.not) :
        cost gs + 1 ≤ gs.length := by
      induction gs with
      | nil => simp at h
      | cons g gs ih =>
        obtain ⟨a,ha,op⟩ := h
        rcases List.mem_cons.mp ha with rfl | tail
        · have zero : charged a = false := by simp [charged,op]
          simpa [cost,List.countP_cons,zero] using Nat.succ_le_succ (cost_le_length gs)
        · have b := ih ⟨a,tail,op⟩
          have c : cost (g::gs) ≤ cost gs + 1 := by
            cases flag : charged g <;> simp [cost,flag]
          have len : (g::gs).length = gs.length + 1 := rfl
          omega

    let original (x : Fin 9 → Bool) :=
      List.ofFn (Function.update x 4 false) ++ [x 0 || x 4, x 4 || x 1]
    let middle (x : Fin 9 → Bool) :=
      [x 0,x 1,x 2,x 3,false,x 5,x 6,x 7,x 8,x 4,x 4 || x 1]
    let pinZero (x : Fin 9 → Bool) : Fin 9 → Bool :=
      ![false,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8]
    let padSeven (x : Fin 7 → Bool) : Fin 9 → Bool :=
      ![false,x 0,x 1,x 2,false,x 3,x 4,x 5,x 6]
    let seven (x : Fin 7 → Bool) :=
      ([(0,1),(1,2),(0,4),(1,5),(2,6),(3,5),(4,6),(6,3)] : List (Fin 7 × Fin 7)).any
        fun e => x e.1 && x e.2
    let firstPins : List WireState :=
      [.inl false,.inr 1,.inr 2,.inr 3,.inr 4,.inr 5,.inr 6,.inr 7,.inr 8,.inr 9,.inr 10]
    let sevenPins : List WireState :=
      [.inl false,.inr 0,.inr 1,.inr 2,.inl false,.inr 3,.inr 4,.inr 5,.inr 6,.inl false,.inr 0]
    have firstValid : ∀ s ∈ firstPins, validStat 11 s := by simp [firstPins,validStat]
    have sevenValid : ∀ s ∈ sevenPins, validStat 7 s := by simp [sevenPins,validStat]
    have checkFirst (x : Fin 9 → Bool) : assigned firstPins (middle x) = original (pinZero x) := by rfl
    have checkSeven (x : Fin 7 → Bool) : assigned sevenPins (List.ofFn x) = middle (padSeven x) := by rfl
    have checkGraph (x : Fin 7 → Bool) : edge (pinZero (padSeven x)) = seven x := by
      change (false && x 0 || (x 0 && x 1 || (x 1 && x 2 || (x 2 && false || (false && false || (false && x 3 || (x 0 && x 4 || (x 1 && x 5 || (x 2 && x 6 || (x 3 && x 5 || (x 4 && x 6 || (x 6 && x 3 || false)))))))))))) = _
      simp only [seven, List.any_cons, List.any_nil, Bool.false_and, Bool.and_false, Bool.false_or, Bool.or_false]
    let row (m : Nat) (i : Fin 9) := m.testBit i.val
    have trackedFirst : Tracked (original (row 16)) (original (row 17)) firstPins := by
      apply of_check
      dsimp only [tracksCheck,original,row,firstPins,constFlag]
      decide
    have trackedSeven : Tracked (middle (row 10)) (middle (row 26)) sevenPins := by
      apply of_check
      dsimp only [tracksCheck,middle,row,sevenPins,constFlag]
      decide
    have firstDiff : edge (row 16) ≠ edge (row 17) := by decide
    have middleDiff : edge (pinZero (row 10)) ≠ edge (pinZero (row 26)) := by decide
    have middleVaries : edge (pinZero (row 0)) ≠ edge (pinZero (row 6)) := by decide
    let emptyRow : Fin 7 → Bool := fun _ => false
    let edgeRow : Fin 7 → Bool := fun i => decide (i.val ≤ 1)
    have sevenVaries : seven emptyRow ≠ seven edgeRow := by decide
    intro predicate C fan bound hasNot exactC
    change ∀ x, C.eval (original x) = edge x at exactC
    have first (x : Fin 9 → Bool) : C.eval (assigned firstPins (middle x)) = edge (pinZero x) := by
      rw [checkFirst,exactC]
    obtain ⟨D,fanD,costD,evalD⟩ := pin_circuit 11 C fan firstPins firstValid
      (original (row 16)) (original (row 17)) trackedFirst
      (by rw [exactC,exactC]; exact firstDiff)
      ⟨middle (row 0),middle (row 6),rfl,rfl,by rw [first,first]; exact middleVaries⟩
    have midD (x : Fin 9 → Bool) : D.eval (middle x) = edge (pinZero x) :=
      (evalD _ rfl).trans (first x)
    have sevenD (x : Fin 7 → Bool) : D.eval (assigned sevenPins (List.ofFn x)) = seven x := by
      rw [checkSeven,midD,checkGraph]
    obtain ⟨E,fanE,costE,evalE⟩ := pin_circuit 7 D fanD sevenPins sevenValid
      (middle (row 10)) (middle (row 26)) trackedSeven
      (by rw [midD,midD]; exact middleDiff)
      ⟨List.ofFn emptyRow,List.ofFn edgeRow,by simp,by simp,by rw [sevenD,sevenD]; exact sevenVaries⟩
    refine ⟨E,fanE,?_,?_⟩
    · funext x
      exact (evalE (List.ofFn x) (by simp)).trans (sevenD x)
    · have pred : (fun g : Gate => @GateOp.rec (fun _ => Bool) true true false (fun _ => true) true g.op) = charged := by
        funext g
        rcases g with ⟨op,pins⟩
        cases op <;> rfl
      rw [pred]
      change cost E.gates ≤ 10
      have used := has_not_cost C.gates hasNot
      change C.gates.length ≤ 13 at bound
      omega

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
          rw [ite_eq_right (show w.length ≠ blank k by omega)]
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
  · push Not at pure
    have witness := signed C fan sz pure exactBank
    have upper := witness.choose_spec.2.2
    have lower := theta witness.choose witness.choose_spec.1 witness.choose_spec.2.1
    omega
