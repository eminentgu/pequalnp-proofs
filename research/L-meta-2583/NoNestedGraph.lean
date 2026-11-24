import PEqualNP.Outside.L_meta_1983

namespace PEqualNP.Research2583.NoNested
open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover EdgeOwnership
open PEqualNP.Outside.L_meta_1983

variable {n : Nat}

theorem gate_val_aux (gs : List Gate) (x : List Bool) (hx : x.length = n) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (hw : ∀ w ∈ g.inputs, w < n + i) :
    V gs x (n + i) = g.op.eval (g.inputs.map (V gs x)) := by
  obtain ⟨pre, post, hsplit, hlen⟩ := split_at gs i g hg
  subst hsplit
  subst hlen
  have h1 : V (pre ++ g :: post) x (n + pre.length)
      = g.op.eval (g.inputs.map fun w => (wF pre x).getD w false) :=
    wire_at n pre post g x hx
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro w hwm
  exact (V_prefix pre (g :: post) x w (by rw [hx]; exact hw w hwm)).symm

theorem orN (gs : List Gate) (x : List Bool) (hx : x.length = n) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (hw : ∀ w ∈ g.inputs, w < n + i) (hop : g.op = GateOp.or) :
    V gs x (n + i) = true ↔ ∃ w ∈ g.inputs, V gs x w = true := by
  rw [gate_val_aux gs x hx i g hg hw, hop]
  simp [GateOp.eval]

theorem andN (gs : List Gate) (x : List Bool) (hx : x.length = n) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (hw : ∀ w ∈ g.inputs, w < n + i) (hop : g.op = GateOp.and) :
    V gs x (n + i) = true ↔ ∀ w ∈ g.inputs, V gs x w = true := by
  rw [gate_val_aux gs x hx i g hg hw, hop]
  simp [GateOp.eval]

-- Cone lemmas, from the merged file L_meta_1600.lean.
lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


-- The cone pruning and propagation proofs below generalize the construction in
-- public L-meta-1983 from fourteen primary inputs to arbitrary arity.
-- The circuit restricted to the cone of the output gate o.
def newG (n : Nat) (C : Circuit) (o : ℕ) : List Gate :=
  C.gates.mapIdx (fun j g => if j = o ∨ InCone n C j o then g else ⟨GateOp.or, []⟩)

lemma newG_len (C : Circuit) (o : ℕ) : (newG n C o).length = C.gates.length := by
  simp [newG]

lemma newG_get (C : Circuit) (o i : ℕ) (g : Gate) (hg : C.gates[i]? = some g) :
    (newG n C o)[i]? = some (if i = o ∨ InCone n C i o then g else ⟨GateOp.or, []⟩) := by
  simp [newG, List.getElem?_mapIdx, hg]

lemma newG_inv (C : Circuit) (o i : ℕ) (g' : Gate) (hg : (newG n C o)[i]? = some g') :
    ∃ g, C.gates[i]? = some g ∧
      g' = if i = o ∨ InCone n C i o then g else ⟨GateOp.or, []⟩ := by
  have hi : i < C.gates.length := by
    have := (List.getElem?_eq_some_iff.1 hg).1
    rw [newG_len] at this
    exact this
  refine ⟨C.gates[i], List.getElem?_eq_getElem hi, ?_⟩
  have h2 := newG_get (n:=n) C o i C.gates[i] (List.getElem?_eq_getElem hi)
  rw [hg] at h2
  exact Option.some.inj h2

lemma inCone_trans (C : Circuit) (i j : ℕ) (hij : InCone n C i j) :
    ∀ m, m < C.gates.length → InCone n C j m → InCone n C i m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hjm
    obtain ⟨w, hw, h1, h2, h3⟩ := (inCone_iff n C j m hm).1 hjm
    refine (inCone_iff n C i m hm).2 ⟨w, hw, h1, h2, Or.inr ?_⟩
    rcases h3 with h3 | h3
    · rw [← h3]; exact hij
    · exact ih (w - n) (by omega) (by omega) h3

private lemma gate_some (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    C.gates[j]? = some (gateAt C j) := by
  rw [gateAt_eq C j hj]; exact List.getElem?_eq_getElem hj

lemma up_true_on_output (C : Circuit) (o : Nat) (ho : o < C.gates.length) (hM : Monotone2 C) (hRB : ReadsBack n C)
    (hno : ¬∃ i j, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
      InCone n C i j ∧ (j = o ∨ InCone n C j o))
    (x : List Bool) (hx : x.length = n) (i : ℕ) (hi : (gateAt C i).op = GateOp.and)
    (hv : V C.gates x (n + i) = true) :
    ∀ j, j < C.gates.length → InCone n C i j → (j = o ∨ InCone n C j o) → V C.gates x (n + j) = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hc live
    obtain ⟨w, hw, h1, h2, h3⟩ := (inCone_iff n C i j hj).1 hc
    have hg := gate_some C j hj
    have hop : (gateAt C j).op = GateOp.or := by
      have hm : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
        simpa using (hM (gateAt C j) (List.mem_of_getElem? hg)).1
      rcases hm with h | h
      · exact absurd ⟨i, j, hi, h, hc,live⟩ hno
      · exact h
    rw [orN C.gates x hx j _ hg (hRB j hj) hop]
    refine ⟨w, hw, ?_⟩
    have hw' : w = n + (w - n) := by omega
    rw [hw']
    rcases h3 with h3 | h3
    · rw [← h3]; exact hv
    · apply ih (w - n) (by omega) (by omega) h3
      right
      have back : InCone n C (w-n) j :=
        (inCone_iff n C _ j hj).2 ⟨w,hw,h1,h2,Or.inl rfl⟩
      rcases live with rfl | path
      · exact back
      · exact inCone_trans C _ j back o ho path

lemma same_val (C : Circuit) (hRB : ReadsBack n C) (o : ℕ) (ho : o < C.gates.length)
    (x : List Bool) (hx : x.length = n) :
    ∀ j, j < C.gates.length → (j = o ∨ InCone n C j o) →
      V (newG n C o) x (n + j) = V C.gates x (n + j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hk
    have hg := gate_some C j hj
    have hr := hRB j hj
    have hg' : (newG n C o)[j]? = some (gateAt C j) := by
      rw [newG_get (n:=n) C o j _ hg, ite_eq_left_of_eq_true _ _ (eq_true hk)]
    rw [gate_val_aux (newG n C o) x hx j _ hg' hr, gate_val_aux C.gates x hx j _ hg hr]
    congr 1
    apply List.map_congr_left
    intro w hw
    have hwlt := hr w hw
    by_cases hn : w < n
    · exact V_in _ _ x w (by omega)
    · have hw' : w = n + (w - n) := by omega
      have hc : InCone n C (w - n) j :=
        (inCone_iff n C _ j hj).2 ⟨w, hw, by omega, hwlt, Or.inl rfl⟩
      rw [hw']
      refine ih (w - n) (by omega) (by omega) (Or.inr ?_)
      rcases hk with hk | hk
      · rw [← hk]; exact hc
      · exact inCone_trans C _ j hc o ho hk

/-- No nested pair of ANDs on a path that reaches the chosen circuit output.
Here `InCone` relates gate indices, whereas `output` is a wire index. -/
def OnOutput (n : Nat) (C : Circuit) : Prop :=
  ∀ o, C.output = n + o → ¬∃ i j, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧
    InCone n C i j ∧ (j = o ∨ InCone n C j o)

theorem cover_bound_on_output (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (nonempty : ∃ u v, G.Adj u v)
    (noFour : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (C : Circuit) (hM : Monotone2 C) (hRB : ReadsBack n C)
    (hno : OnOutput n C)
    (hf : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  have hlen : ∀ x : Fin n → Bool, (List.ofFn x).length = n := fun x => by simp
  have hev : ∀ x : List Bool, C.eval x = V C.gates x C.output := fun x => rfl
  obtain ⟨o, ho, hout⟩ : ∃ o, o < C.gates.length ∧ C.output = n + o := by
    by_cases h1 : C.output < n
    · exfalso
      have h := (hf (fun z => decide (z.1 = C.output))).1 (by
        rw [hev]
        unfold V
        rw [getD_wF _ _ _ (by simpa using h1), getD_ofFn n _ _ _ h1]
        simp)
      obtain ⟨a, b, hab, ha, hb⟩ := h
      have ha' : a.1 = C.output := by simpa using ha
      have hb' : b.1 = C.output := by simpa using hb
      have hab' : a = b := Fin.ext (ha'.trans hb'.symm)
      subst hab'
      exact G.loopless.irrefl a hab
    · by_cases h2 : C.output < n + C.gates.length
      · exact ⟨C.output - n, by omega, by omega⟩
      · exfalso
        obtain ⟨a,b,ab⟩ := nonempty
        have h := (hf (fun _ => true)).2 ⟨a, b, ab, rfl, rfl⟩
        rw [hev, V_out _ _ _ (by rw [hlen]; omega)] at h
        exact Bool.false_ne_true h
  have hfun : ∀ x : Fin n → Bool, V C.gates (List.ofFn x) (n + o) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
    intro x
    rw [← hout, ← hev]
    exact hf x
  have hB := fun x : Fin n → Bool => same_val C hRB o ho (List.ofFn x) (hlen x)
  have hbin : ∀ g ∈ newG n C o, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
    obtain ⟨g0, hg0, he⟩ := newG_inv (n:=n) C o i _ (List.getElem?_eq_getElem hi)
    rw [he]
    have hm := hM g0 (List.mem_of_getElem? hg0)
    split_ifs
    · exact ⟨by simpa using hm.1, hm.2⟩
    · exact ⟨Or.inr rfl, by simp⟩
  have key := @pairCleanBound n G _ noFour (newG n C o) C.output hbin
  have key2 := key (by
    intro x
    have h1 : Circuit.eval ⟨newG n C o, C.output⟩ (List.ofFn x)
        = V C.gates (List.ofFn x) (n + o) := by
      rw [eval_eq, hout]; exact hB x o ho (Or.inl rfl)
    rw [h1]
    apply Bool.eq_iff_iff.2
    simp only [decide_eq_true_eq]
    exact hfun x) (by
    intro i x _ hop hv
    have hi : i.1 < C.gates.length := lt_of_lt_of_eq i.2 (newG_len C o)
    obtain ⟨g0, hg0, he⟩ := newG_inv (n:=n) C o i.1 ((newG n C o).get i) (by simp)
    have hk : i.1 = o ∨ InCone n C i.1 o := by
      by_contra hk
      rw [he, ite_eq_right_of_eq_false _ _ (eq_false hk)] at hop
      simp at hop
    rw [he, ite_eq_left_of_eq_true _ _ (eq_true hk)] at hop
    have hga : gateAt C i.1 = g0 := by
      rw [gateAt_eq C _ hi]
      exact Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hg0)
    have hv' : V C.gates (List.ofFn x) (n + i.1) = true := by
      rw [← hB x i.1 hi hk]; exact hv
    apply (hfun x).1
    rcases hk with hk | hk
    · rw [← hk]; exact hv'
    · exact up_true_on_output C o ho hM hRB (hno o hout) _ (hlen x) i.1 (by rw [hga]; exact hop) hv' o ho hk (Or.inl rfl))
  obtain ⟨T, hT, hcard⟩ := key2
  rw [newG_len] at hcard
  exact ⟨T,hT,hcard⟩

theorem cover_bound (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (nonempty : ∃ u v, G.Adj u v)
    (noFour : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (C : Circuit) (hM : Monotone2 C) (hRB : ReadsBack n C)
    (hno : ¬∃ i j, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧
      InCone n C i j)
    (hf : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  apply cover_bound_on_output G nonempty noFour C hM hRB _ hf
  rintro o hout ⟨i,j,hi,hj,hij,_⟩
  exact hno ⟨i,j,hi,hj,hij⟩

#print axioms cover_bound_on_output
end PEqualNP.Research2583.NoNested
