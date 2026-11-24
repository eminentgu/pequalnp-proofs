import PEqualNP.Defs

/- Constant-propagation, incidence and graph arguments in this file use the published proofs L-meta-1892, L-meta-1955, L-meta-1983 and L-meta-3008 of open-goat/pequalnp-proofs, together with the research proofs of L-meta-2583 and the normalized column trace of L-meta-4387. -/

namespace PEqualNP.Outside.L_meta_physical

namespace Plane1955

theorem lines_through (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  have : Nonempty (Fin N) := ⟨p⟩
  choose! f hf using fun (p' : Fin N) (h : p' ≠ p) => (hu p' p h).exists
  have hfu : ∀ p' l, p' ≠ p → I p' l → I p l → f p' = l := by
    intro p' l h h1 h2
    exact (hu p' p h).unique (hf p' h) ⟨h1, h2⟩
  have hcount := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.erase p)
    (t := Finset.univ.filter (fun l => I p l)) (f := f) (fun p' hp' => by
      have hne := Finset.ne_of_mem_erase hp'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf p' hne).2⟩)
  have hfib : ∀ l ∈ Finset.univ.filter (fun l => I p l),
      ((Finset.univ.erase p).filter (fun p' => f p' = l)).card = q := by
    intro l hl'
    have hpl : I p l := (Finset.mem_filter.mp hl').2
    have e : (Finset.univ.erase p).filter (fun p' => f p' = l)
        = (Finset.univ.filter (fun p' => I p' l)).erase p := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨hne, hfl⟩
        exact ⟨hne, hfl ▸ (hf p' hne).1⟩
      · rintro ⟨hne, hI⟩
        exact ⟨hne, hfu p' l hne hI hpl⟩
    rw [e, Finset.card_erase_of_mem (show p ∈ Finset.univ.filter (fun p' => I p' l) from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩), hl l]
    rfl
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  subst hN
  have h2 : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
    rw [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) (hcount.symm.trans h2)

theorem cardL {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    ((A ×ˢ B).filter (fun pw : Fin N × Fin N => I pw.1 pw.2)).card
      = ∑ p ∈ A, (B.filter (fun w => I p w)).card := by
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.card_filter]

theorem cardR {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    ((A ×ˢ B).filter (fun pw : Fin N × Fin N => I pw.1 pw.2)).card
      = ∑ w ∈ B, (A.filter (fun p => I p w)).card := by
  rw [Finset.card_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Finset.card_filter]

theorem cover {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpt : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = q + 1)
    (A B : Finset (Fin N)) (hc : ∀ p w : Fin N, I p w → p ∈ A ∨ w ∈ B) :
    N ≤ A.card + B.card := by
  have hE : (((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N))).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)).card = N * (q + 1) := by
    rw [cardR, Finset.sum_congr rfl (fun w _ => hl w), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  have hA : ((A ×ˢ (Finset.univ : Finset (Fin N))).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)).card = A.card * (q + 1) := by
    rw [cardL, Finset.sum_congr rfl (fun p _ => hpt p), Finset.sum_const, smul_eq_mul]
  have hB : (((Finset.univ : Finset (Fin N)) ×ˢ B).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)).card = B.card * (q + 1) := by
    rw [cardR, Finset.sum_congr rfl (fun w _ => hl w), Finset.sum_const, smul_eq_mul]
  have hsub : ((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N))).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)
      ⊆ ((A ×ˢ (Finset.univ : Finset (Fin N))).filter (fun pw : Fin N × Fin N => I pw.1 pw.2))
        ∪ (((Finset.univ : Finset (Fin N)) ×ˢ B).filter (fun pw : Fin N × Fin N => I pw.1 pw.2)) := by
    rintro ⟨p, w⟩ h
    have hI : I p w := (Finset.mem_filter.mp h).2
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product]
    rcases hc p w hI with h1 | h1
    · exact Or.inl ⟨⟨h1, Finset.mem_univ _⟩, hI⟩
    · exact Or.inr ⟨⟨Finset.mem_univ _, h1⟩, hI⟩
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [hE, hA, hB, ← Nat.add_mul] at h
  exact Nat.le_of_mul_le_mul_right h (Nat.succ_pos q)

theorem count {N : ℕ} (q k : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (lps pps : Fin N → Fin N → Prop)
    (hpt : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = q + 1) (hkq : k ≤ q)
    (hL : ∀ p w : Fin N, I p w → lps p w ∨ pps p w) :
    (k + 1) * N ≤ ∑ w : Fin N, Set.ncard {p : Fin N | lps p w}
      + ∑ p : Fin N, min (k + 1) (Set.ncard {w : Fin N | pps p w}) := by
  classical
  have e1 : ∀ w : Fin N, Set.ncard {p : Fin N | lps p w}
      = (Finset.univ.filter (fun p : Fin N => lps p w)).card := by
    intro w
    rw [← Set.ncard_coe_finset]
    congr 1
    ext p
    simp
  have e2 : ∀ p : Fin N, Set.ncard {w : Fin N | pps p w}
      = (Finset.univ.filter (fun w : Fin N => pps p w)).card := by
    intro p
    rw [← Set.ncard_coe_finset]
    congr 1
    ext w
    simp
  have e3 : ∑ w : Fin N, (Finset.univ.filter (fun p : Fin N => lps p w)).card
      = ∑ p : Fin N, (Finset.univ.filter (fun w : Fin N => lps p w)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hp : ∀ p : Fin N, k + 1 ≤ (Finset.univ.filter (fun w : Fin N => lps p w)).card
      + min (k + 1) (Set.ncard {w : Fin N | pps p w}) := by
    intro p
    rw [e2 p]
    have hsub : Finset.univ.filter (fun l => I p l)
        ⊆ Finset.univ.filter (fun w : Fin N => lps p w)
          ∪ Finset.univ.filter (fun w : Fin N => pps p w) := by
      intro w hw
      have hI : I p w := (Finset.mem_filter.mp hw).2
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      rcases hL p w hI with h1 | h1
      · exact Or.inl ⟨Finset.mem_univ _, h1⟩
      · exact Or.inr ⟨Finset.mem_univ _, h1⟩
    have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [hpt p] at h
    omega
  rw [Finset.sum_congr rfl (fun w _ => e1 w), e3, ← Finset.sum_add_distrib]
  calc (k + 1) * N = ∑ _p : Fin N, (k + 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun p _ => hp p)


end Plane1955

namespace Fano1983

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj


def posRead {n : ℕ} (gs : List Gate) (w : ℕ) (x : Fin n → Bool) : Bool :=
  match w with
  | 0 => false
  | i + 1 => (wiresFrom gs (List.ofFn x)).getD i false

def clampWire (lim i : ℕ) : ℕ := if i < lim then i + 1 else 0

def gateAtPos (n : ℕ) (gs : List Gate) (w : ℕ) : Gate :=
  gs.getD (w - (n + 1)) ⟨GateOp.or, []⟩

def firstWire (n : ℕ) (gs : List Gate) (w : ℕ) : ℕ :=
  clampWire (w-1) ((gateAtPos n gs w).inputs.getD 0 (w-1))

def secondWire (n : ℕ) (gs : List Gate) (w : ℕ) : ℕ :=
  clampWire (w-1) ((gateAtPos n gs w).inputs.getD 1 ((gateAtPos n gs w).inputs.getD 0 (w-1)))

def andPos (n : ℕ) (gs : List Gate) (w : ℕ) : Bool :=
  match (gateAtPos n gs w).op with
  | GateOp.and => true
  | _ => false

lemma clamp_lt (w i : ℕ) (hw : 0 < w) : clampWire (w-1) i < w := by
  unfold clampWire
  split <;> omega

lemma pos_clamp {n : ℕ} (gs : List Gate) (lim i : ℕ) (x : Fin n → Bool) :
    posRead gs (clampWire lim i) x =
    (if i < lim then (wiresFrom gs (List.ofFn x)).getD i false else false) := by
  simp only [clampWire]
  split <;> rfl

lemma pos_input {n : ℕ} (gs : List Gate) (i : ℕ) (hi : i < n) (x : Fin n → Bool) :
    posRead gs (i+1) x = x ⟨i,hi⟩ := by
  change (wiresFrom gs (List.ofFn x)).getD i false = x ⟨i,hi⟩
  rw [getD_wiresFrom_lt _ _ _ (by simpa using hi)]
  rw [List.getD_eq_getElem (List.ofFn x) false (by simpa using hi),List.getElem_ofFn]

lemma pos_mono {n : ℕ} (gs : List Gate)
    (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : ℕ) (x y : Fin n → Bool) (le : ∀ i, x i = true → y i = true) :
    posRead gs w x = true → posRead gs w y = true := by
  cases w with
  | zero => simp [posRead]
  | succ i =>
    apply wiresFrom_mono gs ops _ _ (by simp)
    intro j h
    by_cases hj : j < n
    · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn] at h ⊢
      exact le _ h
    · rw [List.getD_eq_default _ _ (by simp; omega)] at h
      contradiction

def edgeTrue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

def singletonBits {n : ℕ} (u : Fin n) : Fin n → Bool := fun z => decide (z = u)
def pairBits {n : ℕ} (u v : Fin n) : Fin n → Bool := fun z => decide (z = u ∨ z = v)

lemma edge_single {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) :
    ¬ edgeTrue G (singletonBits u) := by
  rintro ⟨i,j,h,hi,hj⟩
  simp only [singletonBits, decide_eq_true_eq] at hi hj
  subst i
  subst j
  exact G.loopless.irrefl u h

lemma edge_pair {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    edgeTrue G (pairBits u v) ↔ G.Adj u v := by
  constructor
  · rintro ⟨i,j,h,hi,hj⟩
    simp only [pairBits, decide_eq_true_eq] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (G.loopless.irrefl _ h).elim
    · exact h
    · exact h.symm
    · exact (G.loopless.irrefl _ h).elim
  · intro h
    exact ⟨u,v,h,by simp [pairBits],by simp [pairBits]⟩

lemma binary_eval (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (hl : l.length ≤ 2) (nonempty : op = GateOp.and → l ≠ [])
    (v : ℕ → Bool) (lim : ℕ) (vd : v lim = false) :
    op.eval (l.map v) =
      (if (match op with | GateOp.and => true | _ => false) then
        v (l.getD 0 lim) && v (l.getD 1 (l.getD 0 lim))
       else v (l.getD 0 lim) || v (l.getD 1 (l.getD 0 lim))) := by
  cases l with
  | nil =>
    rcases hop with rfl | rfl
    · exact (nonempty rfl rfl).elim
    · simp [GateOp.eval,vd]
  | cons i t =>
    cases t with
    | nil => rcases hop with rfl | rfl <;> simp [GateOp.eval]
    | cons j t =>
      have ht : t = [] := List.length_eq_zero_iff.mp (by simpa using hl)
      subst t
      rcases hop with rfl | rfl <;> simp [GateOp.eval]

def supports {n : ℕ} (gs : List Gate) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => posRead gs w (singletonBits u) = true

lemma mem_support {n : ℕ} (gs : List Gate) (w : ℕ) (u : Fin n) :
    u ∈ supports gs w ↔ posRead gs w (singletonBits u) = true := by simp [supports]


def cleanOn {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) : Prop :=
  ∀ (j : Fin gs.length) (x : Fin n → Bool),
    (x = (fun _ => false) ∨ (∃ u, x = singletonBits u) ∨ (∃ u v, x = pairBits u v)) →
    (gs.get j).op = GateOp.and →
    (wiresFrom gs (List.ofFn x)).getD (n + j.val) false = true → edgeTrue G x

def binaryOps (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma gateAt_index {n : ℕ} (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    gateAtPos n gs (n+j+1) = gs[j] := by
  unfold gateAtPos
  rw [show n+j+1-(n+1) = j by omega,List.getD_eq_getElem _ _ hj]

lemma pos_gate {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs)
    (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length) (x : Fin n → Bool) :
    posRead gs w x =
      (if andPos n gs w then
        posRead gs (firstWire n gs w) x && posRead gs (secondWire n gs w) x
       else posRead gs (firstWire n gs w) x || posRead gs (secondWire n gs w) x) := by
  let j := w-(n+1)
  have hj : j < gs.length := by dsimp [j]; omega
  have hw : w = n+j+1 := by dsimp [j]; omega
  have hg := ops _ (List.getElem_mem hj)
  have nonempty : gs[j].op = GateOp.and → gs[j].inputs ≠ [] := by
    intro ha hempty
    let z : Fin n → Bool := fun _ => false
    have eqg := getD_wiresFrom_gate gs (List.ofFn z) j hj
    simp only [List.length_ofFn, hempty, List.map_nil, ha, GateOp.eval, List.all_nil] at eqg
    obtain ⟨u,v,_,h,_⟩ := clean ⟨j,hj⟩ z (Or.inl rfl) ha eqg
    contradiction
  rw [hw]
  simp only [firstWire, secondWire, andPos, gateAt_index gs j hj, Nat.add_sub_cancel, pos_clamp]
  change (wiresFrom gs (List.ofFn x)).getD (n+j) false = _
  have h := getD_wiresFrom_gate gs (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  rw [h]
  exact binary_eval gs[j].op hg.1 gs[j].inputs hg.2 nonempty
    (fun i => if i < n+j then (wiresFrom gs (List.ofFn x)).getD i false else false)
    (n+j) (by simp)

lemma pos_clean {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length)
    (ha : andPos n gs w = true) (x : Fin n → Bool)
    (hx : x = (fun _ => false) ∨ (∃ u, x = singletonBits u) ∨ (∃ u v, x = pairBits u v)) :
    posRead gs w x = true → edgeTrue G x := by
  let j := w-(n+1)
  have hj : j < gs.length := by dsimp [j]; omega
  have hw : w = n+j+1 := by dsimp [j]; omega
  rw [hw] at ha ⊢
  simp only [andPos, gateAt_index gs j hj] at ha
  have hop : gs[j].op = GateOp.and := by
    cases h : gs[j].op <;> simp_all
  exact clean ⟨j,hj⟩ x hx hop

lemma support_base {n : ℕ} (gs : List Gate) (w : ℕ) (hw : w < n+1) :
    (supports (n:=n) gs w).card ≤ 1 := by
  cases w with
  | zero => simp [supports,posRead]
  | succ i =>
    have hi : i < n := by omega
    have hs : supports gs (i+1) = {⟨i,hi⟩} := by
      ext u
      simp [mem_support,pos_input gs i hi,singletonBits,eq_comm]
    simp [hs]

lemma hit_base {n : ℕ} (gs : List Gate) (w : ℕ) (u v : Fin n) (hw : w < n+1) :
    posRead gs w (pairBits u v) = true → u ∈ supports gs w ∨ v ∈ supports gs w := by
  cases w with
  | zero => simp [posRead]
  | succ i =>
    have hi : i<n := by omega
    simp [mem_support,pos_input gs i hi,pairBits,singletonBits]

lemma support_and {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length)
    (ha : andPos n gs w = true) : supports (n:=n) gs w = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  exact edge_single G u (pos_clean G gs clean w lo hi ha _ (Or.inr (Or.inl ⟨u, rfl⟩)) ((mem_support gs w u).mp hu))

lemma support_or {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w)
    (hi : w < n+1+gs.length) (ha : andPos n gs w = false) :
    supports (n:=n) gs w = supports gs (firstWire n gs w) ∪ supports gs (secondWire n gs w) := by
  ext u
  simp only [Finset.mem_union,mem_support,pos_gate G gs ops clean w lo hi,ha]
  simp

lemma cross_support {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w)
    (hi : w < n+1+gs.length) (ha : andPos n gs w = true)
    (u : Fin n) (hu : u ∈ supports gs (firstWire n gs w))
    (v : Fin n) (hv : v ∈ supports gs (secondWire n gs w)) : G.Adj u v := by
  apply (edge_pair G u v).mp
  apply pos_clean G gs clean w lo hi ha _ (Or.inr (Or.inr ⟨u, v, rfl⟩))
  rw [pos_gate G gs ops clean w lo hi,ha]
  simp only [ite_true, Bool.and_eq_true]
  have hm := pos_mono (n:=n) gs (fun g h => (ops g h).1)
  constructor
  · apply hm (firstWire n gs w) (singletonBits u) (pairBits u v) _ ((mem_support _ _ _).mp hu)
    intro i ht
    simp only [singletonBits,decide_eq_true_eq] at ht
    simp [pairBits,ht]
  · apply hm (secondWire n gs w) (singletonBits v) (pairBits u v) _ ((mem_support _ _ _).mp hv)
    intro i ht
    simp only [singletonBits,decide_eq_true_eq] at ht
    simp [pairBits,ht]


lemma root_read {n : ℕ} (gs : List Gate) (out : ℕ) (x : Fin n → Bool) :
    posRead gs (clampWire (n+gs.length) out) x = (Circuit.mk gs out).eval (List.ofFn x) := by
  rw [pos_clamp]
  change (if out < n+gs.length then _ else _) = (wiresFrom gs (List.ofFn x)).getD out false
  split_ifs with h
  · rfl
  · symm
    apply List.getD_eq_default
    simpa only [length_wiresFrom, List.length_ofFn] using Nat.le_of_not_lt h

lemma root_bound (n len out : ℕ) : clampWire (n+len) out < n+1+len := by
  unfold clampWire
  split <;> omega

lemma root_support_empty {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (out : ℕ)
    (heval : ∀ x, (Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x) :
    supports (n:=n) gs (clampWire (n+gs.length) out) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u h
  apply edge_single G u
  apply (heval _).mp
  rw [← root_read]
  exact (mem_support _ _ _).mp h

lemma root_hits {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (out : ℕ)
    (heval : ∀ x, (Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x) :
    ∀ u v, G.Adj u v → posRead gs (clampWire (n+gs.length) out) (pairBits u v) = true := by
  intro u v h
  rw [root_read,heval]
  exact (edge_pair G u v).mpr h

theorem countUnion {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
    (paid : Finset ℕ) (m : ℕ)
    (step : ∀ w < m, 1 < (support w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ support w ⊆ cs.biUnion support ∧
      cs.card ≤ 1 + (if w ∈ paid then 1 else 0))
    (roots : Finset ℕ) (hr : roots ⊆ Finset.range m) :
    (roots.biUnion support).card ≤ roots.card + ((Finset.range m) ∩ paid).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have : roots = ∅ := by simpa using hr
    simp [this]
  | succ m ih =>
    have old := ih (fun w hw => step w (by omega))
    have hpre : roots.erase m ⊆ Finset.range m := by
      intro w hw
      have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      have hlt := Finset.mem_range.mp (hr hmem)
      exact Finset.mem_range.mpr (by omega)
    have hcost : ((Finset.range (m + 1)) ∩ paid).card =
        ((Finset.range m) ∩ paid).card + (if m ∈ paid then 1 else 0) := by
      by_cases h : m ∈ paid
      · have he : Finset.range (m + 1) ∩ paid = insert m (Finset.range m ∩ paid) := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
      · have he : Finset.range (m + 1) ∩ paid = Finset.range m ∩ paid := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
    rw [hcost]
    by_cases hm : m ∈ roots
    · have hrins := Finset.insert_erase hm
      have hroots : (roots.erase m).card + 1 = roots.card :=
        Finset.card_erase_add_one hm
      by_cases hb : 1 < (support m).card
      · obtain ⟨cs, hcpre, hcov, hcard⟩ := step m (by omega) hb
        have hsub : roots.biUnion support ⊆ ((roots.erase m) ∪ cs).biUnion support := by
          intro a ha
          obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases heq : w = m
          · subst w
            obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp (hcov haw)
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hav⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hw⟩), haw⟩
        have hh := old ((roots.erase m) ∪ cs) (Finset.union_subset hpre hcpre)
        have hh' := Finset.card_le_card hsub
        have hu := Finset.card_union_le (roots.erase m) cs
        omega
      · have hh := old (roots.erase m) hpre
        have he : roots.biUnion support = support m ∪ (roots.erase m).biUnion support := by
          conv_lhs => rw [← hrins]
          rw [Finset.biUnion_insert]
        rw [he]
        have hu := Finset.card_union_le (support m) ((roots.erase m).biUnion support)
        omega
    · rw [Finset.erase_eq_of_notMem hm] at hpre
      have hh := old roots hpre
      omega

theorem dag_union_bound {α : Type*} [DecidableEq α] (f : ℕ → Finset α) (R B : Finset ℕ)
    (step : ∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
      (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) :
    (R.biUnion f).card ≤ R.card + B.card := by
  classical
  let m := R.sup id + 1
  have hr : R ⊆ Finset.range m := by
    intro w hw
    have h : w ≤ R.sup id := Finset.le_sup (f := id) hw
    exact Finset.mem_range.mpr (by dsimp [m]; omega)
  have haux : (R.biUnion f).card ≤ R.card + (Finset.range m ∩ B).card := by
    apply countUnion f B m _ R hr
    intro i _ hi
    rcases step i hi with ⟨a, ha, hsub⟩ | ⟨hiB, a, ha, b, hb, hsub⟩
    · refine ⟨{a}, ?_, ?_, ?_⟩
      · simpa using ha
      · simpa using hsub
      · simp
    · refine ⟨{a,b}, ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Finset.mem_range.mpr ha
        · rw [Finset.mem_singleton.mp hw]
          exact Finset.mem_range.mpr hb
      · simpa using hsub
      · simp only [hiB, ite_true]
        exact Finset.card_le_two
  have hl := Finset.card_le_card (Finset.inter_subset_right (s₁ := Finset.range m) (s₂ := B))
  omega

theorem gate_partition_count (n len : ℕ) (A : ℕ → Bool) (S : ℕ → Finset (Fin n)) :
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = true)).card +
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = false ∧
      1 < (S w).card)).card +
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = false ∧
      (S w).card ≤ 1)).card ≤ len := by
  classical
  let gates := Finset.range (n + 1 + len)
  let ands := gates.filter (fun w => n + 1 ≤ w ∧ A w = true)
  let large := gates.filter (fun w => n + 1 ≤ w ∧ A w = false ∧ 1 < (S w).card)
  let small := gates.filter (fun w => n + 1 ≤ w ∧ A w = false ∧ (S w).card ≤ 1)
  change ands.card + large.card + small.card ≤ len
  have hdis : Disjoint ands large := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    have a := (Finset.mem_filter.mp h₁).2.2
    have b := (Finset.mem_filter.mp h₂).2.2.1
    simp_all
  have hdis' : Disjoint (ands ∪ large) small := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    have b := (Finset.mem_filter.mp h₂).2.2
    rcases Finset.mem_union.mp h₁ with ha | hl
    · have a := (Finset.mem_filter.mp ha).2.2
      simp_all
    · have a := (Finset.mem_filter.mp hl).2.2.2
      exact (Nat.not_lt_of_ge b.2) a
  have hsub : (ands ∪ large) ∪ small ⊆ Finset.Ico (n+1) (n+1+len) := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · rcases Finset.mem_union.mp h with h | h <;>
        exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,
          Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
    · exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,
        Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
  rw [← Finset.card_union_of_disjoint hdis, ← Finset.card_union_of_disjoint hdis']
  simpa using Finset.card_le_card hsub

def coverCert {n : ℕ} (k N : ℕ) (S : ℕ → Finset (Fin n))
    (a b : ℕ → ℕ) (A : ℕ → Bool)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w) (w : ℕ) : Finset (Fin n) :=
  if (S w).card ≤ 1 then
    if _hg : k ≤ w ∧ w < N then
      if A w = true then
        if (S (a w)).card ≤ 1 then coverCert k N S a b A ha hb (a w)
        else coverCert k N S a b A ha hb (b w)
      else
        coverCert k N S a b A ha hb (a w) ∪ coverCert k N S a b A ha hb (b w)
    else S w
  else ∅
termination_by w
decreasing_by all_goals first | exact ha _ _hg.1 _hg.2 | exact hb _ _hg.1 _hg.2

theorem cover_half (n k N r : ℕ) (G : SimpleGraph (Fin n))
    (S : ℕ → Finset (Fin n)) (H : ℕ → Fin n → Fin n → Prop)
    (a b : ℕ → ℕ) (A : ℕ → Bool) (hr : r < N) (hrS : S r = ∅)
    (hrH : ∀ u v, G.Adj u v → H r u v)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handS : ∀ w, k ≤ w → w < N → A w = true →
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hdag : ∀ (f : ℕ → Finset (Fin n)) (R B : Finset ℕ),
      (∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
        (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) →
      (R.biUnion f).card ≤ R.card + B.card) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      T.card ≤ 1 + ((Finset.range N).filter fun w =>
        k ≤ w ∧ A w = false ∧ (S w).card ≤ 1).card := by
  let f := coverCert k N S a b A ha hb
  let B := (Finset.range N).filter fun w => k ≤ w ∧ A w = false ∧ (S w).card ≤ 1
  have feq (w : ℕ) : f w =
      if (S w).card ≤ 1 then
        if k ≤ w ∧ w < N then
          if A w = true then
            if (S (a w)).card ≤ 1 then f (a w) else f (b w)
          else f (a w) ∪ f (b w)
        else S w
      else ∅ := by
    exact coverCert.eq_1 ..
  have hit : ∀ w, w < N → (S w).card ≤ 1 →
      ∀ u v, H w u v → u ∈ f w ∨ v ∈ f w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw ht u v hwuv
      rw [feq, ite_eq_left ht]
      by_cases hkw : k ≤ w
      · rw [ite_eq_left ⟨hkw, hw⟩]
        cases hg : A w with
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          have heq := horS w hkw hw hg
          have hta : (S (a w)).card ≤ 1 := by
            apply (Finset.card_le_card _).trans ht
            rw [heq]
            exact Finset.subset_union_left
          have htb : (S (b w)).card ≤ 1 := by
            apply (Finset.card_le_card _).trans ht
            rw [heq]
            exact Finset.subset_union_right
          have hia := ha w hkw hw
          have hib := hb w hkw hw
          rcases horH w u v hkw hw hg hwuv with h | h
          · have hitA := ih _ hia (hia.trans hw) hta u v h
            simp only [Finset.mem_union]
            tauto
          · have hitB := ih _ hib (hib.trans hw) htb u v h
            simp only [Finset.mem_union]
            tauto
        | true =>
          simp only [ite_true]
          have hz := handH w u v hkw hw hg hwuv
          by_cases htA : (S (a w)).card ≤ 1
          · rw [ite_eq_left htA]
            have hl := ha w hkw hw
            exact ih _ hl (hl.trans hw) htA u v hz.1
          · rw [ite_eq_right htA]
            have hl := hb w hkw hw
            exact ih _ hl (hl.trans hw) ((handS w hkw hw hg).resolve_left htA) u v hz.2
      · rw [ite_eq_right (fun h => hkw h.1)]
        exact hinput w u v (Nat.lt_of_not_ge hkw) hwuv
  refine ⟨f r, fun u v huv => hit r hr (by simp [hrS]) u v (hrH u v huv), ?_⟩
  have hstep (w : ℕ) (hw : 1 < (f w).card) :
      (∃ j < w, f w ⊆ f j) ∨
        (w ∈ B ∧ ∃ i < w, ∃ j < w, f w ⊆ f i ∪ f j) := by
    have ht : (S w).card ≤ 1 := by
      by_contra ht
      rw [feq, ite_eq_right ht] at hw
      simp at hw
    have hg : k ≤ w ∧ w < N := by
      by_contra h
      rw [feq, ite_eq_left ht, ite_eq_right h] at hw
      omega
    have hia := ha w hg.1 hg.2
    have hib := hb w hg.1 hg.2
    cases hop : A w with
    | false =>
      right
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg.2, hg.1, hop, ht⟩,
        a w, hia, b w, hib, ?_⟩
      rw [feq, ite_eq_left ht, ite_eq_left hg, hop]
      simp
    | true =>
      left
      by_cases htA : (S (a w)).card ≤ 1
      · refine ⟨a w, hia, ?_⟩
        rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_left htA]
      · refine ⟨b w, hib, ?_⟩
        rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_right htA]
  simpa [B] using hdag f {r} B hstep

theorem edge_birth (n k N r : ℕ) (S : ℕ → Finset (Fin n))
    (H : ℕ → Fin n → Fin n → Prop) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (x y : Fin n) (hr : r < N) (hxy : H r x y) (hx : x ∉ S r) (hy : y ∉ S r)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hdisj : ∀ w, k ≤ w → w < N → A w = true → Disjoint (S (a w)) (S (b w))) :
    ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
      ((x ∈ S (a w) ∧ y ∈ S (b w)) ∨ (y ∈ S (a w) ∧ x ∈ S (b w))) := by
  induction r using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hkw : k ≤ w
    · have hia := ha w hkw hr
      have hib := hb w hkw hr
      cases hop : A w with
      | false =>
        have hSw := horS w hkw hr hop
        rw [hSw, Finset.mem_union] at hx hy
        rcases horH w x y hkw hr hop hxy with h | h
        · exact ih _ hia (hia.trans hr) h (fun h => hx (.inl h)) (fun h => hy (.inl h))
        · exact ih _ hib (hib.trans hr) h (fun h => hx (.inr h)) (fun h => hy (.inr h))
      | true =>
        have htrue := handH w x y hkw hr hop hxy
        by_cases hsa : x ∈ S (a w) ∨ y ∈ S (a w)
        · by_cases hsb : x ∈ S (b w) ∨ y ∈ S (b w)
          · refine ⟨w, hkw, hr, hop, ?_⟩
            have hd := Finset.disjoint_left.mp (hdisj w hkw hr hop)
            rcases hsa with hax | hay <;> rcases hsb with hbx | hby
            · exact False.elim (hd hax hbx)
            · exact Or.inl ⟨hax, hby⟩
            · exact Or.inr ⟨hay, hbx⟩
            · exact False.elim (hd hay hby)
          · exact ih _ hib (hib.trans hr) htrue.2 (fun h => hsb (.inl h)) (fun h => hsb (.inr h))
        · exact ih _ hia (hia.trans hr) htrue.1 (fun h => hsa (.inl h)) (fun h => hsa (.inr h))
    · rcases hinput w x y (Nat.lt_of_not_ge hkw) hxy with h | h
      · exact False.elim (hx h)
      · exact False.elim (hy h)

theorem edge_finset_gate_bound (n k N : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
    (hunion : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (hjoin : ∀ w, k ≤ w → w < N → A w = true →
      ∀ u ∈ S (a w), ∀ v ∈ S (b w), G.Adj u v)
    (hside : ∀ w, k ≤ w → w < N → A w = true →
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (hcover : ∀ u v, G.Adj u v → ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
      ((u ∈ S (a w) ∧ v ∈ S (b w)) ∨ (v ∈ S (a w) ∧ u ∈ S (b w)))) :
    G.edgeFinset.card ≤
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = true)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)).card := by
  classical
  cases isEmpty_or_nonempty (Fin n) with
  | inl h =>
    have := h
    have he : G.edgeFinset = ∅ := Finset.eq_empty_of_forall_notMem (fun e => isEmptyElim e)
    simp [he]
  | inr hn =>
    let z := Classical.choice hn
    let AS := (Finset.range N).filter (fun w => k ≤ w ∧ A w = true)
    let OS := (Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)
    let adj (c : Fin n) (w : ℕ) := ∀ x ∈ S w, G.Adj c x
    let F (c : Fin n) (w : ℕ) := if w < N ∧ adj c w then S w else ∅
    have pick : ∀ w, ∃ (c : Fin n) (j : ℕ), w ∈ AS →
        ∀ u ∈ S (a w), ∀ v ∈ S (b w),
          (u = c ∧ v ∈ F c j) ∨ (v = c ∧ u ∈ F c j) := by
      intro w
      by_cases hw : w ∈ AS
      · obtain ⟨hN, hk, hA⟩ : w < N ∧ k ≤ w ∧ A w = true := by simpa [AS] using hw
        obtain ⟨ha,hb⟩ := hparents w hk hN
        have hJ := hjoin w hk hN hA
        rcases hside w hk hN hA with h | h
        · by_cases hne : (S (a w)).Nonempty
          · obtain ⟨c,hc⟩ := hne
            have hf : F c (b w) = S (b w) := ite_eq_left ⟨by omega, hJ c hc⟩
            exact ⟨c, b w, fun _ u hu v hv => Or.inl ⟨Finset.card_le_one.mp h u hu c hc, hf ▸ hv⟩⟩
          · exact ⟨z, 0, fun _ u hu => (hne ⟨u,hu⟩).elim⟩
        · by_cases hne : (S (b w)).Nonempty
          · obtain ⟨c,hc⟩ := hne
            have hf : F c (a w) = S (a w) := ite_eq_left ⟨by omega, fun x hx => (hJ x hx c hc).symm⟩
            exact ⟨c, a w, fun _ u hu v hv => Or.inr ⟨Finset.card_le_one.mp h v hv c hc, hf ▸ hu⟩⟩
          · exact ⟨z, 0, fun _ _ _ v hv => (hne ⟨v,hv⟩).elim⟩
      · exact ⟨z, 0, fun h => (hw h).elim⟩
    choose cOf jOf spec using pick
    let oc (w : ℕ) := if h : ∃ c, adj c w then h.choose else z
    have owner_eq (w : ℕ) (c : Fin n) (hbig : 1 < (S w).card) (h : adj c w) : oc w = c := by
      have hex : ∃ c, adj c w := ⟨c,h⟩
      have h' : adj (oc w) w := by simpa [oc, hex] using hex.choose_spec
      by_contra hne
      obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hbig
      exact hc4 (oc w) u c v hne huv ⟨h' u hu, (h u hu).symm, h v hv, (h' v hv).symm⟩
    let R (c : Fin n) := (AS.filter (fun w => cOf w = c)).image jOf
    let B (c : Fin n) := OS.filter (fun w => oc w = c)
    have hlocal (c : Fin n) : ((R c).biUnion (F c)).card ≤ (R c).card + (B c).card := by
      apply dag_union_bound
      intro i hi
      by_cases hgood : i < N ∧ adj c i
      · have hf : F c i = S i := ite_eq_left hgood
        rw [hf] at hi
        have hk : k ≤ i := by by_contra! h; have := hsmall i h; omega
        have hA : A i = false := by
          cases he : A i with
          | false => rfl
          | true => simp [hzero i hk hgood.1 he] at hi
        have ⟨ha,hb⟩ := hparents i hk hgood.1
        have hu := hunion i hk hgood.1 hA
        have hfa : F c (a i) = S (a i) := ite_eq_left ⟨by omega,
          fun x hx => hgood.2 x (hu ▸ Finset.mem_union_left _ hx)⟩
        have hfb : F c (b i) = S (b i) := ite_eq_left ⟨by omega,
          fun x hx => hgood.2 x (hu ▸ Finset.mem_union_right _ hx)⟩
        right
        refine ⟨?_, a i, ha, b i, hb, ?_⟩
        · simp [B, OS, hgood.1, hk, hA, hi, owner_eq i c hi hgood.2]
        · rw [hf,hfa,hfb,hu]
      · simp [F,hgood] at hi
    let E (c : Fin n) := ((R c).biUnion (F c)).image (fun x => s(c,x))
    have subset : G.edgeFinset ⊆ Finset.univ.biUnion E := by
      intro e
      induction e using Sym2.inductionOn with
      | _ u v =>
        intro he
        have huv : G.Adj u v := G.mem_edgeFinset.mp he
        obtain ⟨w,hk,hN,hA,how⟩ := hcover u v huv
        have hw : w ∈ AS := by simp [AS,hN,hk,hA]
        have hj : jOf w ∈ R (cOf w) := Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hw,rfl⟩)
        have member (t : Fin n) (ht : t ∈ F (cOf w) (jOf w)) :
            s(cOf w,t) ∈ Finset.univ.biUnion E :=
          Finset.mem_biUnion.mpr ⟨cOf w, Finset.mem_univ _,
            Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ⟨jOf w,hj,ht⟩)⟩
        rcases how with ⟨hu,hv⟩ | ⟨hv,hu⟩
        · rcases spec w hw u hu v hv with ⟨he,ht⟩ | ⟨he,ht⟩
          · simpa only [he] using member v ht
          · simpa only [he, Sym2.eq_swap] using member u ht
        · rcases spec w hw v hv u hu with ⟨he,ht⟩ | ⟨he,ht⟩
          · simpa only [he, Sym2.eq_swap] using member u ht
          · simpa only [he] using member v ht
    have hrs : (∑ c, (AS.filter (fun w => cOf w = c)).card) = AS.card :=
      (Finset.card_eq_sum_card_fiberwise (f := cOf) (t := Finset.univ) (by simp)).symm
    have hbs : (∑ c, (B c).card) = OS.card :=
      (Finset.card_eq_sum_card_fiberwise (f := oc) (t := Finset.univ) (by simp)).symm
    calc
      G.edgeFinset.card ≤ (Finset.univ.biUnion E).card := Finset.card_le_card subset
      _ ≤ ∑ c, (E c).card := Finset.card_biUnion_le
      _ ≤ ∑ c, ((AS.filter (fun w => cOf w = c)).card + (B c).card) := by
        apply Finset.sum_le_sum
        intro c _
        exact Finset.card_image_le.trans ((hlocal c).trans (Nat.add_le_add_right Finset.card_image_le _))
      _ = _ := by rw [Finset.sum_add_distrib, hrs, hbs]

theorem total_from_model (n k N r L : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : ℕ → Finset (Fin n)) (H : ℕ → Fin n → Fin n → Prop)
    (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hr : r < N) (hrS : S r = ∅) (hrH : ∀ u v, G.Adj u v → H r u v)
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
    (hjoin : ∀ w, k ≤ w → w < N → A w = true →
      ∀ u ∈ S (a w), ∀ v ∈ S (b w), G.Adj u v)
    (hpartition :
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = true)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ (S w).card ≤ 1)).card ≤ L) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      G.edgeFinset.card + T.card ≤ L + 1 := by
  classical
  have hd (w : ℕ) (hk : k ≤ w) (hN : w < N) (hA : A w = true) : Disjoint (S (a w)) (S (b w)) := by
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    exact G.loopless.irrefl t (hjoin w hk hN hA t ht t ht')
  have hside (w : ℕ) (hk : k ≤ w) (hN : w < N) (hA : A w = true) :
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1 := by
    by_contra! hf
    obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hf.1
    obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp hf.2
    have hJ := hjoin w hk hN hA
    exact hc4 u x v y huv hxy ⟨hJ u hu x hx, (hJ v hv x hx).symm, hJ v hv y hy, (hJ u hu y hy).symm⟩
  have births (u v) (huv : G.Adj u v) := edge_birth n k N r S H a b A u v hr
    (hrH u v huv) (by simp [hrS]) (by simp [hrS]) hinput ha hb horS horH handH hd
  have edgeCount := edge_finset_gate_bound n k N G S a b A hc4 hsmall
    (fun w hk hN => ⟨ha w hk hN, hb w hk hN⟩) hzero horS hjoin hside births
  obtain ⟨T,hT,hcard⟩ := cover_half n k N r G S H a b A hr hrS hrH hinput ha hb
    horS horH hside handH (fun f R B step => dag_union_bound f R B step)
  exact ⟨T,hT,by omega⟩

theorem pairCleanBound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (x = (fun _ => false) ∨ (∃ u : Fin n, x = fun z => decide (z = u)) ∨ (∃ u v : Fin n, x = fun z => decide (z = u ∨ z = v))) → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1 := by
  intro n G inst hc4 gs out ops eval clean
  have he : ∀ x : Fin n → Bool, (PEqualNP.CircuitLowerBounds.Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x := by
    intro x
    rw [eval]
    exact decide_eq_true_iff
  apply total_from_model n (n+1) (n+1+gs.length) (clampWire (n+gs.length) out) gs.length G
    (supports gs) (fun w u v => posRead gs w (pairBits u v) = true)
    (firstWire n gs) (secondWire n gs) (andPos n gs) hc4 (root_bound n gs.length out)
    (root_support_empty G gs out he) (root_hits G gs out he) (support_base gs) (hit_base gs)
  · intro w lo _
    exact clamp_lt w _ (by omega)
  · intro w lo _
    exact clamp_lt w _ (by omega)
  · exact support_or G gs ops clean
  · intro w u v lo hi ha h
    simpa only [pos_gate G gs ops clean w lo hi,ha,Bool.false_eq_true,ite_false,Bool.or_eq_true]
      using h
  · intro w u v lo hi ha h
    simpa only [pos_gate G gs ops clean w lo hi,ha,ite_true,Bool.and_eq_true] using h
  · exact support_and G gs clean
  · exact cross_support G gs ops clean
  · exact gate_partition_count n gs.length (andPos n gs) (supports gs)


def wF (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wF_append (gs gs' : List Gate) (w : List Bool) :
    wF (gs ++ gs') w = wF gs' (wF gs w) := by
  simp [wF, List.foldl_append]

theorem wF_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wF gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wF], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wF (g :: gs) w
        = wF gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wF (gs : List Gate) (w : List Bool) :
    (wF gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wF_start gs w
  rw [ht]; simp [hl]

theorem getD_wF (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wF gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wF_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

theorem wire_at (n : ℕ) (pre post : List Gate) (g : Gate) (X : List Bool) (hX : X.length = n) :
    (wF (pre ++ g :: post) X).getD (n + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wF pre X).getD i false) := by
  have h1 : wF (pre ++ g :: post) X = wF post
      (wF pre X ++ [g.op.eval (g.inputs.map fun i => (wF pre X).getD i false)]) := by
    rw [wF_append]; rfl
  have hl : (wF pre X).length = n + pre.length := by
    rw [length_wF]; omega
  rw [h1, getD_wF _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]

-- The value of wire w.
def V (gs : List Gate) (x : List Bool) (w : ℕ) : Bool := (wF gs x).getD w false

theorem eval_eq (gs : List Gate) (out : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, out⟩ x = V gs x out := rfl

theorem V_prefix (pre post : List Gate) (x : List Bool) (w : ℕ) (h : w < x.length + pre.length) :
    V (pre ++ post) x w = V pre x w := by
  unfold V
  rw [wF_append, getD_wF _ _ _ (by rw [length_wF]; exact h)]

theorem gate_val_aux (gs : List Gate) (x : List Bool) (hx : x.length = 14) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (hw : ∀ w ∈ g.inputs, w < 14 + i) :
    V gs x (14 + i) = g.op.eval (g.inputs.map (V gs x)) := by
  obtain ⟨pre, post, hsplit, hlen⟩ := split_at gs i g hg
  subst hsplit
  subst hlen
  have h1 : V (pre ++ g :: post) x (14 + pre.length)
      = g.op.eval (g.inputs.map fun w => (wF pre x).getD w false) :=
    wire_at 14 pre post g x hx
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro w hwm
  exact (V_prefix pre (g :: post) x w (by rw [hx]; exact hw w hwm)).symm

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : ℕ) (h : j < m) :
    (List.ofFn F).getD j d = F ⟨j, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

theorem V_out (gs : List Gate) (x : List Bool) (w : ℕ) (h : x.length + gs.length ≤ w) :
    V gs x w = false := by
  unfold V
  exact List.getD_eq_default _ _ (by rw [length_wF]; exact h)

theorem V_in (gs gs' : List Gate) (x : List Bool) (w : ℕ) (h : w < x.length) :
    V gs x w = V gs' x w := by
  unfold V
  rw [getD_wF _ _ _ h, getD_wF _ _ _ h]

theorem V_gate_some (gs : List Gate) (x : List Bool) (hx : x.length = 14) (i : ℕ)
    (h : V gs x (14 + i) = true) : ∃ g, gs[i]? = some g := by
  have hi : i < gs.length := by
    by_contra hi
    rw [V_out gs x (14 + i) (by rw [hx]; omega)] at h
    exact Bool.false_ne_true h
  exact ⟨gs[i], List.getElem?_eq_getElem hi⟩

theorem orN (gs : List Gate) (x : List Bool) (hx : x.length = 14) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (hw : ∀ w ∈ g.inputs, w < 14 + i) (hop : g.op = GateOp.or) :
    V gs x (14 + i) = true ↔ ∃ w ∈ g.inputs, V gs x w = true := by
  rw [gate_val_aux gs x hx i g hg hw, hop]
  simp [GateOp.eval]

theorem andN (gs : List Gate) (x : List Bool) (hx : x.length = 14) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (hw : ∀ w ∈ g.inputs, w < 14 + i) (hop : g.op = GateOp.and) :
    V gs x (14 + i) = true ↔ ∀ w ∈ g.inputs, V gs x w = true := by
  rw [gate_val_aux gs x hx i g hg hw, hop]
  simp [GateOp.eval]

-- Cone lemmas, from the merged file L_meta_1600.lean.
lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h



-- The Heawood graph.
def hL : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]

def adjB (u v : Fin 14) : Bool := decide ((u.1, v.1) ∈ hL ∨ (v.1, u.1) ∈ hL)

lemma adjB_symm : ∀ u v : Fin 14, adjB u v = adjB v u := by decide +kernel

lemma adjB_irrefl : ∀ u : Fin 14, adjB u u = false := by decide +kernel

lemma noLoop : ∀ a : Fin 14, (a.1, a.1) ∉ hL := by decide +kernel

set_option maxRecDepth 100000 in
lemma adjB_c4 : ∀ a b c d : Fin 14, a ≠ c → b ≠ d →
    ¬ (adjB a b = true ∧ adjB b c = true ∧ adjB c d = true ∧ adjB d a = true) := by
  decide +kernel

def hw : SimpleGraph (Fin 14) := SimpleGraph.fromRel (fun u v => adjB u v = true)

lemma hw_adj (u v : Fin 14) : hw.Adj u v ↔ adjB u v = true := by
  unfold hw
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · rw [adjB_symm]; exact h
  · intro h
    refine ⟨?_, Or.inl h⟩
    rintro rfl
    rw [adjB_irrefl] at h
    exact Bool.false_ne_true h

lemma hw_c4 : ∀ a b c d : Fin 14, a ≠ c → b ≠ d →
    ¬ (hw.Adj a b ∧ hw.Adj b c ∧ hw.Adj c d ∧ hw.Adj d a) := by
  rintro a b c d h1 h2 ⟨p, q, r, s⟩
  exact adjB_c4 a b c d h1 h2
    ⟨(hw_adj _ _).1 p, (hw_adj _ _).1 q, (hw_adj _ _).1 r, (hw_adj _ _).1 s⟩

lemma edge_iff (x : Fin 14 → Bool) :
    (∃ a b : Fin 14, (a.1, b.1) ∈ hL ∧ x a = true ∧ x b = true) ↔
      ∃ u v : Fin 14, hw.Adj u v ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨a, b, h, ha, hb⟩
    refine ⟨a, b, (hw_adj a b).2 ?_, ha, hb⟩
    unfold adjB
    rw [decide_eq_true_eq]
    exact Or.inl h
  · rintro ⟨u, v, h, hu, hv⟩
    have h' := (hw_adj u v).1 h
    unfold adjB at h'
    rw [decide_eq_true_eq] at h'
    rcases h' with h' | h'
    · exact ⟨u, v, h', hu, hv⟩
    · exact ⟨v, u, h', hv, hu⟩

def pairSet : Finset (Fin 14 × Fin 14) :=
  Finset.univ.filter (fun p => p.1 < p.2 ∧ adjB p.1 p.2 = true)

lemma pairSet_card : pairSet.card = 21 := by decide +kernel

lemma hw_edges (inst : Fintype hw.edgeSet) :
    21 ≤ (@SimpleGraph.edgeFinset _ hw inst).card := by
  rw [← pairSet_card]
  refine Finset.card_le_card_of_injOn (fun p => s(p.1, p.2)) ?_ ?_
  · intro p hp
    have hp' : p.1 < p.2 ∧ adjB p.1 p.2 = true := by simpa [pairSet] using hp
    simp only [Finset.mem_coe, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact (hw_adj _ _).2 hp'.2
  · intro p hp q hq h
    have hp' : p.1 < p.2 ∧ adjB p.1 p.2 = true := by simpa [pairSet] using hp
    have hq' : q.1 < q.2 ∧ adjB q.1 q.2 = true := by simpa [pairSet] using hq
    have h' : s(p.1, p.2) = s(q.1, q.2) := h
    rw [Sym2.eq_iff] at h'
    rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso
      have h3 := hp'.1
      rw [h1, h2] at h3
      exact absurd h3 (not_lt.2 hq'.1.le)

def mIdx (v : Fin 14) : Fin 7 :=
  ([0, 1, 2, 3, 4, 5, 6, 1, 2, 5, 0, 6, 3, 4] : List (Fin 7)).getD v.1 0

def mP (i : Fin 7) : Fin 14 := ([0, 1, 2, 3, 4, 5, 6] : List (Fin 14)).getD i.1 0

def mL (i : Fin 7) : Fin 14 := ([10, 7, 8, 12, 13, 9, 11] : List (Fin 14)).getD i.1 0

lemma match_facts : ∀ i : Fin 7,
    adjB (mP i) (mL i) = true ∧ mIdx (mP i) = i ∧ mIdx (mL i) = i := by decide +kernel

lemma cover7 (T : Finset (Fin 14)) (h : ∀ u v : Fin 14, hw.Adj u v → u ∈ T ∨ v ∈ T) :
    7 ≤ T.card := by
  have hs : (Finset.univ : Finset (Fin 7)) ⊆ T.image mIdx := by
    intro i _
    obtain ⟨h1, h2, h3⟩ := match_facts i
    rcases h _ _ ((hw_adj _ _).2 h1) with hh | hh
    · exact Finset.mem_image.2 ⟨_, hh, h2⟩
    · exact Finset.mem_image.2 ⟨_, hh, h3⟩
  have h1 := Finset.card_le_card hs
  have h2 := Finset.card_image_le (s := T) (f := mIdx)
  rw [Finset.card_univ, Fintype.card_fin] at h1
  omega

-- The circuit restricted to the cone of the output gate o.
def newG (C : Circuit) (o : ℕ) : List Gate :=
  C.gates.mapIdx (fun j g => if j = o ∨ InCone 14 C j o then g else ⟨GateOp.or, []⟩)

lemma newG_len (C : Circuit) (o : ℕ) : (newG C o).length = C.gates.length := by
  simp [newG]

lemma newG_get (C : Circuit) (o i : ℕ) (g : Gate) (hg : C.gates[i]? = some g) :
    (newG C o)[i]? = some (if i = o ∨ InCone 14 C i o then g else ⟨GateOp.or, []⟩) := by
  simp [newG, List.getElem?_mapIdx, hg]

lemma newG_inv (C : Circuit) (o i : ℕ) (g' : Gate) (hg : (newG C o)[i]? = some g') :
    ∃ g, C.gates[i]? = some g ∧
      g' = if i = o ∨ InCone 14 C i o then g else ⟨GateOp.or, []⟩ := by
  have hi : i < C.gates.length := by
    have := (List.getElem?_eq_some_iff.1 hg).1
    rw [newG_len] at this
    exact this
  refine ⟨C.gates[i], List.getElem?_eq_getElem hi, ?_⟩
  have h2 := newG_get C o i C.gates[i] (List.getElem?_eq_getElem hi)
  rw [hg] at h2
  exact Option.some.inj h2

lemma inCone_trans (C : Circuit) (i j : ℕ) (hij : InCone 14 C i j) :
    ∀ m, m < C.gates.length → InCone 14 C j m → InCone 14 C i m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hjm
    obtain ⟨w, hw, h1, h2, h3⟩ := (inCone_iff 14 C j m hm).1 hjm
    refine (inCone_iff 14 C i m hm).2 ⟨w, hw, h1, h2, Or.inr ?_⟩
    rcases h3 with h3 | h3
    · rw [← h3]; exact hij
    · exact ih (w - 14) (by omega) (by omega) h3

lemma gate_some (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    C.gates[j]? = some (gateAt C j) := by
  rw [gateAt_eq C j hj]; exact List.getElem?_eq_getElem hj

lemma up_true (C : Circuit) (hM : Monotone2 C) (hRB : ReadsBack 14 C)
    (hno : ¬∃ i j, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
      InCone 14 C i j)
    (x : List Bool) (hx : x.length = 14) (i : ℕ) (hi : (gateAt C i).op = GateOp.and)
    (hv : V C.gates x (14 + i) = true) :
    ∀ j, j < C.gates.length → InCone 14 C i j → V C.gates x (14 + j) = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hc
    obtain ⟨w, hw, h1, h2, h3⟩ := (inCone_iff 14 C i j hj).1 hc
    have hg := gate_some C j hj
    have hop : (gateAt C j).op = GateOp.or := by
      have hm : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
        simpa using (hM (gateAt C j) (List.mem_of_getElem? hg)).1
      rcases hm with h | h
      · exact absurd ⟨i, j, hi, h, hc⟩ hno
      · exact h
    rw [orN C.gates x hx j _ hg (hRB j hj) hop]
    refine ⟨w, hw, ?_⟩
    have hw' : w = 14 + (w - 14) := by omega
    rw [hw']
    rcases h3 with h3 | h3
    · rw [← h3]; exact hv
    · exact ih (w - 14) (by omega) (by omega) h3

lemma same_val (C : Circuit) (hRB : ReadsBack 14 C) (o : ℕ) (ho : o < C.gates.length)
    (x : List Bool) (hx : x.length = 14) :
    ∀ j, j < C.gates.length → (j = o ∨ InCone 14 C j o) →
      V (newG C o) x (14 + j) = V C.gates x (14 + j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hk
    have hg := gate_some C j hj
    have hr := hRB j hj
    have hg' : (newG C o)[j]? = some (gateAt C j) := by
      rw [newG_get C o j _ hg, ite_eq_left_of_eq_true _ _ (eq_true hk)]
    rw [gate_val_aux (newG C o) x hx j _ hg' hr, gate_val_aux C.gates x hx j _ hg hr]
    congr 1
    apply List.map_congr_left
    intro w hw
    have hwlt := hr w hw
    by_cases h14 : w < 14
    · exact V_in _ _ x w (by omega)
    · have hw' : w = 14 + (w - 14) := by omega
      have hc : InCone 14 C (w - 14) j :=
        (inCone_iff 14 C _ j hj).2 ⟨w, hw, by omega, hwlt, Or.inl rfl⟩
      rw [hw']
      refine ih (w - 14) (by omega) (by omega) (Or.inr ?_)
      rcases hk with hk | hk
      · rw [← hk]; exact hc
      · exact inCone_trans C _ j hc o ho hk

theorem core (C : Circuit) (hM : Monotone2 C) (hRB : ReadsBack 14 C)
    (hno : ¬∃ i j, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
      InCone 14 C i j)
    (hf : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ a b : Fin 14, (a.1, b.1) ∈ hL ∧ x a = true ∧ x b = true) : 27 ≤ C.size := by
  have hlen : ∀ x : Fin 14 → Bool, (List.ofFn x).length = 14 := fun x => by simp
  have hev : ∀ x : List Bool, C.eval x = V C.gates x C.output := fun x => rfl
  obtain ⟨o, ho, hout⟩ : ∃ o, o < C.gates.length ∧ C.output = 14 + o := by
    by_cases h1 : C.output < 14
    · exfalso
      have h := (hf (fun z => decide (z.1 = C.output))).1 (by
        rw [hev]
        unfold V
        rw [getD_wF _ _ _ (by simpa using h1), getD_ofFn 14 _ _ _ h1]
        simp)
      obtain ⟨a, b, hab, ha, hb⟩ := h
      have ha' : a.1 = C.output := by simpa using ha
      have hb' : b.1 = C.output := by simpa using hb
      have hab' : a = b := Fin.ext (ha'.trans hb'.symm)
      subst hab'
      exact absurd hab (noLoop a)
    · by_cases h2 : C.output < 14 + C.gates.length
      · exact ⟨C.output - 14, by omega, by omega⟩
      · exfalso
        have h := (hf (fun _ => true)).2 ⟨0, 7, by decide, rfl, rfl⟩
        rw [hev, V_out _ _ _ (by rw [hlen]; omega)] at h
        exact Bool.false_ne_true h
  have hfun : ∀ x : Fin 14 → Bool, V C.gates (List.ofFn x) (14 + o) = true ↔
      ∃ u v : Fin 14, hw.Adj u v ∧ x u = true ∧ x v = true := by
    intro x
    rw [← hout, ← hev, hf x]
    exact edge_iff x
  have hB := fun x : Fin 14 → Bool => same_val C hRB o ho (List.ofFn x) (hlen x)
  have hbin : ∀ g ∈ newG C o, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
    obtain ⟨g0, hg0, he⟩ := newG_inv C o i _ (List.getElem?_eq_getElem hi)
    rw [he]
    have hm := hM g0 (List.mem_of_getElem? hg0)
    split_ifs
    · exact ⟨by simpa using hm.1, hm.2⟩
    · exact ⟨Or.inr rfl, by simp⟩
  have key := @pairCleanBound 14 hw (fun u v => decidable_of_iff _ (hw_adj u v).symm) hw_c4 (newG C o) C.output hbin
  have key2 := key (by
    intro x
    have h1 : Circuit.eval ⟨newG C o, C.output⟩ (List.ofFn x)
        = V C.gates (List.ofFn x) (14 + o) := by
      rw [eval_eq, hout]; exact hB x o ho (Or.inl rfl)
    rw [h1]
    apply Bool.eq_iff_iff.2
    simp only [decide_eq_true_eq]
    exact hfun x) (by
    intro i x _ hop hv
    have hi : i.1 < C.gates.length := lt_of_lt_of_eq i.2 (newG_len C o)
    obtain ⟨g0, hg0, he⟩ := newG_inv C o i.1 ((newG C o).get i) (by simp)
    have hk : i.1 = o ∨ InCone 14 C i.1 o := by
      by_contra hk
      rw [he, ite_eq_right_of_eq_false _ _ (eq_false hk)] at hop
      simp at hop
    rw [he, ite_eq_left_of_eq_true _ _ (eq_true hk)] at hop
    have hga : gateAt C i.1 = g0 := by
      rw [gateAt_eq C _ hi]
      exact Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hg0)
    have hv' : V C.gates (List.ofFn x) (14 + i.1) = true := by
      rw [← hB x i.1 hi hk]; exact hv
    apply (hfun x).1
    rcases hk with hk | hk
    · rw [← hk]; exact hv'
    · exact up_true C hM hRB hno _ (hlen x) i.1 (by rw [hga]; exact hop) hv' o ho hk)
  obtain ⟨T, hT, hcard⟩ := key2
  rw [newG_len] at hcard
  have h7 := cover7 T hT
  have h28 := le_trans (Nat.add_le_add (hw_edges _) h7) hcard
  show 27 ≤ C.gates.length
  omega

end Fano1983

theorem Fano1983 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (14 : ℕ) x1 → (¬∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x4 x5) → (∀ (x5 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (14 : ℕ)) (x7 : Fin (14 : ℕ)), (↑x6, ↑x7) ∈ [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))] ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → (27 : ℕ) ≤ x1.size := by
  intro C hM hRB hno hf
  exact Fano1983.core C hM hRB hno hf

-- The pair-clean circuit argument is adapted from the checked L-meta-1602 proof.
-- The incidence graph has 105 edges and a matching of size 21. An independent
-- pair must therefore activate an AND in any circuit of size at most 124.
-- Cyclic shifts and point-line duality send this pair into the specified input.
namespace Clean1892

namespace Clean

-- The general pair-clean bound and its helpers adapt the checked proof of L-meta-1602.

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj


def posRead {n : ℕ} (gs : List Gate) (w : ℕ) (x : Fin n → Bool) : Bool :=
  match w with
  | 0 => false
  | i + 1 => (wiresFrom gs (List.ofFn x)).getD i false

def clampWire (lim i : ℕ) : ℕ := if i < lim then i + 1 else 0

def gateAtPos (n : ℕ) (gs : List Gate) (w : ℕ) : Gate :=
  gs.getD (w - (n + 1)) ⟨GateOp.or, []⟩

def firstWire (n : ℕ) (gs : List Gate) (w : ℕ) : ℕ :=
  clampWire (w-1) ((gateAtPos n gs w).inputs.getD 0 (w-1))

def secondWire (n : ℕ) (gs : List Gate) (w : ℕ) : ℕ :=
  clampWire (w-1) ((gateAtPos n gs w).inputs.getD 1 ((gateAtPos n gs w).inputs.getD 0 (w-1)))

def andPos (n : ℕ) (gs : List Gate) (w : ℕ) : Bool :=
  match (gateAtPos n gs w).op with
  | GateOp.and => true
  | _ => false

lemma clamp_lt (w i : ℕ) (hw : 0 < w) : clampWire (w-1) i < w := by
  unfold clampWire
  split <;> omega

lemma pos_clamp {n : ℕ} (gs : List Gate) (lim i : ℕ) (x : Fin n → Bool) :
    posRead gs (clampWire lim i) x =
    (if i < lim then (wiresFrom gs (List.ofFn x)).getD i false else false) := by
  simp only [clampWire]
  split <;> rfl

lemma pos_input {n : ℕ} (gs : List Gate) (i : ℕ) (hi : i < n) (x : Fin n → Bool) :
    posRead gs (i+1) x = x ⟨i,hi⟩ := by
  change (wiresFrom gs (List.ofFn x)).getD i false = x ⟨i,hi⟩
  rw [getD_wiresFrom_lt _ _ _ (by simpa using hi)]
  rw [List.getD_eq_getElem (List.ofFn x) false (by simpa using hi),List.getElem_ofFn]

lemma pos_mono {n : ℕ} (gs : List Gate)
    (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : ℕ) (x y : Fin n → Bool) (le : ∀ i, x i = true → y i = true) :
    posRead gs w x = true → posRead gs w y = true := by
  cases w with
  | zero => simp [posRead]
  | succ i =>
    apply wiresFrom_mono gs ops _ _ (by simp)
    intro j h
    by_cases hj : j < n
    · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn] at h ⊢
      exact le _ h
    · rw [List.getD_eq_default _ _ (by simp; omega)] at h
      contradiction

def edgeTrue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

def singletonBits {n : ℕ} (u : Fin n) : Fin n → Bool := fun z => decide (z = u)
def pairBits {n : ℕ} (u v : Fin n) : Fin n → Bool := fun z => decide (z = u ∨ z = v)

lemma edge_single {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) :
    ¬ edgeTrue G (singletonBits u) := by
  rintro ⟨i,j,h,hi,hj⟩
  simp only [singletonBits, decide_eq_true_eq] at hi hj
  subst i
  subst j
  exact G.loopless.irrefl u h

lemma edge_pair {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    edgeTrue G (pairBits u v) ↔ G.Adj u v := by
  constructor
  · rintro ⟨i,j,h,hi,hj⟩
    simp only [pairBits, decide_eq_true_eq] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (G.loopless.irrefl _ h).elim
    · exact h
    · exact h.symm
    · exact (G.loopless.irrefl _ h).elim
  · intro h
    exact ⟨u,v,h,by simp [pairBits],by simp [pairBits]⟩

lemma binary_eval (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (hl : l.length ≤ 2) (nonempty : op = GateOp.and → l ≠ [])
    (v : ℕ → Bool) (lim : ℕ) (vd : v lim = false) :
    op.eval (l.map v) =
      (if (match op with | GateOp.and => true | _ => false) then
        v (l.getD 0 lim) && v (l.getD 1 (l.getD 0 lim))
       else v (l.getD 0 lim) || v (l.getD 1 (l.getD 0 lim))) := by
  cases l with
  | nil =>
    rcases hop with rfl | rfl
    · exact (nonempty rfl rfl).elim
    · simp [GateOp.eval,vd]
  | cons i t =>
    cases t with
    | nil => rcases hop with rfl | rfl <;> simp [GateOp.eval]
    | cons j t =>
      have ht : t = [] := List.length_eq_zero_iff.mp (by simpa using hl)
      subst t
      rcases hop with rfl | rfl <;> simp [GateOp.eval]

def supports {n : ℕ} (gs : List Gate) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => posRead gs w (singletonBits u) = true

lemma mem_support {n : ℕ} (gs : List Gate) (w : ℕ) (u : Fin n) :
    u ∈ supports gs w ↔ posRead gs w (singletonBits u) = true := by simp [supports]


def cleanOn {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) : Prop :=
  ∀ (j : Fin gs.length) (x : Fin n → Bool),
    (x = (fun _ => false) ∨ (∃ u, x = singletonBits u) ∨ (∃ u v, x = pairBits u v)) →
    (gs.get j).op = GateOp.and →
    (wiresFrom gs (List.ofFn x)).getD (n + j.val) false = true → edgeTrue G x

def binaryOps (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma gateAt_index {n : ℕ} (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    gateAtPos n gs (n+j+1) = gs[j] := by
  unfold gateAtPos
  rw [show n+j+1-(n+1) = j by omega,List.getD_eq_getElem _ _ hj]

lemma pos_gate {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs)
    (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length) (x : Fin n → Bool) :
    posRead gs w x =
      (if andPos n gs w then
        posRead gs (firstWire n gs w) x && posRead gs (secondWire n gs w) x
       else posRead gs (firstWire n gs w) x || posRead gs (secondWire n gs w) x) := by
  let j := w-(n+1)
  have hj : j < gs.length := by dsimp [j]; omega
  have hw : w = n+j+1 := by dsimp [j]; omega
  have hg := ops _ (List.getElem_mem hj)
  have nonempty : gs[j].op = GateOp.and → gs[j].inputs ≠ [] := by
    intro ha hempty
    let z : Fin n → Bool := fun _ => false
    have eqg := getD_wiresFrom_gate gs (List.ofFn z) j hj
    simp only [List.length_ofFn, hempty, List.map_nil, ha, GateOp.eval, List.all_nil] at eqg
    obtain ⟨u,v,_,h,_⟩ := clean ⟨j,hj⟩ z (Or.inl rfl) ha eqg
    contradiction
  rw [hw]
  simp only [firstWire, secondWire, andPos, gateAt_index gs j hj, Nat.add_sub_cancel, pos_clamp]
  change (wiresFrom gs (List.ofFn x)).getD (n+j) false = _
  have h := getD_wiresFrom_gate gs (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  rw [h]
  exact binary_eval gs[j].op hg.1 gs[j].inputs hg.2 nonempty
    (fun i => if i < n+j then (wiresFrom gs (List.ofFn x)).getD i false else false)
    (n+j) (by simp)

lemma pos_clean {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length)
    (ha : andPos n gs w = true) (x : Fin n → Bool)
    (hx : x = (fun _ => false) ∨ (∃ u, x = singletonBits u) ∨ (∃ u v, x = pairBits u v)) :
    posRead gs w x = true → edgeTrue G x := by
  let j := w-(n+1)
  have hj : j < gs.length := by dsimp [j]; omega
  have hw : w = n+j+1 := by dsimp [j]; omega
  rw [hw] at ha ⊢
  simp only [andPos, gateAt_index gs j hj] at ha
  have hop : gs[j].op = GateOp.and := by
    cases h : gs[j].op <;> simp_all
  exact clean ⟨j,hj⟩ x hx hop

lemma support_base {n : ℕ} (gs : List Gate) (w : ℕ) (hw : w < n+1) :
    (supports (n:=n) gs w).card ≤ 1 := by
  cases w with
  | zero => simp [supports,posRead]
  | succ i =>
    have hi : i < n := by omega
    have hs : supports gs (i+1) = {⟨i,hi⟩} := by
      ext u
      simp [mem_support,pos_input gs i hi,singletonBits,eq_comm]
    simp [hs]

lemma hit_base {n : ℕ} (gs : List Gate) (w : ℕ) (u v : Fin n) (hw : w < n+1) :
    posRead gs w (pairBits u v) = true → u ∈ supports gs w ∨ v ∈ supports gs w := by
  cases w with
  | zero => simp [posRead]
  | succ i =>
    have hi : i<n := by omega
    simp [mem_support,pos_input gs i hi,pairBits,singletonBits]

lemma support_and {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length)
    (ha : andPos n gs w = true) : supports (n:=n) gs w = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  exact edge_single G u (pos_clean G gs clean w lo hi ha _ (Or.inr (Or.inl ⟨u, rfl⟩)) ((mem_support gs w u).mp hu))

lemma support_or {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w)
    (hi : w < n+1+gs.length) (ha : andPos n gs w = false) :
    supports (n:=n) gs w = supports gs (firstWire n gs w) ∪ supports gs (secondWire n gs w) := by
  ext u
  simp only [Finset.mem_union,mem_support,pos_gate G gs ops clean w lo hi,ha]
  simp

lemma cross_support {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w)
    (hi : w < n+1+gs.length) (ha : andPos n gs w = true)
    (u : Fin n) (hu : u ∈ supports gs (firstWire n gs w))
    (v : Fin n) (hv : v ∈ supports gs (secondWire n gs w)) : G.Adj u v := by
  apply (edge_pair G u v).mp
  apply pos_clean G gs clean w lo hi ha _ (Or.inr (Or.inr ⟨u, v, rfl⟩))
  rw [pos_gate G gs ops clean w lo hi,ha]
  simp only [ite_true, Bool.and_eq_true]
  have hm := pos_mono (n:=n) gs (fun g h => (ops g h).1)
  constructor
  · apply hm (firstWire n gs w) (singletonBits u) (pairBits u v) _ ((mem_support _ _ _).mp hu)
    intro i ht
    simp only [singletonBits,decide_eq_true_eq] at ht
    simp [pairBits,ht]
  · apply hm (secondWire n gs w) (singletonBits v) (pairBits u v) _ ((mem_support _ _ _).mp hv)
    intro i ht
    simp only [singletonBits,decide_eq_true_eq] at ht
    simp [pairBits,ht]


lemma root_read {n : ℕ} (gs : List Gate) (out : ℕ) (x : Fin n → Bool) :
    posRead gs (clampWire (n+gs.length) out) x = (Circuit.mk gs out).eval (List.ofFn x) := by
  rw [pos_clamp]
  change (if out < n+gs.length then _ else _) = (wiresFrom gs (List.ofFn x)).getD out false
  split_ifs with h
  · rfl
  · symm
    apply List.getD_eq_default
    simpa only [length_wiresFrom, List.length_ofFn] using Nat.le_of_not_lt h

lemma root_bound (n len out : ℕ) : clampWire (n+len) out < n+1+len := by
  unfold clampWire
  split <;> omega

lemma root_support_empty {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (out : ℕ)
    (heval : ∀ x, (Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x) :
    supports (n:=n) gs (clampWire (n+gs.length) out) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u h
  apply edge_single G u
  apply (heval _).mp
  rw [← root_read]
  exact (mem_support _ _ _).mp h

lemma root_hits {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (out : ℕ)
    (heval : ∀ x, (Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x) :
    ∀ u v, G.Adj u v → posRead gs (clampWire (n+gs.length) out) (pairBits u v) = true := by
  intro u v h
  rw [root_read,heval]
  exact (edge_pair G u v).mpr h

theorem countUnion {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
    (paid : Finset ℕ) (m : ℕ)
    (step : ∀ w < m, 1 < (support w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ support w ⊆ cs.biUnion support ∧
      cs.card ≤ 1 + (if w ∈ paid then 1 else 0))
    (roots : Finset ℕ) (hr : roots ⊆ Finset.range m) :
    (roots.biUnion support).card ≤ roots.card + ((Finset.range m) ∩ paid).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have : roots = ∅ := by simpa using hr
    simp [this]
  | succ m ih =>
    have old := ih (fun w hw => step w (by omega))
    have hpre : roots.erase m ⊆ Finset.range m := by
      intro w hw
      have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      have hlt := Finset.mem_range.mp (hr hmem)
      exact Finset.mem_range.mpr (by omega)
    have hcost : ((Finset.range (m + 1)) ∩ paid).card =
        ((Finset.range m) ∩ paid).card + (if m ∈ paid then 1 else 0) := by
      by_cases h : m ∈ paid
      · have he : Finset.range (m + 1) ∩ paid = insert m (Finset.range m ∩ paid) := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
      · have he : Finset.range (m + 1) ∩ paid = Finset.range m ∩ paid := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
    rw [hcost]
    by_cases hm : m ∈ roots
    · have hrins := Finset.insert_erase hm
      have hroots : (roots.erase m).card + 1 = roots.card :=
        Finset.card_erase_add_one hm
      by_cases hb : 1 < (support m).card
      · obtain ⟨cs, hcpre, hcov, hcard⟩ := step m (by omega) hb
        have hsub : roots.biUnion support ⊆ ((roots.erase m) ∪ cs).biUnion support := by
          intro a ha
          obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases heq : w = m
          · subst w
            obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp (hcov haw)
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hav⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hw⟩), haw⟩
        have hh := old ((roots.erase m) ∪ cs) (Finset.union_subset hpre hcpre)
        have hh' := Finset.card_le_card hsub
        have hu := Finset.card_union_le (roots.erase m) cs
        omega
      · have hh := old (roots.erase m) hpre
        have he : roots.biUnion support = support m ∪ (roots.erase m).biUnion support := by
          conv_lhs => rw [← hrins]
          rw [Finset.biUnion_insert]
        rw [he]
        have hu := Finset.card_union_le (support m) ((roots.erase m).biUnion support)
        omega
    · rw [Finset.erase_eq_of_notMem hm] at hpre
      have hh := old roots hpre
      omega

theorem dag_union_bound {α : Type*} [DecidableEq α] (f : ℕ → Finset α) (R B : Finset ℕ)
    (step : ∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
      (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) :
    (R.biUnion f).card ≤ R.card + B.card := by
  classical
  let m := R.sup id + 1
  have hr : R ⊆ Finset.range m := by
    intro w hw
    have h : w ≤ R.sup id := Finset.le_sup (f := id) hw
    exact Finset.mem_range.mpr (by dsimp [m]; omega)
  have haux : (R.biUnion f).card ≤ R.card + (Finset.range m ∩ B).card := by
    apply countUnion f B m _ R hr
    intro i _ hi
    rcases step i hi with ⟨a, ha, hsub⟩ | ⟨hiB, a, ha, b, hb, hsub⟩
    · refine ⟨{a}, ?_, ?_, ?_⟩
      · simpa using ha
      · simpa using hsub
      · simp
    · refine ⟨{a,b}, ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Finset.mem_range.mpr ha
        · rw [Finset.mem_singleton.mp hw]
          exact Finset.mem_range.mpr hb
      · simpa using hsub
      · simp only [hiB, ite_true]
        exact Finset.card_le_two
  have hl := Finset.card_le_card (Finset.inter_subset_right (s₁ := Finset.range m) (s₂ := B))
  omega

theorem gate_partition_count (n len : ℕ) (A : ℕ → Bool) (S : ℕ → Finset (Fin n)) :
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = true)).card +
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = false ∧
      1 < (S w).card)).card +
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = false ∧
      (S w).card ≤ 1)).card ≤ len := by
  classical
  let gates := Finset.range (n + 1 + len)
  let ands := gates.filter (fun w => n + 1 ≤ w ∧ A w = true)
  let large := gates.filter (fun w => n + 1 ≤ w ∧ A w = false ∧ 1 < (S w).card)
  let small := gates.filter (fun w => n + 1 ≤ w ∧ A w = false ∧ (S w).card ≤ 1)
  change ands.card + large.card + small.card ≤ len
  have hdis : Disjoint ands large := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    have a := (Finset.mem_filter.mp h₁).2.2
    have b := (Finset.mem_filter.mp h₂).2.2.1
    simp_all
  have hdis' : Disjoint (ands ∪ large) small := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    have b := (Finset.mem_filter.mp h₂).2.2
    rcases Finset.mem_union.mp h₁ with ha | hl
    · have a := (Finset.mem_filter.mp ha).2.2
      simp_all
    · have a := (Finset.mem_filter.mp hl).2.2.2
      exact (Nat.not_lt_of_ge b.2) a
  have hsub : (ands ∪ large) ∪ small ⊆ Finset.Ico (n+1) (n+1+len) := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · rcases Finset.mem_union.mp h with h | h <;>
        exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,
          Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
    · exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,
        Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
  rw [← Finset.card_union_of_disjoint hdis, ← Finset.card_union_of_disjoint hdis']
  simpa using Finset.card_le_card hsub

def coverCert {n : ℕ} (k N : ℕ) (S : ℕ → Finset (Fin n))
    (a b : ℕ → ℕ) (A : ℕ → Bool)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w) (w : ℕ) : Finset (Fin n) :=
  if (S w).card ≤ 1 then
    if _hg : k ≤ w ∧ w < N then
      if A w = true then
        if (S (a w)).card ≤ 1 then coverCert k N S a b A ha hb (a w)
        else coverCert k N S a b A ha hb (b w)
      else
        coverCert k N S a b A ha hb (a w) ∪ coverCert k N S a b A ha hb (b w)
    else S w
  else ∅
termination_by w
decreasing_by all_goals first | exact ha _ _hg.1 _hg.2 | exact hb _ _hg.1 _hg.2

theorem cover_half (n k N r : ℕ) (G : SimpleGraph (Fin n))
    (S : ℕ → Finset (Fin n)) (H : ℕ → Fin n → Fin n → Prop)
    (a b : ℕ → ℕ) (A : ℕ → Bool) (hr : r < N) (hrS : S r = ∅)
    (hrH : ∀ u v, G.Adj u v → H r u v)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handS : ∀ w, k ≤ w → w < N → A w = true →
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hdag : ∀ (f : ℕ → Finset (Fin n)) (R B : Finset ℕ),
      (∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
        (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) →
      (R.biUnion f).card ≤ R.card + B.card) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      T.card ≤ 1 + ((Finset.range N).filter fun w =>
        k ≤ w ∧ A w = false ∧ (S w).card ≤ 1).card := by
  let f := coverCert k N S a b A ha hb
  let B := (Finset.range N).filter fun w => k ≤ w ∧ A w = false ∧ (S w).card ≤ 1
  have feq (w : ℕ) : f w =
      if (S w).card ≤ 1 then
        if k ≤ w ∧ w < N then
          if A w = true then
            if (S (a w)).card ≤ 1 then f (a w) else f (b w)
          else f (a w) ∪ f (b w)
        else S w
      else ∅ := by
    exact coverCert.eq_1 ..
  have hit : ∀ w, w < N → (S w).card ≤ 1 →
      ∀ u v, H w u v → u ∈ f w ∨ v ∈ f w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw ht u v hwuv
      rw [feq, ite_eq_left ht]
      by_cases hkw : k ≤ w
      · rw [ite_eq_left ⟨hkw, hw⟩]
        cases hg : A w with
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          have heq := horS w hkw hw hg
          have hta : (S (a w)).card ≤ 1 := by
            apply (Finset.card_le_card _).trans ht
            rw [heq]
            exact Finset.subset_union_left
          have htb : (S (b w)).card ≤ 1 := by
            apply (Finset.card_le_card _).trans ht
            rw [heq]
            exact Finset.subset_union_right
          have hia := ha w hkw hw
          have hib := hb w hkw hw
          rcases horH w u v hkw hw hg hwuv with h | h
          · have hitA := ih _ hia (hia.trans hw) hta u v h
            simp only [Finset.mem_union]
            tauto
          · have hitB := ih _ hib (hib.trans hw) htb u v h
            simp only [Finset.mem_union]
            tauto
        | true =>
          simp only [ite_true]
          have hz := handH w u v hkw hw hg hwuv
          by_cases htA : (S (a w)).card ≤ 1
          · rw [ite_eq_left htA]
            have hl := ha w hkw hw
            exact ih _ hl (hl.trans hw) htA u v hz.1
          · rw [ite_eq_right htA]
            have hl := hb w hkw hw
            exact ih _ hl (hl.trans hw) ((handS w hkw hw hg).resolve_left htA) u v hz.2
      · rw [ite_eq_right (fun h => hkw h.1)]
        exact hinput w u v (Nat.lt_of_not_ge hkw) hwuv
  refine ⟨f r, fun u v huv => hit r hr (by simp [hrS]) u v (hrH u v huv), ?_⟩
  have hstep (w : ℕ) (hw : 1 < (f w).card) :
      (∃ j < w, f w ⊆ f j) ∨
        (w ∈ B ∧ ∃ i < w, ∃ j < w, f w ⊆ f i ∪ f j) := by
    have ht : (S w).card ≤ 1 := by
      by_contra ht
      rw [feq, ite_eq_right ht] at hw
      simp at hw
    have hg : k ≤ w ∧ w < N := by
      by_contra h
      rw [feq, ite_eq_left ht, ite_eq_right h] at hw
      omega
    have hia := ha w hg.1 hg.2
    have hib := hb w hg.1 hg.2
    cases hop : A w with
    | false =>
      right
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg.2, hg.1, hop, ht⟩,
        a w, hia, b w, hib, ?_⟩
      rw [feq, ite_eq_left ht, ite_eq_left hg, hop]
      simp
    | true =>
      left
      by_cases htA : (S (a w)).card ≤ 1
      · refine ⟨a w, hia, ?_⟩
        rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_left htA]
      · refine ⟨b w, hib, ?_⟩
        rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_right htA]
  simpa [B] using hdag f {r} B hstep

theorem edge_birth (n k N r : ℕ) (S : ℕ → Finset (Fin n))
    (H : ℕ → Fin n → Fin n → Prop) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (x y : Fin n) (hr : r < N) (hxy : H r x y) (hx : x ∉ S r) (hy : y ∉ S r)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hdisj : ∀ w, k ≤ w → w < N → A w = true → Disjoint (S (a w)) (S (b w))) :
    ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
      ((x ∈ S (a w) ∧ y ∈ S (b w)) ∨ (y ∈ S (a w) ∧ x ∈ S (b w))) := by
  induction r using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hkw : k ≤ w
    · have hia := ha w hkw hr
      have hib := hb w hkw hr
      cases hop : A w with
      | false =>
        have hSw := horS w hkw hr hop
        rw [hSw, Finset.mem_union] at hx hy
        rcases horH w x y hkw hr hop hxy with h | h
        · exact ih _ hia (hia.trans hr) h (fun h => hx (.inl h)) (fun h => hy (.inl h))
        · exact ih _ hib (hib.trans hr) h (fun h => hx (.inr h)) (fun h => hy (.inr h))
      | true =>
        have htrue := handH w x y hkw hr hop hxy
        by_cases hsa : x ∈ S (a w) ∨ y ∈ S (a w)
        · by_cases hsb : x ∈ S (b w) ∨ y ∈ S (b w)
          · refine ⟨w, hkw, hr, hop, ?_⟩
            have hd := Finset.disjoint_left.mp (hdisj w hkw hr hop)
            rcases hsa with hax | hay <;> rcases hsb with hbx | hby
            · exact False.elim (hd hax hbx)
            · exact Or.inl ⟨hax, hby⟩
            · exact Or.inr ⟨hay, hbx⟩
            · exact False.elim (hd hay hby)
          · exact ih _ hib (hib.trans hr) htrue.2 (fun h => hsb (.inl h)) (fun h => hsb (.inr h))
        · exact ih _ hia (hia.trans hr) htrue.1 (fun h => hsa (.inl h)) (fun h => hsa (.inr h))
    · rcases hinput w x y (Nat.lt_of_not_ge hkw) hxy with h | h
      · exact False.elim (hx h)
      · exact False.elim (hy h)

theorem edge_finset_gate_bound (n k N : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
    (hunion : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (hjoin : ∀ w, k ≤ w → w < N → A w = true →
      ∀ u ∈ S (a w), ∀ v ∈ S (b w), G.Adj u v)
    (hside : ∀ w, k ≤ w → w < N → A w = true →
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (hcover : ∀ u v, G.Adj u v → ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
      ((u ∈ S (a w) ∧ v ∈ S (b w)) ∨ (v ∈ S (a w) ∧ u ∈ S (b w)))) :
    G.edgeFinset.card ≤
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = true)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)).card := by
  classical
  cases isEmpty_or_nonempty (Fin n) with
  | inl h =>
    have := h
    have he : G.edgeFinset = ∅ := Finset.eq_empty_of_forall_notMem (fun e => isEmptyElim e)
    simp [he]
  | inr hn =>
    let z := Classical.choice hn
    let AS := (Finset.range N).filter (fun w => k ≤ w ∧ A w = true)
    let OS := (Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)
    let adj (c : Fin n) (w : ℕ) := ∀ x ∈ S w, G.Adj c x
    let F (c : Fin n) (w : ℕ) := if w < N ∧ adj c w then S w else ∅
    have pick : ∀ w, ∃ (c : Fin n) (j : ℕ), w ∈ AS →
        ∀ u ∈ S (a w), ∀ v ∈ S (b w),
          (u = c ∧ v ∈ F c j) ∨ (v = c ∧ u ∈ F c j) := by
      intro w
      by_cases hw : w ∈ AS
      · obtain ⟨hN, hk, hA⟩ : w < N ∧ k ≤ w ∧ A w = true := by simpa [AS] using hw
        obtain ⟨ha,hb⟩ := hparents w hk hN
        have hJ := hjoin w hk hN hA
        rcases hside w hk hN hA with h | h
        · by_cases hne : (S (a w)).Nonempty
          · obtain ⟨c,hc⟩ := hne
            have hf : F c (b w) = S (b w) := ite_eq_left ⟨by omega, hJ c hc⟩
            exact ⟨c, b w, fun _ u hu v hv => Or.inl ⟨Finset.card_le_one.mp h u hu c hc, hf ▸ hv⟩⟩
          · exact ⟨z, 0, fun _ u hu => (hne ⟨u,hu⟩).elim⟩
        · by_cases hne : (S (b w)).Nonempty
          · obtain ⟨c,hc⟩ := hne
            have hf : F c (a w) = S (a w) := ite_eq_left ⟨by omega, fun x hx => (hJ x hx c hc).symm⟩
            exact ⟨c, a w, fun _ u hu v hv => Or.inr ⟨Finset.card_le_one.mp h v hv c hc, hf ▸ hu⟩⟩
          · exact ⟨z, 0, fun _ _ _ v hv => (hne ⟨v,hv⟩).elim⟩
      · exact ⟨z, 0, fun h => (hw h).elim⟩
    choose cOf jOf spec using pick
    let oc (w : ℕ) := if h : ∃ c, adj c w then h.choose else z
    have owner_eq (w : ℕ) (c : Fin n) (hbig : 1 < (S w).card) (h : adj c w) : oc w = c := by
      have hex : ∃ c, adj c w := ⟨c,h⟩
      have h' : adj (oc w) w := by simpa [oc, hex] using hex.choose_spec
      by_contra hne
      obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hbig
      exact hc4 (oc w) u c v hne huv ⟨h' u hu, (h u hu).symm, h v hv, (h' v hv).symm⟩
    let R (c : Fin n) := (AS.filter (fun w => cOf w = c)).image jOf
    let B (c : Fin n) := OS.filter (fun w => oc w = c)
    have hlocal (c : Fin n) : ((R c).biUnion (F c)).card ≤ (R c).card + (B c).card := by
      apply dag_union_bound
      intro i hi
      by_cases hgood : i < N ∧ adj c i
      · have hf : F c i = S i := ite_eq_left hgood
        rw [hf] at hi
        have hk : k ≤ i := by by_contra! h; have := hsmall i h; omega
        have hA : A i = false := by
          cases he : A i with
          | false => rfl
          | true => simp [hzero i hk hgood.1 he] at hi
        have ⟨ha,hb⟩ := hparents i hk hgood.1
        have hu := hunion i hk hgood.1 hA
        have hfa : F c (a i) = S (a i) := ite_eq_left ⟨by omega,
          fun x hx => hgood.2 x (hu ▸ Finset.mem_union_left _ hx)⟩
        have hfb : F c (b i) = S (b i) := ite_eq_left ⟨by omega,
          fun x hx => hgood.2 x (hu ▸ Finset.mem_union_right _ hx)⟩
        right
        refine ⟨?_, a i, ha, b i, hb, ?_⟩
        · simp [B, OS, hgood.1, hk, hA, hi, owner_eq i c hi hgood.2]
        · rw [hf,hfa,hfb,hu]
      · simp [F,hgood] at hi
    let E (c : Fin n) := ((R c).biUnion (F c)).image (fun x => s(c,x))
    have subset : G.edgeFinset ⊆ Finset.univ.biUnion E := by
      intro e
      induction e using Sym2.inductionOn with
      | _ u v =>
        intro he
        have huv : G.Adj u v := G.mem_edgeFinset.mp he
        obtain ⟨w,hk,hN,hA,how⟩ := hcover u v huv
        have hw : w ∈ AS := by simp [AS,hN,hk,hA]
        have hj : jOf w ∈ R (cOf w) := Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hw,rfl⟩)
        have member (t : Fin n) (ht : t ∈ F (cOf w) (jOf w)) :
            s(cOf w,t) ∈ Finset.univ.biUnion E :=
          Finset.mem_biUnion.mpr ⟨cOf w, Finset.mem_univ _,
            Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ⟨jOf w,hj,ht⟩)⟩
        rcases how with ⟨hu,hv⟩ | ⟨hv,hu⟩
        · rcases spec w hw u hu v hv with ⟨he,ht⟩ | ⟨he,ht⟩
          · simpa only [he] using member v ht
          · simpa only [he, Sym2.eq_swap] using member u ht
        · rcases spec w hw v hv u hu with ⟨he,ht⟩ | ⟨he,ht⟩
          · simpa only [he, Sym2.eq_swap] using member u ht
          · simpa only [he] using member v ht
    have hrs : (∑ c, (AS.filter (fun w => cOf w = c)).card) = AS.card :=
      (Finset.card_eq_sum_card_fiberwise (f := cOf) (t := Finset.univ) (by simp)).symm
    have hbs : (∑ c, (B c).card) = OS.card :=
      (Finset.card_eq_sum_card_fiberwise (f := oc) (t := Finset.univ) (by simp)).symm
    calc
      G.edgeFinset.card ≤ (Finset.univ.biUnion E).card := Finset.card_le_card subset
      _ ≤ ∑ c, (E c).card := Finset.card_biUnion_le
      _ ≤ ∑ c, ((AS.filter (fun w => cOf w = c)).card + (B c).card) := by
        apply Finset.sum_le_sum
        intro c _
        exact Finset.card_image_le.trans ((hlocal c).trans (Nat.add_le_add_right Finset.card_image_le _))
      _ = _ := by rw [Finset.sum_add_distrib, hrs, hbs]

theorem total_from_model (n k N r L : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : ℕ → Finset (Fin n)) (H : ℕ → Fin n → Fin n → Prop)
    (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hr : r < N) (hrS : S r = ∅) (hrH : ∀ u v, G.Adj u v → H r u v)
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
    (hjoin : ∀ w, k ≤ w → w < N → A w = true →
      ∀ u ∈ S (a w), ∀ v ∈ S (b w), G.Adj u v)
    (hpartition :
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = true)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ (S w).card ≤ 1)).card ≤ L) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      G.edgeFinset.card + T.card ≤ L + 1 := by
  classical
  have hd (w : ℕ) (hk : k ≤ w) (hN : w < N) (hA : A w = true) : Disjoint (S (a w)) (S (b w)) := by
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    exact G.loopless.irrefl t (hjoin w hk hN hA t ht t ht')
  have hside (w : ℕ) (hk : k ≤ w) (hN : w < N) (hA : A w = true) :
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1 := by
    by_contra! hf
    obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hf.1
    obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp hf.2
    have hJ := hjoin w hk hN hA
    exact hc4 u x v y huv hxy ⟨hJ u hu x hx, (hJ v hv x hx).symm, hJ v hv y hy, (hJ u hu y hy).symm⟩
  have births (u v) (huv : G.Adj u v) := edge_birth n k N r S H a b A u v hr
    (hrH u v huv) (by simp [hrS]) (by simp [hrS]) hinput ha hb horS horH handH hd
  have edgeCount := edge_finset_gate_bound n k N G S a b A hc4 hsmall
    (fun w hk hN => ⟨ha w hk hN, hb w hk hN⟩) hzero horS hjoin hside births
  obtain ⟨T,hT,hcard⟩ := cover_half n k N r G S H a b A hr hrS hrH hinput ha hb
    horS horH hside handH (fun f R B step => dag_union_bound f R B step)
  exact ⟨T,hT,by omega⟩

theorem pairCleanBound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (x = (fun _ => false) ∨ (∃ u : Fin n, x = fun z => decide (z = u)) ∨ (∃ u v : Fin n, x = fun z => decide (z = u ∨ z = v))) → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1 := by
  intro n G inst hc4 gs out ops eval clean
  have he : ∀ x : Fin n → Bool, (PEqualNP.CircuitLowerBounds.Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x := by
    intro x
    rw [eval]
    exact decide_eq_true_iff
  apply total_from_model n (n+1) (n+1+gs.length) (clampWire (n+gs.length) out) gs.length G
    (supports gs) (fun w u v => posRead gs w (pairBits u v) = true)
    (firstWire n gs) (secondWire n gs) (andPos n gs) hc4 (root_bound n gs.length out)
    (root_support_empty G gs out he) (root_hits G gs out he) (support_base gs) (hit_base gs)
  · intro w lo _
    exact clamp_lt w _ (by omega)
  · intro w lo _
    exact clamp_lt w _ (by omega)
  · exact support_or G gs ops clean
  · intro w u v lo hi ha h
    simpa only [pos_gate G gs ops clean w lo hi,ha,Bool.false_eq_true,ite_false,Bool.or_eq_true]
      using h
  · intro w u v lo hi ha h
    simpa only [pos_gate G gs ops clean w lo hi,ha,ite_true,Bool.and_eq_true] using h
  · exact support_and G gs clean
  · exact cross_support G gs ops clean
  · exact gate_partition_count n gs.length (andPos n gs) (supports gs)


theorem cleanBound : ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], (∀ p q r s : Fin m, p ≠ r → q ≠ s → ¬ (H.Adj p q ∧ H.Adj q r ∧ H.Adj r s ∧ H.Adj s p)) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun m D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ → (∀ k : ℕ, k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ e w : Fin m, ¬ H.Adj e w → PEqualNP.EdgeOwnership.gateVal m D k (PEqualNP.EdgeOwnership.pairInput e w) = false) → ∃ S : Finset (Fin m), (∀ y z : Fin m, H.Adj y z → y ∈ S ∨ z ∈ S) ∧ H.edgeFinset.card + S.card ≤ D.size + 1 := by
  intro m H _ h4 D hM hfun hclean
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine ⟨∅, fun y => y.elim0, ?_⟩
    have he : H.edgeFinset = ∅ :=
      Finset.eq_empty_of_forall_notMem (fun e _ => Sym2.inductionOn e (fun a _ => a.elim0))
    simp [he]
  · have hmono : ∀ g ∈ D.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
      intro g hg
      have := (hM g hg).1
      simpa using this
    refine Clean1892.Clean.pairCleanBound m H h4 D.gates D.output
      (fun g hg => ⟨hmono g hg, (hM g hg).2⟩) (fun x => ?_) (fun i x hx hop hv => ?_)
    · have := congrFun hfun x
      simpa [PEqualNP.MetaComplexity.circuitFun, PEqualNP.MetaComplexity.NestedCover.graphFun]
        using this
    · have hop' : (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op =
          PEqualNP.CircuitLowerBounds.GateOp.and := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        rw [List.getD_eq_getElem _ _ i.2]
        exact hop
      have hval : ∀ e w : Fin m, ¬ H.Adj e w →
          (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨D.gates, 0⟩
            (List.ofFn (PEqualNP.EdgeOwnership.pairInput e w))).getD (m + (i : ℕ)) false = true →
          False := by
        intro e w hew h
        have h2 := hclean i i.2 hop' e w hew
        have h3 : PEqualNP.EdgeOwnership.gateVal m D i (PEqualNP.EdgeOwnership.pairInput e w)
            = true := h
        rw [h2] at h3
        exact Bool.false_ne_true h3
      rcases hx with rfl | ⟨u, rfl⟩ | ⟨u, v, rfl⟩
      · exfalso
        refine hval ⟨0, hm⟩ ⟨0, hm⟩ (H.irrefl) ?_
        refine Clean1892.Clean.wiresFrom_mono D.gates hmono _ _ (by simp) ?_ _ hv
        intro j h
        by_cases hj : j < m
        · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn] at h
          exact absurd h Bool.false_ne_true
        · rw [List.getD_eq_default _ _ (by simp; omega)] at h
          exact absurd h Bool.false_ne_true
      · exfalso
        refine hval u u (H.irrefl) ?_
        have hxe : (fun z : Fin m => decide (z = u)) = PEqualNP.EdgeOwnership.pairInput u u := by
          funext z
          simp [PEqualNP.EdgeOwnership.pairInput]
        rw [← hxe]
        exact hv
      · by_cases hadj : H.Adj u v
        · exact ⟨u, v, hadj, by simp, by simp⟩
        · exact (hval u v hadj hv).elim

end Clean


end Clean1892

namespace Boundary3008_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_le {w v : List Bool} (h : List.Forall₂ (fun a b => a ≤ b) w v) (i : ℕ) :
    w.getD i false ≤ v.getD i false := by
  induction h generalizing i with
  | nil => simp
  | cons hab _ ih =>
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

theorem bool_le {a b : Bool} : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

theorem gate_le (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) {w v : List Bool}
    (h : List.Forall₂ (fun a b => a ≤ b) w v) :
    g.op.eval (g.inputs.map fun i => w.getD i false) ≤
      g.op.eval (g.inputs.map fun i => v.getD i false) := by
  rw [bool_le]
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro hx x hx2
    obtain ⟨i, hi, rfl⟩ := hx2
    exact bool_le.mp (getD_le h i) (hx _ ⟨i, hi, rfl⟩)
  · rw [hg]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨_, ⟨i, hi, rfl⟩, bool_le.mp (getD_le h i) hx⟩

theorem fold_le (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w v : List Bool, List.Forall₂ (fun a b => a ≤ b) w v →
      List.Forall₂ (fun a b => a ≤ b) (gs.foldl step w) (gs.foldl step v) := by
  induction gs with
  | nil => intro w v h; simpa using h
  | cons g gs ih =>
    intro w v h
    simp only [List.foldl_cons]
    apply ih (fun g2 hg2 => hgs g2 (List.mem_cons_of_mem _ hg2))
    exact List.rel_append h (List.Forall₂.cons (gate_le g (hgs g List.mem_cons_self) h) List.Forall₂.nil)

theorem mono (n : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) (o : ℕ) :
    (gs.foldl step (List.ofFn x)).getD o false ≤ (gs.foldl step (List.ofFn y)).getD o false := by
  have h0 : List.Forall₂ (fun a b => a ≤ b) (List.ofFn x) (List.ofFn y) := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp only [List.length_ofFn], fun i h1 h2 => ?_⟩
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    exact bool_le.mpr (hxy _)
  exact getD_le (fold_le gs hgs _ _ h0) o


def nums : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]

def edges : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]

def cols : List ℕ := [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]

def chk (m : ℕ) : Bool :=
  edges.any (fun e => m.testBit e.1 && m.testBit e.2) ||
    (List.range 37).any (fun j => m &&& cols.getD j 0 == m)

theorem chk_all2 : ∀ a < 128, ∀ b < 128, chk (a * 128 + b) = true := by decide +kernel

theorem chk_all : ∀ m < 16384, chk m = true := by
  intro m hm
  have h := chk_all2 (m / 128) (by omega) (m % 128) (by omega)
  rwa [Nat.div_add_mod' m 128] at h

theorem edges_lt : ∀ e ∈ edges, e.1 < 14 ∧ e.2 < 14 := by decide

theorem col_eq : ∀ j < 37, List.ofFn (fun i : Fin 14 => (cols.getD j 0).testBit i.val) =
    nums.map (fun n => n.testBit (21 + j)) ∧ Nat.testBit 2097151 (21 + j) = false := by
  decide +kernel

theorem edge_eq : ∀ u v : Fin 14, (u.val, v.val) ∈ edges → ∃ k : ℕ, k < 21 ∧
    nums.map (fun n => n.testBit k) = List.ofFn (fun i : Fin 14 => decide (i = u ∨ i = v)) ∧
      Nat.testBit 2097151 k = true := by
  decide +kernel

end Boundary3008_aux

open PEqualNP.CircuitLowerBounds Boundary3008_aux in
theorem Boundary3008 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : ℕ), x1.eval (List.map (fun (x4 : ℕ) => x4.testBit x3) [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)]) = Nat.testBit (2097151 : ℕ) x3) → ∀ (x4 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (14 : ℕ)) (x6 : Fin (14 : ℕ)), (↑x5, ↑x6) ∈ [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))] ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true := by
  rintro ⟨gs, out⟩ hC hk x
  have hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa using (hC g hg).1
  have hm : ∀ y z : Fin 14 → Bool, (∀ i, y i = true → z i = true) →
      Circuit.eval ⟨gs, out⟩ (List.ofFn y) = true →
      Circuit.eval ⟨gs, out⟩ (List.ofFn z) = true := by
    intro y z h hy
    exact bool_le.mp (mono 14 gs hgs y z h out) hy
  constructor
  · intro hx
    have hlt : Nat.ofBits x < 16384 := Nat.ofBits_lt_two_pow x
    have hc := chk_all _ hlt
    have hb : ∀ (i : ℕ) (h : i < 14), (Nat.ofBits x).testBit i = x ⟨i, h⟩ :=
      fun i h => Nat.testBit_ofBits_lt x i h
    simp only [chk, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, List.mem_range,
      beq_iff_eq] at hc
    rcases hc with ⟨e, he, h1, h2⟩ | ⟨j, hj, hjm⟩
    · obtain ⟨l1, l2⟩ := edges_lt e he
      refine ⟨⟨e.1, l1⟩, ⟨e.2, l2⟩, he, ?_, ?_⟩
      · rw [← hb e.1 l1]; exact h1
      · rw [← hb e.2 l2]; exact h2
    · exfalso
      obtain ⟨c1, c2⟩ := col_eq j hj
      have h3 := hm x (fun i : Fin 14 => (cols.getD j 0).testBit i.val) (by
        intro i hi
        have h4 : (Nat.ofBits x &&& cols.getD j 0).testBit i.val = true := by
          rw [hjm, hb i.val i.isLt]; exact hi
        rw [Nat.testBit_and] at h4
        simp only [Bool.and_eq_true] at h4
        exact h4.2) hx
      rw [c1] at h3
      have h5 : Circuit.eval ⟨gs, out⟩ (nums.map (fun n => n.testBit (21 + j))) =
          Nat.testBit 2097151 (21 + j) := hk (21 + j)
      rw [h3, c2] at h5
      exact Bool.false_ne_true h5.symm
  · rintro ⟨u, v, huv, hu, hv⟩
    obtain ⟨k, _, e1, e2⟩ := edge_eq u v huv
    have h5 : Circuit.eval ⟨gs, out⟩ (nums.map (fun n => n.testBit k)) =
        Nat.testBit 2097151 k := hk k
    rw [e1, e2] at h5
    refine hm _ x ?_ h5
    intro i hi
    simp only [decide_eq_true_eq] at hi
    rcases hi with rfl | rfl
    · exact hu
    · exact hv

namespace Research2583.Fano
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Point-line coordinates from the public L-meta-1983 labeling. -/
def flags : List (Fin 7 × Fin 7) := [(0,0), (0,1), (0,3), (1,0), (1,2), (1,6), (2,1), (2,5), (2,6), (3,0), (3,4), (3,5), (4,3), (4,4), (4,6), (5,2), (5,3), (5,5), (6,1), (6,2), (6,4)]
def I (p l : Fin 7) : Prop := (p,l) ∈ flags
instance : DecidableRel I := fun p l => inferInstanceAs (Decidable ((p,l) ∈ flags))

theorem plane_axioms :
    (∀ l : Fin 7, (Finset.univ.filter (fun p => I p l)).card = 3) ∧
    (∀ p p' : Fin 7, p ≠ p' → ∃! l : Fin 7, I p l ∧ I p' l) := by
  unfold ExistsUnique
  decide +kernel


end Research2583.Fano

namespace Research2583.Fano
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

def Computes (C : Circuit) : Prop := ∀ x : Fin (7+7) → Bool, circuitFun 14 C x =
  decide (∃ p l : Fin 7, I p l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)

def Nested (C : Circuit) : Prop := ∃ i j, (gateAt C i).op = .and ∧
  (gateAt C j).op = .and ∧ EdgeOwnership.InCone 14 C i j

private theorem mono {C : Circuit} (h : TopForm.IsAO2 14 C) : Monotone2 C := by
  intro g hg
  exact ⟨h.1 g hg, Nat.le_of_eq (h.2.2 g hg)⟩

private def FlagWires (a b : Fin 14) : Prop := ∃ p l : Fin 7, I p l ∧
  a = Fin.castAdd 7 p ∧ b = Fin.natAdd 7 l

instance {a b : Fin 14} : Decidable (FlagWires a b) := by unfold FlagWires; infer_instance

private theorem wire_numbers : ∀ a b : Fin 14,
    (a.val,b.val) ∈ Fano1983.hL ↔ FlagWires a b := by decide +kernel

private theorem flags_eval {C : Circuit} (hC : Computes C) (x : Fin 14 → Bool) :
    C.eval (List.ofFn x) = true ↔ ∃ a b : Fin 14, FlagWires a b ∧ x a = true ∧ x b = true := by
  change circuitFun 14 C x = true ↔ _
  rw [hC,decide_eq_true_eq]
  constructor
  · rintro ⟨p,l,h,ha,hb⟩
    exact ⟨_,_,⟨p,l,h,rfl,rfl⟩,ha,hb⟩
  · rintro ⟨a,b,⟨p,l,h,rfl,rfl⟩,ha,hb⟩
    exact ⟨p,l,h,ha,hb⟩

theorem single_and_layer {C : Circuit} (ao : TopForm.IsAO2 14 C) (hC : Computes C)
    (h : ¬ Nested C) : 27 ≤ C.size := by
  apply Fano1983 C (mono ao) ao.2.1 h
  intro x
  rw [flags_eval hC]
  change _ ↔ ∃ a b : Fin 14, (a.val,b.val) ∈ Fano1983.hL ∧ x a = true ∧ x b = true
  simp only [wire_numbers]


end Research2583.Fano

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK
open scoped BigOperators Sym2

namespace PlaneReadOne

variable {N : ℕ} (I : Fin N → Fin N → Prop)

def adjacent (a b : Fin (N+N)) : Prop :=
  Fin.addCases (fun p => Fin.addCases (fun _ => False) (fun l => I p l) b)
    (fun l => Fin.addCases (fun p => I p l) (fun _ => False) b) a

def graph : SimpleGraph (Fin (N+N)) where
  Adj := adjacent I
  symm := by
    constructor
    intro a b
    induction a using Fin.addCases <;> induction b using Fin.addCases <;> simp only [adjacent,Fin.addCases_left,Fin.addCases_right] <;> tauto
  loopless := by
    constructor
    intro a
    induction a using Fin.addCases <;> simp only [adjacent,Fin.addCases_left,Fin.addCases_right] <;> tauto

noncomputable instance : DecidableRel (graph I).Adj := Classical.decRel _

private theorem cross_ne (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have eq := congrArg Fin.val h
  change p.val = N + l.val at eq
  omega

theorem noFour
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l) : NoFourCycle (graph I) := by
  have line (a b u v : Fin N) (ne : a ≠ b) (hu : I a u ∧ I b u) (hv : I a v ∧ I b v) :
      u = v := (unique a b ne).unique hu hv
  have point (a b u v : Fin N) (ne : u ≠ v) (ha : I a u ∧ I a v) (hb : I b u ∧ I b v) :
      a = b := by
    by_contra ab
    exact ne (line a b u v ab ⟨ha.1,hb.1⟩ ⟨ha.2,hb.2⟩)
  intro a b hab
  apply Finset.card_le_one.mpr
  intro u hu v hv
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hu hv
  induction a using Fin.addCases <;> induction b using Fin.addCases <;>
    induction u using Fin.addCases <;> induction v using Fin.addCases <;>
    simp only [graph,adjacent,Fin.addCases_left,Fin.addCases_right] at hu hv <;>
    obtain ⟨hu₁,hu₂⟩ := hu <;> obtain ⟨hv₁,hv₂⟩ := hv <;> try contradiction
  all_goals
    apply congrArg _
    first
    | exact line _ _ _ _ (fun h => hab (congrArg _ h)) ⟨hu₁,hu₂⟩ ⟨hv₁,hv₂⟩
    | exact point _ _ _ _ (fun h => hab (congrArg _ h)) ⟨hu₁,hu₂⟩ ⟨hv₁,hv₂⟩

theorem graph_eval (z : Fin (N+N) → Bool) :
    (∃ u v, (graph I).Adj u v ∧ z u = true ∧ z v = true) ↔
    ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
  constructor
  · rintro ⟨u,v,adj,hu,hv⟩
    induction u using Fin.addCases <;> induction v using Fin.addCases <;>
      simp only [graph,adjacent,Fin.addCases_left,Fin.addCases_right] at adj <;> exact ⟨_,_,adj,by assumption,by assumption⟩
  · rintro ⟨p,l,hp,hz,hl⟩
    exact ⟨Fin.castAdd N p,Fin.natAdd N l,by simpa only [graph,adjacent,Fin.addCases_left,Fin.addCases_right] using hp,hz,hl⟩

private def encode (e : Fin N × Fin N) : Sym2 (Fin (N+N)) :=
  s(Fin.castAdd N e.1, Fin.natAdd N e.2)

private theorem encode_inj : Function.Injective (@encode N) := by
  rintro ⟨p,l⟩ ⟨p',l'⟩ h
  rcases Sym2.eq_iff.mp h with h | h
  · obtain ⟨hp,hl⟩ := h
    have : p = p' := Fin.castAdd_injective _ _ hp
    have : l = l' := by simpa [Fin.ext_iff] using congrArg Fin.val hl
    congr
  · exact (cross_ne _ _ h.1).elim

theorem edges [DecidableRel I] (q : ℕ)
    (degree : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1) :
    N*(q+1) ≤ (graph I).edgeFinset.card := by
  classical
  let pairs := ((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N))).filter
    fun e => I e.1 e.2
  have count : pairs.card = N*(q+1) := by
    change (((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N))).filter _).card = _
    rw [Plane1955.cardR,Finset.sum_congr rfl (fun l _ => degree l)]
    simp
  have sub : pairs.image encode ⊆ (graph I).edgeFinset := by
    rintro _ h
    obtain ⟨⟨p,l⟩,hp,rfl⟩ := Finset.mem_image.mp h
    apply SimpleGraph.mem_edgeFinset.mpr
    change (graph I).Adj (Fin.castAdd N p) (Fin.natAdd N l)
    simpa only [graph,adjacent,Fin.addCases_left,Fin.addCases_right] using (Finset.mem_filter.mp hp).2
  rw [← count, ← Finset.card_image_of_injective pairs encode_inj]
  exact Finset.card_le_card sub

theorem cover (q : ℕ) [DecidableRel I]
    (lines : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (points : ∀ p, (Finset.univ.filter fun l => I p l).card = q+1)
    (T : Finset (Fin (N+N))) (hits : ∀ u v, (graph I).Adj u v → u ∈ T ∨ v ∈ T) :
    N ≤ T.card := by
  let A := Finset.univ.filter fun p : Fin N => Fin.castAdd N p ∈ T
  let B := Finset.univ.filter fun l : Fin N => Fin.natAdd N l ∈ T
  have lower := Plane1955.cover q I lines points A B (by
    intro p l h
    simpa [A,B] using hits (Fin.castAdd N p) (Fin.natAdd N l) (by simpa only [graph,adjacent,Fin.addCases_left,Fin.addCases_right] using h))
  let pa := A.image (Fin.castAdd N)
  let lb := B.image (Fin.natAdd N)
  have prem : Disjoint pa lb := by
    refine Finset.disjoint_left.mpr ?_
    intro v ha hb
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨l,_,eq⟩ := Finset.mem_image.mp hb
    exact cross_ne p l eq.symm
  have sub : pa ∪ lb ⊆ T := by
    intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp hp).2
    · obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp hl).2
  have natInj : Function.Injective (@Fin.natAdd N N) := by
    intro a b h
    apply Fin.ext
    simpa using congrArg Fin.val h
  have size := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint prem] at size
  change (A.image (Fin.castAdd N)).card + (B.image (Fin.natAdd N)).card ≤ T.card at size
  rw [Finset.card_image_of_injective _ (Fin.castAdd_injective _ _),
    Finset.card_image_of_injective _ natInj] at size
  omega

/-- Supply the edge-cover inequality from a circuit argument, and the exact
    plane count completes the lower bound. -/
theorem ofCoverBound (q : ℕ) [DecidableRel I] (C : Circuit) (hq : 2 ≤ q)
    (order : N = q^2+q+1)
    (lines : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
    (bound : ∃ T : Finset (Fin (N+N)),
      (∀ u v, (graph I).Adj u v → u ∈ T ∨ v ∈ T) ∧
      (graph I).edgeFinset.card + T.card ≤ C.size+1) : N*(q+2) ≤ C.size+1 := by
  obtain ⟨T,hits,lim⟩ := bound
  have points := Plane1955.lines_through q N I hq order lines unique
  have hT := cover I q lines points T hits
  have hE := edges I q lines
  calc
    N*(q+2) = N*(q+1)+N := by ring
    _ ≤ _ := by omega


end PlaneReadOne

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

namespace PlaneReadOne

variable {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]

def Computes (C : Circuit) : Prop :=
  ∀ z : Fin (N+N) → Bool, circuitFun (N+N) C z =
    decide (∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)

omit [DecidableRel I] in
theorem cycleFree
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l) :
    ∀ a b c d, a ≠ c → b ≠ d →
      ¬ ((graph I).Adj a b ∧ (graph I).Adj b c ∧ (graph I).Adj c d ∧ (graph I).Adj d a) := by
  rintro a b c d ac bd ⟨ab,bc,cd,da⟩
  have common := Finset.card_le_one.mp (noFour I unique a c ac)
  apply bd (common b _ d _)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ab,bc.symm⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,da.symm,cd⟩

private theorem output_nonedge (C : Circuit) (eval : Computes I C)
    (u v : Fin (N+N)) (nonedge : ¬(graph I).Adj u v) :
    circuitFun (N+N) C (pairInput u v) = false := by
  rw [eval]
  apply decide_eq_false
  intro h
  obtain ⟨a,b,edge,ha,hb⟩ := (graph_eval I _).mpr h
  simp only [pairInput,decide_eq_true_eq] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (graph I).loopless.irrefl _ edge
  · exact nonedge edge
  · exact nonedge edge.symm
  · exact (graph I).loopless.irrefl _ edge

/-- A clean AND at a rejected two-position input produces false. Repeated
    positions are allowed, so the test includes singleton inputs. -/
def AndsRejectNonedges (C : Circuit) : Prop :=
  ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.and →
    ∀ u v : Fin (N+N), ¬(graph I).Adj u v → gateVal (N+N) C k (pairInput u v) = false

/-- Nested AND gates are permitted. Only their values on graph nonedges are tested. -/
theorem pairClean (q : ℕ) (C : Circuit) (hq : 2 ≤ q) (order : N = q^2+q+1)
    (lines : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
    (ao : IsAO2 (N+N) C) (eval : Computes I C) (clean : AndsRejectNonedges I C) :
    N*(q+2) ≤ C.size+1 := by
  classical
  apply ofCoverBound I q C hq order lines unique
  apply Clean1892.Clean.cleanBound (N+N) (graph I)
    (cycleFree I unique) C _ _ clean
  · intro g hg
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ao.1 g hg,
      (ao.2.2 g hg).le⟩
  · funext z
    rw [eval]
    simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or]
    exact decide_eq_decide.mpr (graph_eval I z).symm

/-- If truth of each AND implies truth of the output on every assignment,
    the circuit meets the star threshold even with nested ANDs. -/
theorem dominated (q : ℕ) (C : Circuit) (hq : 2 ≤ q) (order : N = q^2+q+1)
    (lines : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
    (ao : IsAO2 (N+N) C) (eval : Computes I C)
    (dom : ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.and →
      ∀ z, gateVal (N+N) C k z = true → circuitFun (N+N) C z = true) :
    N*(q+2) ≤ C.size+1 := by
  apply pairClean I q C hq order lines unique ao eval
  intro k hk hop u v nonedge
  cases h : gateVal (N+N) C k (pairInput u v) with
  | false => rfl
  | true =>
    have yes := dom k hk hop _ h
    rw [output_nonedge I C eval u v nonedge] at yes
    contradiction

/-- Any circuit below the threshold has an explicit AND and a rejected input
    supported on at most two positions which the AND accepts. -/
theorem dirtyWitness (q : ℕ) (C : Circuit) (hq : 2 ≤ q) (order : N = q^2+q+1)
    (lines : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
    (ao : IsAO2 (N+N) C) (eval : Computes I C) (small : C.size+1 < N*(q+2)) :
    ∃ k, k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ∃ u v : Fin (N+N), ¬(graph I).Adj u v ∧ gateVal (N+N) C k (pairInput u v) = true ∧
        circuitFun (N+N) C (pairInput u v) = false := by
  by_contra missing
  apply (Nat.not_le.mpr small) (pairClean I q C hq order lines unique ao eval ?_)
  intro k hk hop u v nonedge
  cases h : gateVal (N+N) C k (pairInput u v) with
  | false => rfl
  | true => exact (missing ⟨k,hk,hop,u,v,nonedge,h,output_nonedge I C eval u v nonedge⟩).elim

end PlaneReadOne

namespace Research4387

private def Chain {α : Type} (P : List α → α → Prop) (base xs : List α) :=
  ∀ i : Fin xs.length, P (base ++ xs.take i.val) (xs.get i)

private theorem chainPrefix {α : Type} {P : List α → α → Prop} {base xs tail : List α}
    (h : Chain P base (xs ++ tail)) : Chain P base xs := by
  intro i
  have := h ⟨i.val,by simp; omega⟩
  simpa only [List.get_eq_getElem,List.getElem_append_left i.isLt,
    List.take_append_of_le_length i.isLt.le] using this

private theorem chainLast {α : Type} {P : List α → α → Prop} {base xs : List α} {v : α}
    (h : Chain P base (xs ++ [v])) : P (base ++ xs) v := by
  have := h ⟨xs.length,by simp⟩
  simpa only [List.get_eq_getElem,List.getElem_append_right (Nat.le_refl _),
    Nat.sub_self,List.getElem_cons_zero,List.take_append_length] using this

private theorem chainPush {α : Type} {P : List α → α → Prop} {base xs : List α} {v : α}
    (h : Chain P base xs) (last : P (base ++ xs) v) : Chain P base (xs ++ [v]) := by
  rintro ⟨i,hi⟩
  by_cases before : i < xs.length
  · simpa only [List.get_eq_getElem,List.getElem_append_left before,List.take_append_of_le_length before.le]
      using (h ⟨i,before⟩)
  · have eq : i = xs.length := by simp at hi; omega
    subst i
    simpa only [List.get_eq_getElem,List.getElem_append_right (Nat.le_refl _),
      Nat.sub_self,List.getElem_cons_zero,List.take_append_length] using last

private def Step {w : Nat} (bank : List (BitVec w)) (v : BitVec w) : Prop :=
  ∃ a ∈ bank, ∃ b ∈ bank, v = a &&& b ∨ v = a ||| b

private def Fresh {w : Nat} (bank : List (BitVec w)) (v : BitVec w) : Prop :=
  v ∉ bank ∧ v ≠ 0 ∧ v ≠ BitVec.allOnes w ∧ Step bank v

private theorem eraseConstants {w : Nat} {bank : List (BitVec w)} {v : BitVec w}
    (new : v ∉ 0 :: BitVec.allOnes w :: bank)
    (h : Step (0 :: BitVec.allOnes w :: bank) v) : Fresh bank v := by
  simp only [List.mem_cons,not_or] at new
  refine ⟨new.2.2,new.1,new.2.1,?_⟩
  obtain ⟨a,ha,b,hb,op⟩ := h
  simp only [List.mem_cons] at ha hb
  rcases ha with rfl | rfl | ha <;> rcases hb with rfl | rfl | hb
  all_goals first | exact ⟨a,ha,b,hb,op⟩ | rcases op with rfl | rfl <;> simp_all

/-- Scan in topological order. A value already available costs no additional
gate. Each discarded constant remains available solely in the bookkeeping. -/
private theorem scan {w : Nat} (base xs : List (BitVec w))
    (h : Chain Step (0 :: BitVec.allOnes w :: base) xs) :
    ∃ ys, ys.length ≤ xs.length ∧ Chain Fresh base ys ∧
      ∀ z ∈ (0 :: BitVec.allOnes w :: base) ++ xs,
        z ∈ 0 :: BitVec.allOnes w :: (base ++ ys) := by
  induction xs using List.reverseRecOn with
  | nil => exact ⟨[],by simp,fun i => Fin.elim0 i,by simp⟩
  | append_singleton xs v ih =>
    obtain ⟨ys,budget,valid,cover⟩ := ih (chainPrefix h)
    have op := chainLast h
    have extended : Step (0 :: BitVec.allOnes w :: (base ++ ys)) v := by
      obtain ⟨a,ha,b,hb,eq⟩ := op
      exact ⟨a,cover _ ha,b,cover _ hb,eq⟩
    by_cases old : v ∈ 0 :: BitVec.allOnes w :: (base ++ ys)
    · refine ⟨ys,by simp; omega,valid,?_⟩
      intro z hz
      rw [← List.append_assoc] at hz
      rcases List.mem_append.mp hz with previous | last
      · exact cover _ previous
      · simpa only [List.mem_singleton.mp last] using old
    · refine ⟨ys ++ [v],by simpa using budget,chainPush valid (eraseConstants old extended),?_⟩
      intro z hz
      rw [← List.append_assoc] at hz
      rcases List.mem_append.mp hz with previous | last
      · have p := cover _ previous
        simp only [List.mem_cons,List.mem_append] at p ⊢
        tauto
      · simp [List.mem_singleton.mp last]

/-- An arbitrary-width AND/OR straight-line program for a nonconstant target
can omit constants, repeated masks, and every instruction after the target. -/
theorem normalizeChain {w : Nat} (base xs : List (BitVec w)) (target : BitVec w)
    (valid : ∀ i : Fin xs.length,
      let bank := (0 :: BitVec.allOnes w :: base) ++ xs.take i.val
      ∃ a ∈ bank, ∃ b ∈ bank, xs.get i = a &&& b ∨ xs.get i = a ||| b)
    (hit : target ∈ (0 :: BitVec.allOnes w :: base) ++ xs)
    (nonzero : target ≠ 0) (nonone : target ≠ BitVec.allOnes w) (new : target ∉ base) :
    ∃ ys : List (BitVec w), ys.length ≤ xs.length ∧ ys.getLast? = some target ∧
      ∀ i : Fin ys.length,
        let bank := base ++ ys.take i.val
        ys.get i ∉ bank ∧ ys.get i ≠ 0 ∧ ys.get i ≠ BitVec.allOnes w ∧
          ∃ a ∈ bank, ∃ b ∈ bank, ys.get i = a &&& b ∨ ys.get i = a ||| b := by
  obtain ⟨ys,budget,normal,cover⟩ := scan base xs valid
  have inYs : target ∈ ys := by
    have available := cover target hit
    simp only [List.mem_cons,List.mem_append] at available
    exact ((available.resolve_left nonzero).resolve_left nonone).resolve_left new
  obtain ⟨pre,tail,rfl⟩ := List.append_of_mem inYs
  refine ⟨pre ++ [target],?_,by simp,?_⟩
  · simp at budget ⊢; omega
  · apply chainPrefix (tail:=tail) (P:=Fresh)
    simpa only [List.append_assoc,List.singleton_append] using normal

end Research4387

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity NestedCover PEqualNP.TopForm

namespace Packed4387

abbrev Col := BitVec 58

def row (k : ℕ) (vs : List Col) := vs.map (fun v => v.getLsbD k)

def Step (pool : List Col) (v : Col) : Prop :=
  ∃ a ∈ pool, ∃ b ∈ pool, v = a &&& b ∨ v = a ||| b

def Chain (bank vs : List Col) : Prop :=
  ∀ j : Fin vs.length, Step (bank ++ vs.take j.val) (vs.get j)

def firstGate : Gate := ⟨.or,[0,1]⟩

/-- Column realizations record the complete wire vector at every bit,
    as well as the physical first gate. -/
structure Real (raw pool : List Col) (gs : List Gate) : Prop where
  count : raw.length + gs.length = pool.length
  first : gs.head? = some firstGate
  ao : IsAO2 raw.length ⟨gs,0⟩
  wires : ∀ k : ℕ, (Circuit.mk gs 0).wires (row k raw) = row k pool

private theorem append_ok {n : ℕ} {gs : List Gate} (ok : IsAO2 n ⟨gs,0⟩)
    (g : Gate) (op : g.op = .and ∨ g.op = .or) (len : g.inputs.length = 2)
    (refs : ∀ j ∈ g.inputs, j < n+gs.length) : IsAO2 n ⟨gs++[g],0⟩ := by
  constructor
  · intro h hh
    rcases List.mem_append.mp hh with hh | hh
    · exact ok.1 _ hh
    · have := List.mem_singleton.mp hh; subst h; exact op
  constructor
  · intro j hj a ha
    change j < (gs++[g]).length at hj
    change a ∈ ((gs++[g]).getD j _).inputs at ha
    by_cases old : j < gs.length
    · rw [List.getD_append _ _ _ _ old] at ha
      exact ok.2.1 j old a ha
    · have eq : j = gs.length := by simp at hj; omega
      subst j
      simpa using (refs a (by simpa using ha))
  · intro h hh
    rcases List.mem_append.mp hh with hh | hh
    · exact ok.2.2 _ hh
    · have := List.mem_singleton.mp hh; subst h; exact len

private theorem val_get (k : ℕ) (vs : List Col) (i : Fin vs.length) :
    (row k vs).getD i.val false = (vs.get i).getLsbD k := by
  rw [List.getD_eq_getElem _ _ (by simp [row])]
  simp [row]

private theorem extend {raw pool : List Col} {gs : List Gate} (built : Real raw pool gs)
    {v : Col} (step : Step pool v) : ∃ g, Real raw (pool++[v]) (gs++[g]) := by
  obtain ⟨a,ha,b,hb,which⟩ := step
  obtain ⟨i,ra⟩ := List.mem_iff_get.mp ha
  obtain ⟨j,rb⟩ := List.mem_iff_get.mp hb
  have ci : i.val < raw.length+gs.length := by rw [built.count]; exact i.isLt
  have cj : j.val < raw.length+gs.length := by rw [built.count]; exact j.isLt
  have push (op : GateOp) (binary : op = .and ∨ op = .or)
      (bits : ∀ k, op.eval [a.getLsbD k,b.getLsbD k] = v.getLsbD k) :
      Real raw (pool++[v]) (gs++[⟨op,[i.val,j.val]⟩]) := by
    refine ⟨by simp [built.count,← Nat.add_assoc],?_,?_,?_⟩
    · cases eq : gs with
      | nil => simp [eq] at built; have h := built.first; contradiction
      | cons h t => simpa [eq] using built.first
    · apply append_ok built.ao _ binary rfl
      intro ref href
      simp only [List.mem_cons,List.not_mem_nil,or_false] at href
      rcases href with rfl | rfl <;> assumption
    · intro k
      have app :
          (Circuit.mk (gs++[⟨op,[i.val,j.val]⟩]) 0).wires (row k raw) =
          (Circuit.mk gs 0).wires (row k raw) ++
            [op.eval [((Circuit.mk gs 0).wires (row k raw)).getD i.val false,
              ((Circuit.mk gs 0).wires (row k raw)).getD j.val false]] := by
        simp only [Circuit.wires,List.foldl_append,List.foldl_cons,List.foldl_nil,List.map_cons,List.map_nil]
      rw [app,built.wires k,val_get k pool i,val_get k pool j,ra,rb,bits k]
      simp [row]
  rcases which with rfl | rfl
  · exact ⟨_,push .and (Or.inl rfl) (fun k => by simp [GateOp.eval])⟩
  · exact ⟨_,push .or (Or.inr rfl) (fun k => by simp [GateOp.eval])⟩

/-- Compile a sequence that uses only AND/OR on previously available columns. -/
theorem compile {raw base : List Col} {start : List Gate} (initial : Real raw base start)
    (xs : List Col) (chain : Chain base xs) : ∃ gs, Real raw (base++xs) gs := by
  induction xs using List.reverseRecOn with
  | nil => simpa using Exists.intro start initial
  | append_singleton xs v ih =>
    have prev : Chain base xs := by
      intro j
      have h := chain ⟨j.val, by simp⟩
      simpa only [List.get_eq_getElem,List.getElem_append_left j.isLt,
        List.take_append_of_le_length j.isLt.le] using h
    have step := chain ⟨xs.length,by simp⟩
    simp only [List.get_eq_getElem,List.getElem_append_right (Nat.le_refl _),Nat.sub_self,
      List.getElem_cons_zero,List.take_append_length] at step
    obtain ⟨gs,old⟩ := ih prev
    obtain ⟨g,ext⟩ := extend old step
    exact ⟨_,by simpa only [List.append_assoc] using ext⟩

end Packed4387

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open Research2583

namespace Packed4387

def raw : List Col := [95229015649943559,63038587666488,256462815680,4292497062759936,
  8521481482240,14003410187812864,55389823207997440,189297016294081033,
  155696362464477250,218994303132270608,183565875465490436,229736628138025984,
  270286071508633728,288160007407550752]

def base : List Col := raw ++ [95274182876594239]
def seeds : List Col := 0 :: BitVec.allOnes 58 :: base
def target : Col := 2097151

private theorem initial : Real raw base [firstGate] := by
  refine ⟨rfl,rfl,by decide,?_⟩
  intro k
  have key : (95274182876594239 : Col) = (95229015649943559 : Col) ||| 63038587666488 := by decide
  change row k raw ++ [(95229015649943559 : Col).getLsbD k ||
      ((63038587666488 : Col).getLsbD k || false)] = row k raw ++ [(95274182876594239 : Col).getLsbD k]
  rw [key,BitVec.getLsbD_or,Bool.or_false]

private theorem isPhysical {xs : List Col} (length : xs.length ≤ 25)
    (chain : Chain seeds xs) (hit : target ∈ seeds++xs) :
    ∃ C : Circuit, IsAO2 14 C ∧ C.gates.head? = some firstGate ∧ C.size ≤ 26 ∧
      ∀ k : ℕ, C.eval (row k raw) = target.getLsbD k := by
  obtain ⟨ys,budget,last,normal⟩ := Research4387.normalizeChain base xs target
    chain hit (by decide) (by decide) (by decide)
  obtain ⟨gs,built⟩ := compile initial ys (fun j => (normal j).2.2.2)
  obtain ⟨before,eq⟩ := List.getLast?_eq_some_iff.mp last
  have hmem : target ∈ base++ys := by simp [eq]
  obtain ⟨idx,points⟩ := List.mem_iff_get.mp hmem
  refine ⟨⟨gs,idx.val⟩,built.ao,built.first,?_,?_⟩
  · have h := built.count
    have hr : raw.length = 14 := rfl
    have hb : base.length = 15 := rfl
    rw [hr,List.length_append,hb] at h
    change gs.length ≤ 26
    omega
  · intro k
    change ((Circuit.mk gs 0).wires (row k raw)).getD idx.val false = _
    rw [built.wires k]
    rw [List.getD_eq_getElem _ _ (by simpa [row] using idx.isLt)]
    simp only [row,List.getElem_map]
    exact congrArg (fun c : Col => c.getLsbD k) points

private theorem isComputing {C : Circuit} (ao : IsAO2 14 C)
    (table : ∀ k : ℕ, C.eval (row k raw) = target.getLsbD k) : Fano.Computes C := by
  have mono : Monotone2 C := fun g hg => ⟨ao.1 g hg,(ao.2.2 g hg).le⟩
  have exactC := Boundary3008 C mono table
  have link : ∀ a b : Fin 14, (a.val,b.val) ∈ Boundary3008_aux.edges ↔
      ∃ p l : Fin 7, Fano.I p l ∧ a = Fin.castAdd 7 p ∧ b = Fin.natAdd 7 l := by
    decide +kernel
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  change C.eval (List.ofFn x) = true ↔ _
  rw [exactC x]
  change (∃ a b : Fin 14, (a.val,b.val) ∈ Boundary3008_aux.edges ∧ x a = true ∧ x b = true) ↔ _
  constructor
  · rintro ⟨a,b,edge,xa,xb⟩
    obtain ⟨p,l,inc,rfl,rfl⟩ := (link a b).mp edge
    exact ⟨p,l,inc,xa,xb⟩
  · rintro ⟨p,l,inc,xp,xl⟩
    exact ⟨_,_,(link _ _).mpr ⟨p,l,inc,rfl,rfl⟩,xp,xl⟩

/-- A hypothetical 25-step chain gives a physical toposorted AO2 circuit with
    a prescribed first gate. Two ANDs are nested, and some AND accepts a
    rejected input supported on at most two raw vertices. -/
theorem physicalCounterexample (xs : List Col) (length : xs.length ≤ 25)
    (chain : Chain seeds xs) (hit : target ∈ seeds++xs) :
    ∃ C : Circuit, IsAO2 14 C ∧ C.gates.head? = some firstGate ∧ C.size ≤ 26 ∧
      Fano.Computes C ∧ Fano.Nested C ∧
      ∃ k, k < C.size ∧ (gateAt C k).op = .and ∧
        ∃ u v : Fin 14, gateVal 14 C k (pairInput u v) = true ∧
          C.eval (List.ofFn (pairInput u v)) = false := by
  obtain ⟨C,ao,first,size,table⟩ := isPhysical length chain hit
  have computes := isComputing ao table
  have nested : Fano.Nested C := by
    by_contra h
    have := Fano.single_and_layer ao computes h
    omega
  have dirty := PlaneReadOne.dirtyWitness Fano.I 2 C (by decide) (by decide)
    Fano.plane_axioms.1 Fano.plane_axioms.2 ao computes (by omega)
  obtain ⟨k,hk,op,u,v,_,gate,output⟩ := dirty
  exact ⟨C,ao,first,size,computes,nested,k,hk,op,u,v,gate,output⟩

end Packed4387

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open Research2583

namespace Packed4387

theorem checkedPhysical :
  let base := List.map (BitVec.ofNat 58) ([95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752, 95274182876594239] : List Nat)
  ∀ xs : List (BitVec 58), xs.length ≤ 25 →
    (∀ j : Fin xs.length, let w := base ++ xs.take j.val
      ∃ a ∈ w, ∃ b ∈ w, xs.get j = a &&& b ∨ xs.get j = a ||| b) →
    (2097151 : BitVec 58) ∈ xs →
    ∃ C : Circuit, IsAO2 14 C ∧ C.gates.head? = some (⟨.or,[0,1]⟩ : Gate) ∧ C.size ≤ 26 ∧
    (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) =
      decide (∃ p l : Fin 7, (p.val+l.val)%7 ∈ ([0,1,3] : List Nat) ∧
        x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) ∧
    (∃ i j, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 14 C i j) ∧
    (∃ k, k < C.size ∧ (gateAt C k).op = .and ∧ ∃ u v : Fin 14,
      gateVal 14 C k (pairInput u v) = true ∧ C.eval (List.ofFn (pairInput u v)) = false) := by
  intro start xs budget chain hit
  have start_eq : start = base := rfl
  rw [start_eq] at chain
  have old : Chain seeds xs := by
    intro j
    obtain ⟨a,ha,b,hb,h⟩ := chain j
    exact ⟨a,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha),
      b,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hb),h⟩
  obtain ⟨C,ao,first,size,func,nested,dirty⟩ := physicalCounterexample xs budget old (List.mem_append_right _ hit)
  refine ⟨C,ao,first,size,?_,nested,dirty⟩
  have table : ∀ p l : Fin 7, Fano.I p l ↔ (p.val+l.val)%7 ∈ ([0,1,3] : List Nat) := by
    decide +kernel
  intro x
  change circuitFun 14 C x = _
  rw [func]
  apply decide_eq_decide.mpr
  simp only [table]


end Packed4387

end PEqualNP.Outside.L_meta_physical

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.L_meta_physical : let base := List.map (BitVec.ofNat 58) ([95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752, 95274182876594239] : List Nat)
  ∀ xs : List (BitVec 58), xs.length ≤ 25 →
    (∀ j : Fin xs.length, let w := base ++ xs.take j.val
      ∃ a ∈ w, ∃ b ∈ w, xs.get j = a &&& b ∨ xs.get j = a ||| b) →
    (2097151 : BitVec 58) ∈ xs →
    ∃ C : Circuit, IsAO2 14 C ∧ C.gates.head? = some (⟨.or,[0,1]⟩ : Gate) ∧ C.size ≤ 26 ∧
    (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) =
      decide (∃ p l : Fin 7, (p.val+l.val)%7 ∈ ([0,1,3] : List Nat) ∧
        x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) ∧
    (∃ i j, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 14 C i j) ∧
    (∃ k, k < C.size ∧ (gateAt C k).op = .and ∧ ∃ u v : Fin 14,
      gateVal 14 C k (pairInput u v) = true ∧ C.eval (List.ofFn (pairInput u v)) = false) :=
  PEqualNP.Outside.L_meta_physical.Packed4387.checkedPhysical
