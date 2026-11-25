import PEqualNP.Defs

namespace VertexPeel.ZeroFold

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK PEqualNP.ReadTwo PEqualNP.Core

/- Wire lemmas and the semantic merging predicate are from upstream L-meta-2797. -/
-- One pass over the gates, each gate appending one value.
def run {α : Type} (step : List α → Gate → α) (R : List α) (gs : List Gate) : List α :=
  gs.foldl (fun R g => R ++ [step R g]) R

lemma run_length {α : Type} (step : List α → Gate → α) (R : List α) (gs : List Gate) :
    (run step R gs).length = R.length + gs.length := by
  induction gs generalizing R with
  | nil => simp [run]
  | cons g gs ih =>
    have := ih (R ++ [step R g])
    simp only [run, List.foldl_cons, List.length_cons] at this ⊢
    rw [this]
    simp
    omega

lemma run_old {α : Type} (step : List α → Gate → α) (R : List α) (gs : List Gate) (d : α) (i : ℕ)
    (hi : i < R.length) : (run step R gs).getD i d = R.getD i d := by
  induction gs generalizing R with
  | nil => rfl
  | cons g gs ih =>
    have := ih (R ++ [step R g]) (by simp; omega)
    simp only [run, List.foldl_cons] at this ⊢
    rw [this, List.getD_append _ _ _ _ hi]

lemma run_new {α : Type} (step : List α → Gate → α) (R : List α) (gs : List Gate) (d : α) (j : ℕ)
    (hj : j < gs.length) :
    ∃ P : List α, (run step R gs).getD (R.length + j) d = step P gs[j] ∧
      ∀ i < R.length + j, P.getD i d = (run step R gs).getD i d := by
  induction gs generalizing R j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      refine ⟨R, ?_, fun i hi => (run_old step R _ d i (by omega)).symm⟩
      have := run_old step (R ++ [step R g]) gs d R.length (by simp)
      simp only [run, List.foldl_cons, Nat.add_zero] at this ⊢
      rw [this, List.getD_append_right _ _ _ _ (le_refl _)]
      simp
    | succ j =>
      obtain ⟨P, h1, h2⟩ := ih (R ++ [step R g]) j (by simpa using hj)
      have hlen : (R ++ [step R g]).length + j = R.length + (j + 1) := by simp; omega
      rw [hlen] at h1 h2
      exact ⟨P, h1, h2⟩

def sB (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

lemma two (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b, C.gates[j].inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧
      (C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or) := by
  have h2 := hC.2.2 C.gates[j] (List.getElem_mem hj)
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp h2
  have hr := hC.2.1 j hj
  have hg : gateAt C j = C.gates[j] := by
    unfold gateAt; rw [List.getD_eq_getElem _ _ hj]
  rw [hg, hab] at hr
  exact ⟨a, b, hab, hr a (by simp), hr b (by simp), hC.1 _ (List.getElem_mem hj)⟩

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  unfold gateAt; rw [List.getD_eq_getElem _ _ hj]

lemma wval_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j a b : ℕ) (hj : j < C.gates.length)
    (hab : C.gates[j].inputs = [a, b]) (ha : a < n + j) (hb : b < n + j) :
    wval C x (n + j) = C.gates[j].op.eval [wval C x a, wval C x b] := by
  obtain ⟨P, h1, h2⟩ := run_new sB (List.ofFn x) C.gates false j hj
  rw [List.length_ofFn] at h1 h2
  change (run sB (List.ofFn x) C.gates).getD (n + j) false = _
  rw [h1]
  unfold sB
  rw [hab]
  simp only [List.map_cons, List.map_nil]
  rw [h2 a ha, h2 b hb]
  rfl

lemma wval_and {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j a b : ℕ) (hj : j < C.gates.length)
    (hab : C.gates[j].inputs = [a, b]) (ha : a < n + j) (hb : b < n + j)
    (ho : C.gates[j].op = GateOp.and) : wval C x (n + j) = (wval C x a && wval C x b) := by
  rw [wval_gate C x j a b hj hab ha hb, ho]
  simp [GateOp.eval]

lemma wval_or {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j a b : ℕ) (hj : j < C.gates.length)
    (hab : C.gates[j].inputs = [a, b]) (ha : a < n + j) (hb : b < n + j)
    (ho : C.gates[j].op = GateOp.or) : wval C x (n + j) = (wval C x a || wval C x b) := by
  rw [wval_gate C x j a b hj hab ha hb, ho]
  simp [GateOp.eval]

lemma wval_in {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) : wval C x i = x i := by
  change (run sB (List.ofFn x) C.gates).getD i false = _
  rw [run_old _ _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

lemma wval_past {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    wval C x w = false := by
  change (run sB (List.ofFn x) C.gates).getD w false = _
  rw [List.getD_eq_default]
  rw [run_length]; simpa using hw

variable {n : ℕ}

def zr (Z : Finset (Fin n)) (x : Fin n → Bool) : Fin n → Bool := fun i => if i ∈ Z then false else x i

def fv (C : Circuit) (Z : Finset (Fin n)) (w : ℕ) (x : Fin n → Bool) : Bool := wval C (zr Z x) w

def Mg (C : Circuit) (Z : Finset (Fin n)) (j : ℕ) : Prop :=
  j < C.gates.length ∧ (∀ a < n + j, fv C Z (n + j) ≠ fv C Z a) ∧ fv C Z (n + j) ≠ fun _ => false

lemma fv_in (C : Circuit) (Z : Finset (Fin n)) (i : Fin n) (hi : i ∉ Z) : fv C Z i = fun x => x i := by
  funext x
  unfold fv
  rw [wval_in]
  unfold zr
  rw [ite_eq_right hi]

lemma fv_in0 (C : Circuit) (Z : Finset (Fin n)) (i : Fin n) (hi : i ∈ Z) : fv C Z i = fun _ => false := by
  funext x
  unfold fv
  rw [wval_in]
  unfold zr
  rw [ite_eq_left hi]

lemma fv_past (C : Circuit) (Z : Finset (Fin n)) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    fv C Z w = fun _ => false := by
  funext x
  exact wval_past C _ w hw

lemma fv_and (C : Circuit) (Z : Finset (Fin n)) (j a b : ℕ) (hj : j < C.gates.length)
    (hab : C.gates[j].inputs = [a, b]) (ha : a < n + j) (hb : b < n + j)
    (ho : C.gates[j].op = GateOp.and) (x : Fin n → Bool) :
    fv C Z (n + j) x = (fv C Z a x && fv C Z b x) := wval_and C _ j a b hj hab ha hb ho

lemma fv_or (C : Circuit) (Z : Finset (Fin n)) (j a b : ℕ) (hj : j < C.gates.length)
    (hab : C.gates[j].inputs = [a, b]) (ha : a < n + j) (hb : b < n + j)
    (ho : C.gates[j].op = GateOp.or) (x : Fin n → Bool) :
    fv C Z (n + j) x = (fv C Z a x || fv C Z b x) := wval_or C _ j a b hj hab ha hb ho

-- a gate with a false operand is not merging
lemma kill (C : Circuit) (hC : IsAO2 n C) (Z : Finset (Fin n)) (j : ℕ) (hj : j < C.gates.length) (c : ℕ)
    (hc : c ∈ C.gates[j].inputs) (h0 : fv C Z c = fun _ => false) : ¬ Mg C Z j := by
  rintro ⟨_, h1, h2⟩
  obtain ⟨a, b, hab, ha, hb, hop⟩ := two n C hC j hj
  rw [hab] at hc
  have hc : c = a ∨ c = b := by simpa using hc
  rcases hop with ho | ho
  · refine h2 (funext fun x => ?_)
    rw [fv_and C Z j a b hj hab ha hb ho]
    rcases hc with rfl | rfl
    · rw [h0]; rfl
    · rw [h0, Bool.and_false]
  · rcases hc with rfl | rfl
    · refine h1 b hb (funext fun x => ?_)
      rw [fv_or C Z j c b hj hab ha hb ho, h0]; rfl
    · refine h1 a ha (funext fun x => ?_)
      rw [fv_or C Z j a c hj hab ha hb ho, h0, Bool.or_false]


def Rep (gs : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  f = (fun _ => false) ∨ ∃ w < n + gs.length, f = fun x => wval (⟨gs,0⟩ : Circuit) x w

private theorem old_val (gs : List Gate) (g : Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : w < n + gs.length) :
    wval (⟨gs ++ [g],0⟩ : Circuit) x w = wval (⟨gs,0⟩ : Circuit) x w := by
  change ((gs ++ [g]).foldl (fun R h => R ++ [sB R h]) (List.ofFn x)).getD w false = _
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  apply List.getD_append
  change w < (run sB (List.ofFn x) gs).length
  simpa [run_length] using hw

private theorem Rep.snoc {gs : List Gate} {f : (Fin n → Bool) → Bool} (r : Rep gs f) (g : Gate) :
    Rep (gs ++ [g]) f := by
  rcases r with r | ⟨w,hw,r⟩
  · exact Or.inl r
  · exact Or.inr ⟨w,by simp; omega, r.trans (funext fun x => (old_val gs g x w hw).symm)⟩

private theorem appendAO {gs : List Gate} (old : IsAO2 n ⟨gs,0⟩) (a b : ℕ)
    (ha : a < n+gs.length) (hb : b < n+gs.length) (op : GateOp) (ho : op = .and ∨ op = .or) :
    IsAO2 n ⟨gs ++ [⟨op,[a,b]⟩],0⟩ := by
  let g : Gate := ⟨op,[a,b]⟩
  change IsAO2 n ⟨gs ++ [g],0⟩
  refine ⟨?_,?_,?_⟩
  · intro q hq
    rcases List.mem_append.mp hq with e | e
    · exact old.1 _ e
    · simpa using (List.mem_singleton.mp e ▸ ho : q.op = .and ∨ q.op = .or)
  · intro j hj i hi
    change i ∈ ((gs ++ [g]).getD j _).inputs at hi
    by_cases e : j < gs.length
    · rw [List.getD_append _ _ _ _ e] at hi
      exact old.2.1 j e i hi
    · have hlen : j < (gs ++ [g]).length := hj
      have ej : j = gs.length := by simp at hlen; omega
      subst j
      rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
      have hit : i = a ∨ i = b := by simpa [g] using hi
      rcases hit with rfl | rfl <;> assumption
  · intro q hq
    rcases List.mem_append.mp hq with e | e
    · exact old.2.2 _ e
    · rw [List.mem_singleton.mp e]; rfl

open Classical in
theorem compile_prefix (C : Circuit) (hC : IsAO2 n C) (Z : Finset (Fin n)) (k : ℕ)
    (hk : k ≤ C.size) :
    ∃ gs : List Gate, IsAO2 n ⟨gs,0⟩ ∧ gs.length ≤ ((Finset.range k).filter (Mg C Z)).card ∧
      ∀ w < n+k, Rep gs (fv C Z w) := by
  classical
  induction k with
  | zero =>
    have empty : IsAO2 n ⟨[],0⟩ := by
      refine ⟨?_,?_,?_⟩
      · intro g hg
        exact (List.not_mem_nil hg).elim
      · intro j hj
        exact (Nat.not_lt_zero _ hj).elim
      · intro g hg
        exact (List.not_mem_nil hg).elim
    refine ⟨[],empty,by simp,?_⟩
    intro w hw
    let i : Fin n := ⟨w,by omega⟩
    by_cases e : i ∈ Z
    · exact Or.inl (fv_in0 C Z i e)
    · refine Or.inr ⟨w,by simp; omega,(fv_in C Z i e).trans ?_⟩
      exact funext fun x => (wval_in (⟨[],0⟩ : Circuit) x i).symm
  | succ k ih =>
    obtain ⟨gs,hgs,hs,rep⟩ := ih (by omega)
    have hk' : k < C.gates.length := by exact Nat.lt_of_succ_le hk
    by_cases hm : Mg C Z k
    · obtain ⟨a,b,hab,ha,hb,ho⟩ := two n C hC k hk'
      have dep (w : ℕ) (hit : w ∈ C.gates[k].inputs) : fv C Z w ≠ fun _ => false :=
        fun e => (kill C hC Z k hk' w hit e) hm
      obtain ⟨u,hu,eu⟩ := (rep a ha).resolve_left (dep a (by simp [hab]))
      obtain ⟨v,hv,ev⟩ := (rep b hb).resolve_left (dep b (by simp [hab]))
      let g : Gate := ⟨C.gates[k].op,[u,v]⟩
      refine ⟨gs ++ [g],appendAO hgs u v hu hv _ ho,?_,?_⟩
      · simpa [Finset.range_add_one, Finset.filter_insert, hm] using hs
      · intro w hw
        by_cases e : w < n+k
        · exact (rep w e).snoc g
        · have we : w = n+k := by omega
          subst w
          refine Or.inr ⟨n+gs.length,by simp,funext fun x => ?_⟩
          change wval C (zr Z x) (n+k) = _
          rw [wval_gate C (zr Z x) k a b hk' hab ha hb]
          have newGate := wval_gate (n := n) (⟨gs++[g],0⟩ : Circuit) x gs.length u v
            (by simp) (by simp [g]) hu hv
          rw [newGate]
          simp only [List.getElem_append_right (by omega : gs.length ≤ gs.length), Nat.sub_self,
            List.getElem_cons_zero]
          change C.gates[k].op.eval [fv C Z a x,fv C Z b x] = C.gates[k].op.eval [_,_]
          rw [eu,ev,old_val gs g x u hu,old_val gs g x v hv]
    · refine ⟨gs,hgs,?_,?_⟩
      · simpa [Finset.range_add_one,Finset.filter_insert,hm] using hs
      · intro w hw
        by_cases e : w < n+k
        · exact rep w e
        · have we : w = n+k := by omega
          subst w
          by_cases z : fv C Z (n+k) = fun _ => false
          · exact Or.inl z
          · have dup : ∃ a < n+k, fv C Z (n+k) = fv C Z a := by
              by_contra! bad
              exact hm ⟨hk',bad,z⟩
            obtain ⟨a,ha,ea⟩ := dup
            rw [ea]
            exact rep _ ha

open Classical in
theorem compile (C : Circuit) (hC : IsAO2 n C) (Z : Finset (Fin n)) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = fv C Z C.output ∧
      D.size ≤ ((Finset.range C.size).filter (Mg C Z)).card := by
  classical
  obtain ⟨gs,hg,hlen,r⟩ := compile_prefix C hC Z C.size le_rfl
  have rep : Rep gs (fv C Z C.output) := by
    by_cases e : C.output < n+C.size
    · exact r _ e
    · exact Or.inl (fv_past C Z _ (Nat.le_of_not_gt e))
  rcases rep with z | ⟨w,hw,ew⟩
  · refine ⟨⟨gs,n+gs.length⟩,hg,?_,hlen⟩
    rw [z]
    exact funext fun x => wval_past (⟨gs,n+gs.length⟩ : Circuit) x _ (le_refl _)
  · exact ⟨⟨gs,w⟩,hg,ew.symm,hlen⟩

end VertexPeel.ZeroFold
