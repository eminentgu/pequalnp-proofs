import PEqualNP.Outside.L_meta_1737

namespace Research.LeafCharge

open PEqualNP.Outside.L_meta_1737 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def isAnd : GateOp → Bool | .and => true | _ => false
def ands (gs : List Gate) := (gs.filter fun g => isAnd g.op).length
def Mono (g : Gate) : Prop := (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

@[simp] theorem ands_append (xs ys : List Gate) : ands (xs ++ ys) = ands xs + ands ys := by
  simp [ands]

private theorem emitted (op : GateOp) (m : ℕ) (ins : List Stat)
    (ho : op = .and ∨ op = .or) :
    ∀ g ∈ (simplify op m ins).1.toList, g.op = op ∧ Mono g := by
  rcases ho with rfl | rfl <;>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    (try cases a) <;> (try cases b) <;> simp [simplify,simpAnd,simpOr,Mono]

private theorem or_true (m : ℕ) (ins : List Stat) (hl : ins.length ≤ 2)
    (hit : Sum.inl true ∈ ins) : (simplify .or m ins).2 = Sum.inl true := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
    simp_all [simplify,simpOr]

private theorem local_bound (n : ℕ) (acc : List Stat × List Gate) (g : Gate)
    (hg : Mono g) : ands (elimStep n acc g).2 ≤ ands acc.2 + ands [g] := by
  let ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false)
  let e := (simplify g.op (n+acc.2.length) ins).1
  change ands (acc.2 ++ e.toList) ≤ _
  rw [ands_append]
  cases he : e with
  | none => simp [ands]
  | some q =>
    have hq := emitted g.op (n+acc.2.length) ins hg.1 q (by change q ∈ e.toList; simp [he])
    cases hv : isAnd g.op <;> simp [ands,hq.1,hv]

private theorem count_bound (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (ok : ∀ g ∈ gs, Mono g) : ands (elim n gs acc).2 ≤ ands acc.2 + ands gs := by
  induction gs generalizing acc with
  | nil => simp [elim,ands]
  | cons g gs ih =>
    have a := local_bound n acc g (ok g (by simp))
    have b := ih (elimStep n acc g) (fun q h => ok q (by simp [h]))
    change ands (elim n gs (elimStep n acc g)).2 ≤ _
    rw [show g :: gs = [g] ++ gs from rfl, ands_append]
    omega

private theorem remainsMono (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (ok : ∀ g ∈ gs, Mono g) (old : ∀ g ∈ acc.2, Mono g) : ∀ g ∈ (elim n gs acc).2, Mono g := by
  induction gs generalizing acc with
  | nil => exact old
  | cons g gs ih =>
    apply ih _ (fun q h => ok q (by simp [h]))
    intro q hq
    rcases List.mem_append.mp hq with h|h
    · exact old q h
    · exact (emitted _ _ _ (ok g (by simp)).1 q h).2

private def Tracks (a b : List Bool) (s : List Stat) : Prop :=
  ∀ i, a.getD i false ≠ b.getD i false → s.getD i (Sum.inl false) = Sum.inl true

private def push (a : List Bool) (g : Gate) :=
  a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]

private theorem trackStep (n : ℕ) (g : Gate) (acc : List Stat × List Gate) (a b : List Bool)
    (ha : a.length = acc.1.length) (hb : b.length = acc.1.length)
    (ok : Mono g) (track : Tracks a b acc.1)
    (eqc : ands (elimStep n acc g).2 = ands acc.2 + ands [g]) :
    Tracks (push a g) (push b g) (elimStep n acc g).1 := by
  intro i diff
  by_cases hi : i = acc.1.length
  · subst i
    unfold push at diff
    rw [← ha, getD_snoc_eq, ha, ← hb, getD_snoc_eq] at diff
    obtain ⟨j, hj, hneq⟩ : ∃ j ∈ g.inputs, a.getD j false ≠ b.getD j false := by
      by_contra! h
      exact diff (congrArg g.op.eval (List.map_congr_left h))
    let ins := g.inputs.map fun j => acc.1.getD j (Sum.inl false)
    have hit : Sum.inl true ∈ ins := List.mem_map.mpr ⟨j,hj,track j hneq⟩
    change (acc.1 ++ [_]).getD acc.1.length _ = _
    rw [getD_snoc_eq]
    rcases ok.1 with op|op
    · have he := simplify_count g.op (n+acc.2.length) ins (Or.inl op)
          (by simpa [ins] using ok.2) (by simp [op]) ⟨true,hit⟩
      change ands (acc.2 ++ (simplify g.op _ ins).1.toList) = _ at eqc
      rw [he] at eqc
      simp [ands,op,isAnd] at eqc
    · change (simplify g.op _ ins).2 = _
      rw [op]
      exact or_true _ _ (by simpa [ins] using ok.2) hit
  · unfold push at diff
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)] at diff
    change (acc.1 ++ [_]).getD i _ = _
    rw [getD_snoc_ne _ _ _ _ hi]
    exact track i diff

private theorem trackAll (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (a b : List Bool)
    (ha : a.length = acc.1.length) (hb : b.length = acc.1.length)
    (ok : ∀ g ∈ gs, Mono g) (track : Tracks a b acc.1)
    (eqc : ands (elim n gs acc).2 = ands acc.2 + ands gs) :
    Tracks (wiresFrom gs a) (wiresFrom gs b) (elim n gs acc).1 := by
  induction gs generalizing acc a b with
  | nil => exact track
  | cons g gs ih =>
    have okg := ok g (by simp)
    have rest : ∀ q ∈ gs, Mono q := fun q h => ok q (by simp [h])
    have s := local_bound n acc g okg
    have t := count_bound n gs (elimStep n acc g) rest
    change ands (elim n gs (elimStep n acc g)).2 = _ at eqc
    rw [show g :: gs = [g] ++ gs from rfl, ands_append] at eqc
    apply ih (elimStep n acc g) (push a g) (push b g) (by simp [push,elimStep,ha])
      (by simp [push,elimStep,hb]) rest (trackStep n g acc a b ha hb okg track (by omega)) (by omega)

private def labels {n : ℕ} (v p i : Fin n) : Stat :=
  if i = v then Sum.inl true else if i = p then Sum.inl false else Sum.inr i.val

def pin {n : ℕ} (v p : Fin n) (x : Fin n → Bool) (i : Fin n) : Bool :=
  if i = v then true else if i = p then false else x i

private theorem getIn {α : Type} {n : ℕ} (f : Fin n → α) (i : ℕ) (hi : i<n) (d : α) :
    (List.ofFn f).getD i d = f ⟨i,hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_ofFn]

private theorem initInv {n : ℕ} (v p : Fin n) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (List.ofFn (pin v p x)) (List.ofFn (labels v p),[]) := by
  constructor
  · simp
  · intro i
    by_cases hi : i<n
    · simp only [getIn _ _ hi, wiresFrom, List.foldl_nil, List.length_nil, Nat.add_zero]
      unfold labels pin
      split_ifs <;> simp [Stat.Valid,Stat.val,hi]
    · simp [hi,Stat.Valid,Stat.val]

private theorem tracksStart {n : ℕ} (v p : Fin n) (a b : Fin n → Bool)
    (d : ∀ i, a i ≠ b i → i = v) :
    Tracks (List.ofFn a) (List.ofFn b) (List.ofFn (labels v p)) := by
  intro i h
  by_cases hi : i<n
  · rw [getIn _ _ hi, getIn _ _ hi] at h
    rw [getIn _ _ hi]; simp [labels,d _ h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)] at h
    exact (h rfl).elim

/-- A sensitive input fixed high consumes an AND if the restricted output can be false.
A second input may be fixed low at the same time. -/
theorem restrictAnd {n : ℕ} (C : Circuit) (v p : Fin n) (hm : Monotone2 C)
    (a b : Fin n → Bool) (hd : ∀ i, a i ≠ b i → i = v)
    (diff : C.eval (List.ofFn a) ≠ C.eval (List.ofFn b))
    (zero : ∃ x, C.eval (List.ofFn (pin v p x)) = false) :
    ∃ D : Circuit, Monotone2 D ∧ ands D.gates < ands C.gates ∧
      ∀ x, D.eval (List.ofFn x) = C.eval (List.ofFn (pin v p x)) := by
  let start : List Stat × List Gate := (List.ofFn (labels v p),[])
  let finish := elim n C.gates start
  have ok : ∀ g ∈ C.gates, Mono g := hm
  have mono := remainsMono n C.gates start ok (by simp [start])
  have inv (x : Fin n → Bool) := inv_elim n (List.ofFn x) (by simp) C.gates _ _
    (fun g hg => ⟨(ok g hg).1.imp_right Or.inl,(ok g hg).2⟩) (initInv v p x)
  let out := finish.1.getD C.output (Sum.inl false)
  have val (x : Fin n → Bool) : out.val (wiresFrom finish.2 (List.ofFn x)) =
      C.eval (List.ofFn (pin v p x)) := ((inv x).2 C.output).2
  obtain ⟨z,hz⟩ := zero
  have cold : out ≠ Sum.inl true := by
    intro e
    have := val z
    rw [e,hz] at this
    exact Bool.noConfusion this
  have less : ands finish.2 < ands C.gates := by
    have le := count_bound n C.gates start ok
    have h0 : ands start.2 = 0 := rfl
    change ands finish.2 ≤ _ at le
    rw [h0, Nat.zero_add] at le
    apply lt_of_le_of_ne le
    intro he
    apply cold
    apply trackAll n C.gates start (List.ofFn a) (List.ofFn b) (by simp [start])
      (by simp [start]) ok (tracksStart v p a b hd) (by rw [h0,Nat.zero_add]; exact he) C.output diff
  cases e : out with
  | inr j =>
    exact ⟨⟨finish.2,j⟩,mono,less,fun x => by change (wiresFrom finish.2 _).getD j false = _; simpa only [e,Stat.val] using val x⟩
  | inl c =>
    have off : c = false := by cases c <;> simp_all
    subst c
    refine ⟨⟨[],n⟩,by simp [Monotone2],by change 0 < _; omega,?_⟩
    intro x
    have := val x
    rw [e] at this
    change (List.ofFn x).getD n false = _
    rw [List.getD_eq_default _ _ (by simp)]
    exact this

end Research.LeafCharge
