import PEqualNP.Outside.L_meta_2904

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2904

namespace Triple2836.Pinning

def charged (g : Gate) : Bool :=
  match g.op with
  | .not => false
  | _ => true

def cost (gs : List Gate) : ℕ := gs.countP charged

private def weight (g : Gate) : ℕ := if charged g then 1 else 0

private theorem cost_append (gs hs : List Gate) : cost (gs ++ hs) = cost gs + cost hs := by
  simp [cost]

private theorem cost_cons (g : Gate) (gs : List Gate) : cost (g :: gs) = weight g + cost gs := by
  cases e : charged g <;> simp [weight, cost, e, Nat.add_comm]

private def statPins (acc : List Stat × List Gate) (g : Gate) : List Stat :=
  g.inputs.map fun i => acc.1.getD i (.const false)

private def result (n : ℕ) (acc : List Stat × List Gate) (g : Gate) :=
  simplify g.op (n + acc.2.length) (statPins acc g)

private def evaluate (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private theorem option_le_one (o : Option Gate) : cost o.toList ≤ 1 := by
  cases o with
  | none => decide
  | some g => cases e : charged g <;> simp [cost, e]

private theorem not_cost (m : ℕ) (ins : List Stat) :
    cost (simpNot m ins).1.toList = 0 := by
  cases ins with
  | nil => rfl
  | cons s rest => cases s <;> rfl

private theorem step_bound (n : ℕ) (a : List Stat × List Gate) (g : Gate) :
    cost (result n a g).1.toList ≤ weight g := by
  obtain ⟨op,pins⟩ := g
  cases op <;> try exact option_le_one _
  exact le_of_eq (not_cost _ _)

private theorem step_cost (n : ℕ) (a : List Stat × List Gate) (g : Gate) :
    cost (elimStep n a g).2 = cost a.2 + cost (result n a g).1.toList := cost_append _ _

/-- If a raw or intermediate value changes between the two witness rows,
    the specialized state has already replaced that wire by a constant. -/
def Tracked (l r : List Bool) (stats : List Stat) : Prop :=
  stats.length = l.length ∧ stats.length = r.length ∧
    ∀ i, l.getD i false = r.getD i false ∨ ∃ b, stats.getD i (.const false) = .const b

private theorem one_value (n : ℕ) (a : List Stat × List Gate) (g : Gate) (l r : List Bool)
    (hg : Ok g) (track : Tracked l r a.1)
    (kept : cost (result n a g).1.toList = weight g) :
    evaluate g l = evaluate g r ∨ ∃ b, (result n a g).2 = .const b := by
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
      · left; simpa [evaluate,GateOp.eval] using congrArg Bool.not h
      · right
        refine ⟨!b,?_⟩
        change (simpNot _ (a.1.getD i (.const false) :: _)).2 = _
        rw [h]
        rfl
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

private theorem track_snoc (l r : List Bool) (stats : List Stat) (x y : Bool) (z : Stat)
    (h : Tracked l r stats) (v : x = y ∨ ∃ b, z = .const b) :
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

theorem elim_cost (n : ℕ) (gs : List Gate) (a : List Stat × List Gate) :
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

theorem track_if_no_saving (n : ℕ) (gs : List Gate) (a : List Stat × List Gate) (l r : List Bool)
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

/-- If the original output separates two tracked rows and the specialized output
    is represented by a wire, specialization saves at least one non-NOT gate. -/
theorem pin_saves_charged (n : ℕ) (gs : List Gate) (a : List Stat × List Gate) (l r : List Bool)
    (o newOutput : ℕ) (ok : ∀ g ∈ gs, Ok g) (tracked : Tracked l r a.1)
    (diff : (wiresFrom gs l).getD o false ≠ (wiresFrom gs r).getD o false)
    (wire : (elim n gs a).1.getD o (.const false) = .wire newOutput) :
    cost (elim n gs a).2 + 1 ≤ cost a.2 + cost gs := by
  have bound := elim_cost n gs a
  by_contra! bad
  have eqCost : cost (elim n gs a).2 = cost a.2 + cost gs := by omega
  have final := track_if_no_saving n gs a l r ok tracked eqCost
  obtain ⟨b,impossible⟩ := (final.2.2 o).resolve_left diff
  rw [wire] at impossible
  contradiction

/-- Source indices in a wiring diagram can name input pins of the new circuit
    or Boolean constants. Mapping the new row through it gives the old row. -/
def assigned (labels : List Stat) (x : List Bool) : List Bool :=
  labels.map (Stat.val x)

theorem assigned_inv (n : ℕ) (labels : List Stat) (x : List Bool) (_xn : x.length = n)
    (valid : ∀ s ∈ labels, s.Valid n) :
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

/-- Apply a wiring diagram of constants and projections to a fan-in-two circuit.
    Two tracked witness rows force a strict saving if the restricted function
    still takes both truth values. The result is a circuit in the project model. -/
theorem pin_circuit (n : ℕ) (C : Circuit) (fan : FanInTwo C)
    (labels : List Stat) (valid : ∀ s ∈ labels, s.Valid n)
    (l r : List Bool) (tracked : Tracked l r labels)
    (diff : C.eval l ≠ C.eval r)
    (vary : ∃ x y : List Bool, x.length = n ∧ y.length = n ∧
      C.eval (assigned labels x) ≠ C.eval (assigned labels y)) :
    ∃ D : Circuit, FanInTwo D ∧ cost D.gates + 1 ≤ cost C.gates ∧
      ∀ x : List Bool, x.length = n → D.eval x = C.eval (assigned labels x) := by
  let a : List Stat × List Gate := (labels,[])
  let out := elim n C.gates a
  have semantics (x : List Bool) (hx : x.length = n) :
      (out.1.getD C.output (.const false)).val (wiresFrom out.2 x) =
        C.eval (assigned labels x) := by
    exact ((inv_elim n x hx C.gates (assigned labels x) a fan
      (assigned_inv n labels x hx valid)).2 C.output).2
  cases hout : out.1.getD C.output (.const false) with
  | const b =>
    obtain ⟨x,y,hx,hy,xy⟩ := vary
    have e₁ := semantics x hx
    have e₂ := semantics y hy
    rw [hout] at e₁ e₂
    exact (xy (e₁.symm.trans e₂)).elim
  | wire o =>
    refine ⟨⟨out.2,o⟩,elim_ok n C.gates a (by simp [a]),?_,?_⟩
    · have h := pin_saves_charged n C.gates a l r C.output o fan tracked diff hout
      simpa [a,cost, out] using h
    · intro x hx
      have h := semantics x hx
      rw [hout] at h
      exact h

end Triple2836.Pinning
