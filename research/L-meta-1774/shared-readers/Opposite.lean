import Shannon

namespace PEqualNP.Research.GuardedReaders

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover

/-- The value can be changed by rerouting just this reader, with all other choices fixed. -/
def Influential {ι : Type} (f : (ι → Bool) → Bool) (i : ι) : Prop :=
  ∃ a b : ι → Bool, (∀ j, j ≠ i → a j = b j) ∧ f a ≠ f b

theorem agree_on_influential {ι : Type} [Fintype ι] (f : (ι → Bool) → Bool)
    (a b : ι → Bool) (same : ∀ i, Influential f i → a i = b i) : f a = f b := by
  classical
  suffices aux : ∀ (S : Finset ι) (a b : ι → Bool), (∀ j ∉ S, a j = b j) →
      (∀ j, Influential f j → a j = b j) → f a = f b from
    aux Finset.univ a b (by simp) same
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro a b h _
    exact congrArg f (funext (by simpa using h))
  | @insert i S ne ih =>
    intro a b h agreed
    let c := Function.update a i (b i)
    have others : ∀ j, j ≠ i → a j = c j := by
      intro j hj
      simp [c,Function.update_of_ne hj]
    have first : f a = f c := by
      by_contra different
      obtain eq := agreed i ⟨a,c,others,different⟩
      have ac : a = c := by
        funext j
        by_cases hj : j = i
        · simpa [c,hj] using eq
        · exact others j hj
      exact different (congrArg f ac)
    apply first.trans (ih c b ?_ ?_)
    · intro j jS
      by_cases ji : j = i
      · simp [c,ji]
      · exact (others j ji).symm.trans (h j (by simp [ji,jS]))
    · intro j hj
      by_cases ji : j = i
      · simp [c,ji]
      · exact (others j ji).symm.trans (agreed j hj)

/-- If every orientation leaks on one of two kinds of row, and their uniformly safe
orientations are opposite, the two kinds have a common influential coordinate. -/
theorem opposing_support {ι X : Type} [Fintype ι] (L R : X → Prop)
    (trial : (ι → Bool) → X → Bool)
    (zero : ∀ x, L x → trial (fun _ => false) x = false)
    (one : ∀ x, R x → trial (fun _ => true) x = false)
    (leak : ∀ o, ∃ x, (L x ∨ R x) ∧ trial o x = true) :
    ∃ i, (∃ x, L x ∧ Influential (fun o => trial o x) i) ∧
      (∃ y, R y ∧ Influential (fun o => trial o y) i) := by
  classical
  let Left (i : ι) := ∃ x, L x ∧ Influential (fun o => trial o x) i
  let o (i : ι) := !decide (Left i)
  by_contra absent
  obtain ⟨x,lr,tr⟩ := leak o
  rcases lr with hx | hx
  · have h := agree_on_influential (fun t => trial t x) o (fun _ => false) (fun i hi => by
      have yes : Left i := ⟨x,hx,hi⟩
      simp [o,yes])
    exact Bool.noConfusion (tr.symm.trans (h.trans (zero x hx)))
  · have h := agree_on_influential (fun t => trial t x) o (fun _ => true) (fun i hi => by
      have no : ¬Left i := fun lh => absent ⟨i,lh,x,hx,hi⟩
      simp [o,no])
    exact Bool.noConfusion (tr.symm.trans (h.trans (one x hx)))

def Readers.count {α} (s : Readers α) : Nat := match s with
  | .finish _ => 0
  | .reader _ _ _ rest => rest.count + 1

def Readers.orient {α} (s : Readers α) (o : Fin s.count → Bool) : Readers α := match s with
  | .finish t => .finish t
  | .reader _ g b rest => .reader (o ⟨0,Nat.zero_lt_succ _⟩) g b (rest.orient (fun i => o i.succ))

theorem Readers.orient_size {α} (s : Readers α) (o : Fin s.count → Bool) :
    (s.orient o).size = s.size := by
  induction s with
  | finish => rfl
  | reader k g b rest ih => simp [Readers.orient,Readers.size,ih]

theorem Readers.orient_const_read {α} (s : Readers α) (o : Fin s.count → Bool)
    (q : Bool) (v : α → Bool) : (s.orient o).value (fun _ => q) v = s.value (fun _ => q) v := by
  induction s with
  | finish => rfl
  | reader k g b rest ih => simp [Readers.orient,Readers.value,ih]

theorem Readers.uniform {α} (s : Readers α) (b : Bool) (read : Bool → Bool) (v : α → Bool) :
    (s.orient (fun _ => b)).value read v = s.value (fun _ => read b) v := by
  induction s with
  | finish => rfl
  | reader k g b rest ih => simp only [Readers.orient,Readers.value,ih]

def wireEnv {n α} (gs : List Gate) (port : α → Nat) (x : Fin n → Bool) (i : α) : Bool :=
  (before gs x).getD (port i) false

def Readers.trial {n α} (s : Readers α) (gs : List Gate) (port : α → Nat) (l r : α)
    (o : Fin s.count → Bool) (x : Fin n → Bool) : Bool :=
  let v := wireEnv gs port x
  (s.orient o).value (fun k => if k then v l else v r) v

/-- In a minimum circuit, some single reader is influential on both a left-only and a
right-only independent input. The other readers' settings may differ between the inputs. -/
theorem optimum_has_two_sided_reader {n : Nat} {α : Type} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (gs : List Gate) (port : α → Nat) (s : Readers α) (l r : α)
    (bound : ∀ a, port a < n + gs.length) (m : Monotone2 ⟨gs,0⟩)
    (correct : circuitFun n (attach n gs port (s.original l r)) = graphFun G ∅)
    (optimum : IsMinimalMonoCircuit n (attach n gs port (s.original l r))) :
    ∃ i : Fin s.count,
      (∃ x : Fin n → Bool, (graphFun G ∅ x = false ∧ wireEnv gs port x l = true ∧
        wireEnv gs port x r = false) ∧ Influential (fun o => s.trial gs port l r o x) i) ∧
      (∃ y : Fin n → Bool, (graphFun G ∅ y = false ∧ wireEnv gs port y l = false ∧
        wireEnv gs port y r = true) ∧ Influential (fun o => s.trial gs port l r o y) i) := by
  classical
  let v (x : Fin n → Bool) := wireEnv gs port x
  let test (o : Fin s.count → Bool) (x : Fin n → Bool) := s.trial gs port l r o x
  have old (x : Fin n → Bool) : s.value (fun _ => v x l && v x r) (v x) = graphFun G ∅ x := by
    have h := congrFun correct x
    rw [attach_value _ _ _ _ bound,Readers.original_value] at h
    exact h
  have physical (o : Fin s.count → Bool) (x : Fin n → Bool) :
      circuitFun n (attach n gs port ((s.orient o).rerouted l r)) x = test o x := by
    rw [attach_value _ _ _ _ bound,Readers.rerouted_value]
    rfl
  have grows (o) (x) : graphFun G ∅ x = true → test o x = true := by
    intro hx
    have initial : (s.orient o).value (fun _ => v x l && v x r) (v x) = true :=
      ((s.orient_const_read o _ _).trans (old x)).trans hx
    have safe (k : Bool) : (v x l && v x r) = true → (if k then v x l else v x r) = true := by
      cases k <;> simp_all
    exact (s.orient o).value_mono safe (fun _ h => h) initial
  have witness (o) : ∃ x : Fin n → Bool, graphFun G ∅ x = false ∧ test o x = true := by
    by_contra fail
    have eq : circuitFun n (attach n gs port ((s.orient o).rerouted l r)) = graphFun G ∅ := by
      funext x
      rw [physical]
      cases hx : graphFun G ∅ x with
      | true => exact grows o x hx
      | false =>
        cases h : test o x with
        | false => rfl
        | true => exact False.elim (fail ⟨x,hx,h⟩)
    have le := optimum.2 _ (attach_mono n gs port _ m) (eq.trans correct.symm)
    simp only [attach_size,Readers.original,Readers.rerouted,Net.size,Readers.compile_size,
      Readers.orient_size] at le
    omega
  have common (o) (x) (he : v x l = v x r) : test o x = graphFun G ∅ x := by
    have eq : (fun k : Bool => if k then v x l else v x r) = (fun _ => v x l && v x r) := by
      funext k
      cases k <;> simp [he]
    change (s.orient o).value _ (v x) = _
    rw [eq,Readers.orient_const_read]
    exact old x
  apply opposing_support (trial := test)
  · rintro x ⟨hx,hl,hr⟩
    change (s.orient (fun _ => false)).value _ (v x) = false
    rw [Readers.uniform]
    simpa [v,hl,hr] using (old x).trans hx
  · rintro x ⟨hx,hl,hr⟩
    change (s.orient (fun _ => true)).value _ (v x) = false
    rw [Readers.uniform]
    simpa [v,hl,hr] using (old x).trans hx
  · intro o
    obtain ⟨x,off,on⟩ := witness o
    refine ⟨x,?_,on⟩
    have diff : v x l ≠ v x r := fun eq => Bool.noConfusion (on.symm.trans ((common o x eq).trans off))
    cases hl : v x l <;> cases hr : v x r
    · exact False.elim (diff (hl.trans hr.symm))
    · exact Or.inr ⟨off,hl,hr⟩
    · exact Or.inl ⟨off,hl,hr⟩
    · exact False.elim (diff (hl.trans hr.symm))

end PEqualNP.Research.GuardedReaders
