import Omit

namespace PEqualNP.Research.GuardedReaders

open CircuitLowerBounds EdgeOwnership MetaComplexity MetaComplexity.NestedCover

def Route.bit (k : Route) (l r : Bool) : Bool := match k with
  | .left => l | .right => r | .omit => false

/-- Independently set the signal arriving at each reader while retaining the actual
prefix assignment. Later readers can still depend on the earlier guarded outputs. -/
def Readers.bank {α} (s : Readers α) (on : Fin s.count → Bool) (v : α → Bool) : Bool := match s with
  | .finish t => t.value v
  | .reader _ g b rest => rest.bank (fun i => on i.succ)
      (fun z => z.elim (v g && (on ⟨0,Nat.zero_lt_succ _⟩ || v b)) v)

theorem Readers.patched_bank {α} (s : Readers α) (o : Fin s.count → Route) (l r : Bool) (v : α → Bool) :
    s.patchedValue o l r v = s.bank (fun i => (o i).bit l r) v := by
  induction s with
  | finish => rfl
  | reader side g b rest ih =>
    cases h : o ⟨0,Nat.zero_lt_succ _⟩ <;>
      simp only [Readers.patchedValue,Readers.bank,h,ih,Route.bit,Bool.false_or]

theorem Readers.constant_bank {α} (s : Readers α) (q : Bool) (v : α → Bool) :
    s.value (fun _ => q) v = s.bank (fun _ => q) v := by
  induction s with
  | finish => rfl
  | reader side g b rest ih => simp only [Readers.value,Readers.bank,ih]

theorem Readers.bank_mono {α} (s : Readers α) {a b : Fin s.count → Bool} {v w : α → Bool}
    (ab : ∀ i, a i = true → b i = true) (vw : ∀ i, v i = true → w i = true) :
    s.bank a v = true → s.bank b w = true := by
  induction s with
  | finish t => exact t.value_mono vw
  | reader side g x rest ih =>
    apply ih (fun i => ab i.succ)
    intro z
    cases z with
    | some i => exact vw i
    | none =>
      exact bin_mono (op := true) (vw g) (bin_mono (op := false) (ab ⟨0,Nat.zero_lt_succ _⟩) (vw x))

private theorem assign_three {ι X : Type} [Fintype ι] (L R E : X → Prop)
    (bank : X → (ι → Bool) → Bool)
    (absent : ¬∃ i, (∃ x, L x ∧ Influential (bank x) i) ∧
      (∃ y, R y ∧ Influential (bank y) i) ∧ (∃ z, E z ∧ Influential (bank z) i)) :
    ∃ o : ι → Route,
      (∀ x, L x → bank x (fun i => (o i).bit true false) = bank x (fun _ => false)) ∧
      (∀ y, R y → bank y (fun i => (o i).bit false true) = bank y (fun _ => false)) ∧
      (∀ z, E z → bank z (fun i => (o i).bit true true) = bank z (fun _ => true)) := by
  classical
  let LS (i : ι) := ∃ x, L x ∧ Influential (bank x) i
  let RS (i : ι) := ∃ x, R x ∧ Influential (bank x) i
  let o (i : ι) : Route := if ¬LS i then .left else if ¬RS i then .right else .omit
  refine ⟨o,?_,?_,?_⟩
  · intro x hx
    apply agree_on_influential
    intro i hi
    have yes : LS i := ⟨x,hx,hi⟩
    simp [o,yes]; split <;> rfl
  · intro y hy
    apply agree_on_influential
    intro i hi
    have yes : RS i := ⟨y,hy,hi⟩
    simp [o,yes]; split <;> rfl
  · intro z hz
    apply agree_on_influential
    intro i hi
    by_cases lh : LS i
    · have rh : ¬ RS i := fun rh => absent ⟨i,lh,rh,z,hz,hi⟩
      simp [o,lh,rh,Route.bit]
    · simp [o,lh,Route.bit]

/-- Least size forces one reader influential on each of three types of inputs: independent
left-only, independent right-only, and an actual edge on which both operands are true. -/
theorem optimum_three_rows {n : Nat} {α : Type} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (gs : List Gate) (port : α → Nat) (s : Readers α) (l r : α)
    (bound : ∀ a, port a < n + gs.length) (m : Monotone2 ⟨gs,0⟩)
    (correct : circuitFun n (attach n gs port (s.original l r)) = graphFun G ∅)
    (optimum : IsMinimalMonoCircuit n (attach n gs port (s.original l r))) :
    let v := fun x => wireEnv gs port x
    let pivotal := fun (x : Fin n → Bool) => Influential (fun a => s.bank a (v x))
    ∃ i : Fin s.count,
      (∃ x, (graphFun G ∅ x = false ∧ v x l = true ∧ v x r = false) ∧ pivotal x i) ∧
      (∃ y, (graphFun G ∅ y = false ∧ v y l = false ∧ v y r = true) ∧ pivotal y i) ∧
      (∃ z, (∃ a b, G.Adj a b ∧ z = pairInput a b ∧ v z l = true ∧ v z r = true) ∧ pivotal z i) := by
  classical
  intro v pivotal
  let L (x : Fin n → Bool) := graphFun G ∅ x = false ∧ v x l = true ∧ v x r = false
  let R (x : Fin n → Bool) := graphFun G ∅ x = false ∧ v x l = false ∧ v x r = true
  let E (x : Fin n → Bool) := ∃ a b, G.Adj a b ∧ x = pairInput a b ∧ v x l = true ∧ v x r = true
  let bank (x : Fin n → Bool) (a : Fin s.count → Bool) := s.bank a (v x)
  have old (x : Fin n → Bool) : bank x (fun _ => v x l && v x r) = graphFun G ∅ x := by
    have h := congrFun correct x
    rw [attach_value _ _ _ _ bound,Readers.original_value,Readers.constant_bank] at h
    exact h
  by_contra absent
  obtain ⟨o,offL,offR,onE⟩ := assign_three L R E bank absent
  obtain ⟨legal,size,iff⟩ := patch_criterion G gs port s o l r bound m
  let D := attach n gs port (s.patch o l r id)
  have eq : circuitFun n D = graphFun G ∅ := by
    apply iff.mpr
    constructor
    · intro a b edge
      let x := pairInput a b
      have on : graphFun G ∅ x = true := by
        simp [graphFun,x]; exact ⟨a,b,edge,by simp [pairInput],by simp [pairInput]⟩
      change s.patchedValue o (v x l) (v x r) (v x) = true
      rw [Readers.patched_bank]
      by_cases yes : (v x l && v x r) = true
      · have both := Bool.and_eq_true_iff.mp yes
        rw [both.1,both.2]
        have same := onE x ⟨a,b,edge,rfl,both⟩
        exact same.trans (by simpa only [yes] using (old x).trans on)
      · have no : (v x l && v x r) = false := by simpa using yes
        have initial : bank x (fun _ => false) = true := by simpa only [no] using (old x).trans on
        exact s.bank_mono (fun _ h => False.elim (Bool.noConfusion h)) (fun _ h => h) initial
    · intro x off
      change s.patchedValue o (v x l) (v x r) (v x) = false
      rw [Readers.patched_bank]
      cases hl : v x l <;> cases hr : v x r
      · have eq : (fun i => (o i).bit false false) = (fun _ => false) := by
          funext i; cases o i <;> rfl
        rw [eq]; simpa [hl,hr] using (old x).trans off
      · exact (offR x ⟨off,hl,hr⟩).trans (by simpa [hl,hr] using (old x).trans off)
      · exact (offL x ⟨off,hl,hr⟩).trans (by simpa [hl,hr] using (old x).trans off)
      · have initial : bank x (fun _ => true) = false := by simpa [hl,hr] using (old x).trans off
        cases h : s.bank (fun i => (o i).bit true true) (v x) with
        | false => rfl
        | true =>
          have impossible : bank x (fun _ => true) = true := s.bank_mono (fun _ _ => rfl) (fun _ h => h) h
          exact False.elim (Bool.noConfusion (impossible.symm.trans initial))
  have lower := optimum.2 _ legal (eq.trans correct.symm)
  omega

end PEqualNP.Research.GuardedReaders
