import Opposite
import PEqualNP.Outside.L_meta_2573

namespace PEqualNP.Research.GuardedReaders

open CircuitLowerBounds EdgeOwnership MetaComplexity MetaComplexity.NestedCover

/-- Each reader may also omit the shared operand, turning `H ∧ (J ∨ B)` into `H ∧ B`. -/
inductive Route where | left | right | omit deriving DecidableEq

def Readers.omissions {α} (s : Readers α) (o : Fin s.count → Route) : Nat := match s with
  | .finish _ => 0
  | .reader _ _ _ rest => rest.omissions (fun i => o i.succ) +
      if o ⟨0,Nat.zero_lt_succ _⟩ = .omit then 1 else 0

def Readers.patch {α β} (s : Readers α) (o : Fin s.count → Route) (l r : β) (f : α → β) : Net β :=
  match s with
  | .finish t => t.rename f
  | .reader _ g b rest =>
    let next := fun i => o i.succ
    let use (u : β) := Net.gate false u (f b) <| .gate true (some (f g)) none <|
      rest.patch next (some (some l)) (some (some r)) (fun z => z.elim none (fun a => some (some (f a))))
    match o ⟨0,Nat.zero_lt_succ _⟩ with
    | .left => use l
    | .right => use r
    | .omit => .gate true (f g) (f b) <|
      rest.patch next (some l) (some r) (fun z => z.elim none (fun a => some (f a)))

def Readers.patchedValue {α} (s : Readers α) (o : Fin s.count → Route) (l r : Bool) (v : α → Bool) : Bool :=
  match s with
  | .finish t => t.value v
  | .reader _ g b rest =>
    let alternative := match o ⟨0,Nat.zero_lt_succ _⟩ with
      | .left => l || v b
      | .right => r || v b
      | .omit => v b
    rest.patchedValue (fun i => o i.succ) l r (fun z => z.elim (v g && alternative) v)

theorem Readers.patch_size {α β} (s : Readers α) (o : Fin s.count → Route) (l r : β) (f : α → β) :
    (s.patch o l r f).size + s.omissions o = s.size := by
  induction s generalizing β with
  | finish t => simp [Readers.patch,Readers.size,Readers.omissions,t.rename_size]
  | reader side g b rest ih =>
    cases h : o ⟨0,Nat.zero_lt_succ _⟩ <;>
      simp [Readers.patch,Readers.omissions,Readers.size,Net.size,h] <;>
      first | have hz := ih (fun i => o i.succ) (some (some l)) (some (some r))
                  (fun z => z.elim none (fun a => some (some (f a)))); omega
            | have hz := ih (fun i => o i.succ) (some l) (some r)
                  (fun z => z.elim none (fun a => some (f a))); omega

theorem Readers.patch_value {α β} (s : Readers α) (o : Fin s.count → Route) (l r : β)
    (f : α → β) (v : β → Bool) :
    (s.patch o l r f).value v = s.patchedValue o (v l) (v r) (fun a => v (f a)) := by
  induction s generalizing β with
  | finish t => exact t.rename_value f v
  | reader side g b rest ih =>
    cases h : o ⟨0,Nat.zero_lt_succ _⟩ <;>
      simp only [Readers.patch,Readers.patchedValue,h,Net.value,ih] <;>
      congr 1 <;> funext z <;> cases z <;> rfl

theorem graph_rows_iff {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit)
    (mono : Monotone2 D) : circuitFun n D = graphFun G ∅ ↔
    (∀ a b, G.Adj a b → circuitFun n D (pairInput a b) = true) ∧
    (∀ x, graphFun G ∅ x = false → circuitFun n D x = false) := by
  constructor
  · intro correct
    refine ⟨?_,fun x h => (congrFun correct x).trans h⟩
    intro a b edge
    rw [correct]
    simp only [graphFun,Finset.notMem_empty, false_and, exists_false,decide_false,Bool.false_or,decide_eq_true_eq]
    exact ⟨a,b,edge,by simp [pairInput],by simp [pairInput]⟩
  · rintro ⟨edge,indep⟩
    funext x
    cases hx : graphFun G ∅ x with
    | false => exact indep x hx
    | true =>
      obtain ⟨a,b,ad,ha,hb⟩ : ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by simpa [graphFun] using hx
      apply Outside.L_meta_2573.eval_mono D mono (pairInput a b) x _ (edge a b ad)
      intro j hj
      simp only [pairInput,decide_eq_true_eq] at hj
      rcases hj with rfl | rfl <;> assumption

/-- Routing and omission are certified from the candidate's symbolic row evaluations. A
direct omission saves its reader OR as well as the removal of the shared AND. -/
theorem patch_criterion {n α} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gs : List Gate) (port : α → Nat) (s : Readers α) (o : Fin s.count → Route) (l r : α)
    (bound : ∀ a, port a < n + gs.length) (m : Monotone2 ⟨gs,0⟩) :
    let C := attach n gs port (s.original l r)
    let D := attach n gs port (s.patch o l r id)
    let val := fun (x : Fin n → Bool) =>
      let v := wireEnv gs port x
      s.patchedValue o (v l) (v r) v
    Monotone2 D ∧ D.size + (1 + s.omissions o) = C.size ∧
      (circuitFun n D = graphFun G ∅ ↔
        (∀ a b, G.Adj a b → val (pairInput a b) = true) ∧
        (∀ x, graphFun G ∅ x = false → val x = false)) := by
  intro C D val
  have legal : Monotone2 D := attach_mono _ _ _ _ m
  refine ⟨legal,?_,?_⟩
  · have size := s.patch_size o l r id
    simp only [C,D,attach_size,Readers.original,Net.size,Readers.compile_size]
    omega
  · have eq (x : Fin n → Bool) : circuitFun n D x = val x :=
      (attach_value _ _ _ _ bound x).trans (s.patch_value o l r id (wireEnv gs port x))
    simpa only [eq] using graph_rows_iff G D legal

end PEqualNP.Research.GuardedReaders
