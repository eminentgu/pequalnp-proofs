import LiteralGuards

namespace PEqualNP.Research.GuardedReaders

/-- Trace a guard port to a named prefix wire. A newly produced reader output receives
no primary-input name, while every pre-existing port preserves its original name. -/
def Readers.guardWire {α X : Type} (s : Readers α) (label : α → Option X) : Fin s.count → Option X :=
  match s with
  | .finish _ => Fin.elim0
  | .reader _ g _ rest => Fin.cases (label g) (rest.guardWire (fun z => z.elim none label))

private theorem unchanged_at_false_guard {α X : Type} (s : Readers α) (label : α → Option X)
    (v : α → Bool) (x : X → Bool) (tracks : ∀ a w, label a = some w → v a = x w)
    (i : Fin s.count) (w : X) (named : s.guardWire label i = some w) (off : x w = false)
    (a b : Fin s.count → Bool) (others : ∀ j, j ≠ i → a j = b j) : s.bank a v = s.bank b v := by
  induction s with
  | finish => exact Fin.elim0 i
  | reader k g alt rest ih =>
    have aux (index : Fin (rest.count+1)) (named : (Readers.reader k g alt rest).guardWire label index = some w)
        (others : ∀ j, j ≠ index → a j = b j) :
        (Readers.reader k g alt rest).bank a v = (Readers.reader k g alt rest).bank b v := by
      refine Fin.cases (motive := fun j => (Readers.reader k g alt rest).guardWire label j = some w →
        (∀ t, t ≠ j → a t = b t) → (Readers.reader k g alt rest).bank a v = (Readers.reader k g alt rest).bank b v)
        ?_ ?_ index named others
      · intro name restEq
        have hg : v g = false := (tracks g w name).trans off
        have tailEq : (fun t : Fin rest.count => a t.succ) = (fun t => b t.succ) :=
          funext (fun t => restEq t.succ (Fin.succ_ne_zero t))
        simp only [Readers.bank,hg,Bool.false_and,tailEq]
      · intro j name restEq
        have first : a ⟨0,Nat.zero_lt_succ _⟩ = b ⟨0,Nat.zero_lt_succ _⟩ := restEq _ (Ne.symm (Fin.succ_ne_zero j))
        simp only [Readers.bank,first]
        apply ih (label := fun z => z.elim none label) (i := j)
        · intro z t matchLabel
          cases z with
          | none => cases matchLabel
          | some z => exact tracks z t matchLabel
        · exact name
        · intro t different
          apply restEq t.succ
          intro heq
          exact different (Fin.succ_injective _ heq)
    exact aux i named others

/-- A literal input wire guarding a reader is a semantic vertex guard, regardless of the
number of downstream copies of the reader output. -/
theorem vertexGuard_of_wire {n α} (s : Readers α) (gs : List CircuitLowerBounds.Gate) (port : α → Nat)
    (label : α → Option (Fin n)) (tracks : ∀ x : Fin n → Bool, ∀ a w, label a = some w → wireEnv gs port x a = x w)
    (i : Fin s.count) (w : Fin n) (named : s.guardWire label i = some w) :
    VertexGuard s gs port i w := by
  intro x sensitive
  cases hx : x w with
  | true => rfl
  | false =>
    obtain ⟨a,b,same,different⟩ := sensitive
    exact False.elim (different (unchanged_at_false_guard s label _ x (tracks x) i w named hx a b same))

end PEqualNP.Research.GuardedReaders
