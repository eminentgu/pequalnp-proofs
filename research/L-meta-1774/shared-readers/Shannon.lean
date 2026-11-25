import Guarded

namespace PEqualNP.Research.GuardedReaders

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover

private def choice (l r : Bool) (s : Bool) := if s then l else r

private def crossed (s : Bool) (l r g b : Bool) := g && (choice l r s || b)

private def saved (l r g b : Bool) := g && ((l && r) || b)

private theorem lift_choice (l r s : Bool) (h : (l && r) = true) : choice l r s = true := by
  cases s <;> simp_all [choice]

private theorem saved_le (s l r g b : Bool) : saved l r g b = true → crossed s l r g b = true := by
  apply bin_mono (op := true) id
  exact bin_mono (op := false) (lift_choice l r s) id

/-- Each reader is compared with the same already-chosen prefix and the fully rerouted
suffix. If rerouting flips its exported port on this input, the Boolean output cofactors of
the suffix at this port must agree. Earlier reader outputs use their original values. -/
def Readers.masked {α} (s : Readers α) (l r : Bool) (v : α → Bool) : Prop := match s with
  | .finish _ => True
  | .reader side g b rest =>
    let old := saved l r (v g) (v b)
    let fresh := crossed side l r (v g) (v b)
    let suffix := fun bit => rest.value (choice l r) (fun z => z.elim bit v)
    (old ≠ fresh → suffix false = suffix true) ∧ rest.masked l r (fun z => z.elim old v)

private theorem bool_chain {a b c : Bool} (h : a = true → b = true) (k : b = true → c = true) :
    (c = b ∧ b = a) ↔ c = a := by cases a <;> cases b <;> cases c <;> simp_all

/-- The cofactor test is necessary and sufficient on a single input, even when a reader
output is reused by many later AND/OR gates. -/
theorem Readers.masked_iff {α} (s : Readers α) (l r : Bool) (v : α → Bool) :
    s.masked l r v ↔ s.value (fun k => if k then l else r) v = s.value (fun _ => l && r) v := by
  induction s with
  | finish => simp [Readers.masked,Readers.value]
  | reader side g b rest ih =>
    let old := saved l r (v g) (v b)
    let fresh := crossed side l r (v g) (v b)
    let w := fun (t : Bool) (z : Option _) => z.elim t v
    let f := fun t => rest.value (choice l r) (w t)
    let initial := rest.value (fun _ => l && r) (w old)
    change ((old ≠ fresh → f false = f true) ∧ rest.masked l r (w old)) ↔ f fresh = initial
    have localCofactors : (old ≠ fresh → f false = f true) ↔ f fresh = f old := by
      cases old <;> cases fresh <;> simp [eq_comm]
    have lower : initial = true → f old = true :=
      rest.value_mono (lift_choice l r) (fun _ h => h)
    have upper : f old = true → f fresh = true := by
      apply rest.value_mono (fun _ h => h)
      intro z
      cases z with
      | none => exact saved_le _ _ _ _ _
      | some a => exact id
    rw [localCofactors,ih]
    exact bool_chain lower upper

/-- The physical reader rerouting is an exact alternate circuit for the graph precisely
when every independent input passes the sequential cofactor test. The two circuits always
differ in size by exactly the one shared AND gate. -/
theorem shannon_exchange_iff {n : Nat} {α : Type} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gs : List Gate) (port : α → Nat) (s : Readers α) (l r : α)
    (bound : ∀ a, port a < n + gs.length)
    (correct : circuitFun n (attach n gs port (s.original l r)) = graphFun G ∅) :
    circuitFun n (attach n gs port (s.rerouted l r)) = graphFun G ∅ ↔
    ∀ x : Fin n → Bool, graphFun G ∅ x = false →
      let v := fun a => (before gs x).getD (port a) false
      s.masked (v l) (v r) v := by
  constructor
  · intro good x _
    let v := fun a => (before gs x).getD (port a) false
    apply (s.masked_iff (v l) (v r) v).mpr
    have h := (congrFun good x).trans (congrFun correct x).symm
    rw [attach_value _ _ _ _ bound,attach_value _ _ _ _ bound] at h
    exact (Readers.rerouted_value s l r v).symm.trans (h.trans (Readers.original_value s l r v))
  · intro h
    funext x
    let v := fun a => (before gs x).getD (port a) false
    have old := congrFun correct x
    rw [attach_value _ _ _ _ bound, Readers.original_value] at old
    rw [attach_value _ _ _ _ bound, Readers.rerouted_value]
    cases hx : graphFun G ∅ x with
    | false => exact ((s.masked_iff (v l) (v r) v).mp (h x hx)).trans (old.trans hx)
    | true => exact s.value_mono (lift_choice _ _) (fun _ h => h) (old.trans hx)

/-- Every choice of parent wires in a globally minimal circuit with this layout has an
independent input on which a reader flips and the downstream cofactors at that reader differ. -/
theorem optimal_forces_observable_failure {n : Nat} {α : Type} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (gs : List Gate) (port : α → Nat) (s : Readers α) (l r : α)
    (bound : ∀ a, port a < n + gs.length) (m : Monotone2 ⟨gs,0⟩)
    (correct : circuitFun n (attach n gs port (s.original l r)) = graphFun G ∅)
    (optimum : IsMinimalMonoCircuit n (attach n gs port (s.original l r))) :
    ∃ x : Fin n → Bool, graphFun G ∅ x = false ∧
      let v := fun a => (before gs x).getD (port a) false
      ¬ s.masked (v l) (v r) v := by
  by_contra! h
  have eq := (shannon_exchange_iff G gs port s l r bound correct).mpr
    (fun x hx => Classical.byContradiction (h x hx))
  have le := optimum.2 _ (attach_mono n gs port _ m) (eq.trans correct.symm)
  have saved : (attach n gs port (s.rerouted l r)).size + 1 =
      (attach n gs port (s.original l r)).size := by
    simp [attach_size,Readers.original,Readers.rerouted,Net.size,Readers.compile_size,Nat.add_assoc]
  omega

end PEqualNP.Research.GuardedReaders
