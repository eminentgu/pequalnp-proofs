import ThreeRows

namespace PEqualNP.Research.GuardedReaders

open CircuitLowerBounds EdgeOwnership MetaComplexity MetaComplexity.NestedCover

/-- A vertex guard for reader `i` means that varying the signal reaching this reader
can affect the final output only on inputs with that vertex set. -/
def VertexGuard {n α} (s : Readers α) (gs : List Gate) (port : α → Nat)
    (i : Fin s.count) (w : Fin n) : Prop :=
  ∀ x : Fin n → Bool, Influential (fun flags => s.bank flags (wireEnv gs port x)) i → x w = true

/-- A common AND of disjoint disjunctions cannot belong to a least circuit in this layout
if every reader has a vertex guard, even when subsequent computation is shared. -/
theorem disjoint_ORs_forbid_vertex_guards {n : Nat} {α : Type} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (gs : List Gate) (port : α → Nat) (s : Readers α) (l r : α)
    (bound : ∀ a, port a < n + gs.length) (m : Monotone2 ⟨gs,0⟩)
    (correct : circuitFun n (attach n gs port (s.original l r)) = graphFun G ∅)
    (L R : Finset (Fin n)) (disjoint : Disjoint L R)
    (left : ∀ x : Fin n → Bool, wireEnv gs port x l = true ↔ ∃ a ∈ L, x a = true)
    (right : ∀ x : Fin n → Bool, wireEnv gs port x r = true ↔ ∃ a ∈ R, x a = true)
    (watch : ∀ i, ∃ w : Fin n, VertexGuard s gs port i w) :
    ¬IsMinimalMonoCircuit n (attach n gs port (s.original l r)) := by
  intro optimum
  obtain ⟨i,⟨x,⟨_,_,xr⟩,supportX⟩,⟨y,⟨_,yl,_⟩,supportY⟩,z,⟨a,b,_,rfl,zl,zr⟩,supportZ⟩ :=
    optimum_three_rows G gs port s l r bound m correct optimum
  obtain ⟨w,guard⟩ := watch i
  have wL : w ∉ L := by
    intro member
    have yes := (left y).2 ⟨w,member,guard y supportY⟩
    exact Bool.noConfusion (yes.symm.trans yl)
  have wR : w ∉ R := by
    intro member
    have yes := (right x).2 ⟨w,member,guard x supportX⟩
    exact Bool.noConfusion (yes.symm.trans xr)
  obtain ⟨p,pL,zp⟩ := (left _).1 zl
  obtain ⟨q,qR,zq⟩ := (right _).1 zr
  have zw := guard _ supportZ
  have pq : p ≠ q := fun e => (Finset.disjoint_left.mp disjoint pL) (e ▸ qR)
  simp only [pairInput,decide_eq_true_eq] at zp zq zw
  grind

/-- The routing used for a vertex guard chooses the other operand if its own variable
already implies one operand. An external guard can omit the signal. -/
def vertexRoute {n} (L R : Finset (Fin n)) (w : Fin n) : Route :=
  if w ∈ L then .right else if w ∈ R then .left else .omit

/-- The explicit rerouting always computes the same graph function. This covers guarded
readers of disjoint positive disjunctions in every graph, regardless of its girth. -/
theorem vertex_guard_exchange {n : Nat} {α : Type} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (gs : List Gate) (port : α → Nat) (s : Readers α) (l r : α)
    (bound : ∀ a, port a < n + gs.length) (m : Monotone2 ⟨gs,0⟩)
    (correct : circuitFun n (attach n gs port (s.original l r)) = graphFun G ∅)
    (L R : Finset (Fin n)) (disjoint : Disjoint L R)
    (left : ∀ x : Fin n → Bool, wireEnv gs port x l = true ↔ ∃ a ∈ L, x a = true)
    (right : ∀ x : Fin n → Bool, wireEnv gs port x r = true ↔ ∃ a ∈ R, x a = true)
    (guard : Fin s.count → Fin n) (active : ∀ i, VertexGuard s gs port i (guard i)) :
    let o := fun i => vertexRoute L R (guard i)
    let C := attach n gs port (s.original l r)
    let D := attach n gs port (s.patch o l r id)
    Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size + (1 + s.omissions o) = C.size := by
  classical
  intro o C D
  let v (x : Fin n → Bool) := wireEnv gs port x
  let bank (x : Fin n → Bool) (flags : Fin s.count → Bool) := s.bank flags (v x)
  have old (x : Fin n → Bool) : bank x (fun _ => v x l && v x r) = graphFun G ∅ x := by
    have h := congrFun correct x
    rw [attach_value _ _ _ _ bound,Readers.original_value,Readers.constant_bank] at h
    exact h
  obtain ⟨legal,size,test⟩ := patch_criterion G gs port s o l r bound m
  refine ⟨legal,test.mpr ⟨?_,?_⟩,size⟩
  · intro a b edge
    let x := pairInput a b
    have graphOn : graphFun G ∅ x = true := by
      simp [graphFun,x]; exact ⟨a,b,edge,by simp [pairInput],by simp [pairInput]⟩
    change s.patchedValue o (v x l) (v x r) (v x) = true
    rw [Readers.patched_bank]
    by_cases both : (v x l && v x r) = true
    · obtain ⟨hl,hr⟩ := Bool.and_eq_true_iff.mp both
      obtain ⟨p,pL,hp⟩ := (left x).1 hl
      obtain ⟨q,qR,hq⟩ := (right x).1 hr
      have pq : p ≠ q := fun e => (Finset.disjoint_left.mp disjoint pL) (e ▸ qR)
      rw [hl,hr]
      have eq := agree_on_influential (bank x) (fun i => (o i).bit true true) (fun _ => true)
        (fun i hi => by
          have hw := active i x hi
          simp only [x,pairInput,decide_eq_true_eq] at hp hq hw
          have member : guard i ∈ L ∨ guard i ∈ R := by grind
          rcases member with le | ri
          · simp [o,vertexRoute,le,Route.bit]
          · by_cases le : guard i ∈ L <;> simp [o,vertexRoute,le,ri,Route.bit])
      exact eq.trans (by simpa only [both] using (old x).trans graphOn)
    · have no : (v x l && v x r) = false := by simpa using both
      have base : bank x (fun _ => false) = true := by simpa only [no] using (old x).trans graphOn
      exact s.bank_mono (fun _ h => False.elim (Bool.noConfusion h)) (fun _ h => h) base
  · intro x off
    change s.patchedValue o (v x l) (v x r) (v x) = false
    rw [Readers.patched_bank]
    cases hl : v x l <;> cases hr : v x r
    · have eq : (fun i => (o i).bit false false) = (fun _ => false) := by funext i; cases o i <;> rfl
      rw [eq]; simpa [hl,hr] using (old x).trans off
    · apply (agree_on_influential (bank x) _ (fun _ => false) ?_).trans (by simpa [hl,hr] using (old x).trans off)
      intro i hi
      have noL : guard i ∉ L := fun member => Bool.noConfusion (((left x).2 ⟨_,member,active i x hi⟩).symm.trans hl)
      by_cases ri : guard i ∈ R <;> simp [o,vertexRoute,noL,ri,Route.bit]
    · apply (agree_on_influential (bank x) _ (fun _ => false) ?_).trans (by simpa [hl,hr] using (old x).trans off)
      intro i hi
      have noR : guard i ∉ R := fun member => Bool.noConfusion (((right x).2 ⟨_,member,active i x hi⟩).symm.trans hr)
      by_cases le : guard i ∈ L <;> simp [o,vertexRoute,le,noR,Route.bit]
    · have base : bank x (fun _ => true) = false := by simpa [hl,hr] using (old x).trans off
      cases h : s.bank (fun i => (o i).bit true true) (v x) with
      | false => rfl
      | true =>
        have yes : bank x (fun _ => true) = true := s.bank_mono (fun _ _ => rfl) (fun _ h => h) h
        exact False.elim (Bool.noConfusion (yes.symm.trans base))

end PEqualNP.Research.GuardedReaders
