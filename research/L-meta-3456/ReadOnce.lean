import Support

namespace SingletonFiniteFormula.Formula

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open SingletonSupport

variable {α : Type}

def varList : Formula α → List α
  | .atom x => [x]
  | .node _ l r => l.varList ++ r.varList

theorem varList_length (f : Formula α) : f.varList.length = f.leaves := by
  induction f with
  | atom x => rfl
  | node op l r hl hr => simp [varList, leaves, hl, hr]

theorem eval_same_on (f : Formula α) {x y : α → Bool}
    (h : ∀ i ∈ f.varList, x i = y i) : f.eval x = f.eval y := by
  induction f with
  | atom i => exact h i (by simp [varList])
  | node op l r hl hr =>
    have el := hl (fun i hi => h i (List.mem_append_left _ hi))
    have er := hr (fun i hi => h i (List.mem_append_right _ hi))
    simp [eval,el,er]

theorem eval_uniform (f : Formula α) (v : Bool) : f.eval (fun _ => v) = v := by
  induction f with
  | atom x => rfl
  | node op l r hl hr => cases op <;> cases v <;> simp_all [eval,Op.apply]

theorem essential_left {n : Nat} (op : Op) (l r : Formula (Fin n)) (i : Fin n)
    (dis : ∀ a ∈ l.varList, a ∉ r.varList) (old : Essential (fun z => l.eval z) i) :
    Essential (fun z => (Formula.node op l r).eval z) i := by
  obtain ⟨x,y,e,hx,hy⟩ := old
  let b : Bool := match op with | .meet => true | .join => false
  let patch (z : Fin n → Bool) (j : Fin n) := if j ∈ l.varList then z j else b
  have left (z : Fin n → Bool) : l.eval (patch z) = l.eval z :=
    eval_same_on l (fun j hj => by simp [patch,hj])
  have right (z : Fin n → Bool) : r.eval (patch z) = b := by
    rw [← eval_uniform r b]
    apply eval_same_on
    intro j hj
    have hj' : j ∉ l.varList := fun h => dis j h hj
    simp [patch,hj']
  refine ⟨patch x, patch y, fun j hj => by simp [patch, e j hj], ?_, ?_⟩
  · simp only [eval,left,right,hx]
    cases op <;> rfl
  · simp only [eval,left,right,hy]
    cases op <;> rfl

theorem swap_node {n : Nat} (op : Op) (l r : Formula (Fin n)) (z : Fin n → Bool) :
    (Formula.node op l r).eval z = (Formula.node op r l).eval z := by
  cases op <;> simp [eval, Op.apply, Bool.and_comm, Bool.or_comm]

theorem essential_of_nodup {n : Nat} (f : Formula (Fin n)) (h : f.varList.Nodup) :
    ∀ i ∈ f.varList, Essential (fun z => f.eval z) i := by
  induction f with
  | atom a =>
    intro i hi
    have eq : i = a := by simpa [varList] using hi
    subst i
    refine ⟨fun j => decide (j = a), fun _ => false, ?_, by simp [eval], rfl⟩
    intro j hj
    simp [hj]
  | node op l r hl hr =>
    change (l.varList ++ r.varList).Nodup at h
    obtain ⟨lnd,rnd,dis⟩ := List.nodup_append.mp h
    intro i hi
    change i ∈ l.varList ++ r.varList at hi
    rcases List.mem_append.mp hi with hi | hi
    · exact essential_left op l r i (fun a ha hm => dis a ha a hm rfl) (hl lnd i hi)
    · obtain ⟨x,y,e,hx,hy⟩ := essential_left op r l i
        (fun a ha hm => dis a hm a ha rfl) (hr rnd i hi)
      exact ⟨x,y,e,(swap_node op l r x).trans hx,(swap_node op l r y).trans hy⟩

theorem readOnce_optimal {n : Nat} (C : Circuit) (f : Formula (Fin n))
    (mono : Monotone2 C) (nd : f.varList.Nodup)
    (he : ∀ z, f.eval z = circuitFun n C z) : f.gates ≤ C.size := by
  have esc : ∀ i ∈ f.varList.toFinset, Essential (circuitFun n C) i := by
    intro i hi
    obtain ⟨x,y,h,hx,hy⟩ := essential_of_nodup f nd i (List.mem_toFinset.mp hi)
    exact ⟨x,y,h,(he x).symm.trans hx, (he y).symm.trans hy⟩
  have lower := essential_card_le C (fun g hg => (mono g hg).2) _ esc
  rw [List.toFinset_card_of_nodup nd, varList_length, leaves_eq] at lower
  omega

theorem normalize_readOnce {n : Nat} (C : Circuit) (f : Formula (Fin n))
    (mono : Monotone2 C) (nd : f.varList.Nodup)
    (he : ∀ z, f.eval z = circuitFun n C z) :
    ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack n D ∧ D.size ≤ C.size ∧
      (∀ z, circuitFun n D z = circuitFun n C z) ∧
      ∀ j < D.gates.length, (NestedCover.gateAt D j).op = .and →
        ∀ i : Fin n, (D.wires (List.ofFn (single i))).getD (n+j) false = false :=
  circuit_normalize_of_formula C f (readOnce_optimal C f mono nd he) he

end SingletonFiniteFormula.Formula
