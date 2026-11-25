import PinDesk
import PEqualNP.Outside.L_meta_2668

namespace PEqualNP.Research.GatePinning

open CircuitLowerBounds EdgeOwnership MetaComplexity MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_2668 (bypass bypass_mono bypass_length bypass_eval_eq)

/-- Any genuine gate of a minimum circuit has an output-critical edge under clamping.
An unused zero can instead be deleted and all its reads sent to the missing output wire. -/
theorem critical_exists {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit} {k : Nat}
    (least : IsMinimalMonoCircuit n C) (correct : circuitFun n C = graphFun G ∅) (inside : k < C.size) :
    ∃ a b, needed G C k a b := by
  classical
  by_contra absent
  let Z := zero C k
  have bound : k < Z.gates.length := by simpa [Z,zero,Circuit.size] using inside
  have mono : Monotone2 Z := replace_mono least.1 (by simp) (by simp)
  have same : circuitFun n Z = graphFun G ∅ := by
    apply subgate_correct G inside least.1 correct _ mono
    · intro x hx
      exact False.elim (Bool.noConfusion ((zero_value inside x).symm.trans hx))
    · exact fun a b h => False.elim (absent ⟨a,b,h⟩)
  let D := bypass n Z k (n+Z.gates.length)
  have equal : circuitFun n D = circuitFun n Z := by
    funext x
    apply bypass_eval_eq (n := n) (by simp) (fun j hj => (mono _ (Outside.L_meta_5465.gateAt_mem hj)).1)
      bound (Or.inr le_rfl)
    exact (zero_value inside x).trans (Outside.L_meta_2668.val_ge (n := n) (by simp) le_rfl).symm
  have minSize := least.2 D (bypass_mono mono) (equal.trans (same.trans correct.symm))
  have size : D.size = Z.gates.length - 1 := bypass_length ..
  have sz : Z.gates.length = C.size := replace_length ..
  omega

def MultipleCritical {n} (G : SimpleGraph (Fin n)) (C : Circuit) (k : Nat) :=
  ∃ a b c d, needed G C k a b ∧ needed G C k c d ∧ ¬ ((a=c ∧ b=d) ∨ (a=d ∧ b=c))

/-- One critical edge suffices, even when the old gate never owned that particular edge.
The new primary AND owns the edge simply because it has no gate ancestor. -/
theorem repair_if_at_most_one_critical {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hC : Eligible G C) {k : Nat} (inside : k < C.size) (hand : (gateAt C k).op = .and)
    (only : ¬ MultipleCritical G C k) :
    ∃ D : Circuit, Eligible G D ∧ D.size = C.size ∧
      (∀ j < k, BadAt G D j → BadAt G C j) ∧ ¬ BadAt G D k := by
  obtain ⟨u,v,need⟩ := critical_exists G hC.1 hC.2.1 inside
  have choice (a b) (e : needed G C k a b) : (a=u ∧ b=v) ∨ (a=v ∧ b=u) := by
    by_contra wrong
    exact only ⟨a,b,u,v,e,need,wrong⟩
  let D := pin C k u v
  have legal : Monotone2 D := replace_mono hC.1.1 (by simp) (by simp)
  have size : D.size = C.size := replace_length ..
  have below (x : Fin n → Bool) : gateVal n D k x = true → gateVal n C k x = true := by
    rw [pin_value u v inside]
    intro hx
    have both := Bool.and_eq_true_iff.mp hx
    apply Outside.L_meta_2573.wires_mono C (Outside.L_meta_2573.mono2_ops C hC.1.1) (pairInput u v) x _
      (n+k) (needed_turns_on G hC.1.1 inside hC.2.1 need)
    intro w hw
    simp only [pairInput,decide_eq_true_eq] at hw
    rcases hw with rfl | rfl
    · exact both.1
    · exact both.2
  have eq : circuitFun n D = graphFun G ∅ := by
    apply subgate_correct G inside hC.1.1 hC.2.1 _ legal below
    intro a b hit
    change gateVal n (pin C k u v) k (pairInput a b) = true
    rw [pin_value u v inside]
    rcases choice a b hit with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [pairInput]
  have minimal : IsMinimalMonoCircuit n D :=
    ⟨legal,fun E m f => size ▸ hC.1.2 E m (f.trans (eq.trans hC.2.1.symm))⟩
  have productive : Productive G D := by
    intro j hj op
    by_cases target : j = k
    · subst j
      exact ⟨u,v,need.1,pin_owns u v inside⟩
    · have op0 : (gateAt C j).op = .and := (congrArg Gate.op
          (show gateAt D j = gateAt C j from replace_elsewhere target)).symm.trans op
      obtain ⟨a,b,edge,owned⟩ := hC.2.2 j (size ▸ hj) op0
      refine ⟨a,b,edge,other_owners_survive hC.1.1 hand ?_ below target owned⟩
      intro w h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl | rfl
      · exact Or.inl u.isLt
      · exact Or.inl v.isLt
  refine ⟨D,⟨minimal,eq,productive⟩,size,?_,?_⟩
  · rintro j hj ⟨a,b,c,d,ab,cd,i,j,more⟩
    exact ⟨a,b,c,d,ab,cd,before_new_to_old hC.1.1 hj i,before_new_to_old hC.1.1 hj j,more⟩
  · rintro ⟨a,b,c,d,ab,cd,i,j,ac,ad,bc,bd⟩
    rcases pin_has_center u v inside i with h|h <;> rcases pin_has_center u v inside j with t|t <;> grind

/-- The exact desk step only needs earliest bad gates with two distinct unavoidable graph
edges for which the existing critical-star pin is unavailable. -/
theorem exact_of_remaining_critical_cases
    (hard : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) → TopForm.NoFourCycle G →
      ∀ C : Circuit, Eligible G C → ∀ k < C.size, (∀ j < k, ¬BadAt G C j) → BadAt G C k →
      MultipleCritical G C k → ¬AdmitsStarPin G C k →
      ∃ D : Circuit, Eligible G D ∧ D.size = C.size ∧ (∀ j < k, BadAt G D j → BadAt G C j) ∧ ¬BadAt G D k) :
    Exact1774 := by
  classical
  intro n G dec tri four useful count C min correct ready positive
  have repairs (E : Circuit) (eligible : Eligible G E) (k : Nat) (bound : k<E.size)
      (prefixOK : ∀ j<k, ¬BadAt G E j) (bad : BadAt G E k) :
      ∃ D : Circuit, Eligible G D ∧ D.size = E.size ∧ (∀ j < k, BadAt G D j → BadAt G E j) ∧ ¬BadAt G D k := by
    by_cases canPin : AdmitsStarPin G E k
    · exact repair_of_star_pin G eligible bound canPin
    by_cases multi : MultipleCritical G E k
    · exact hard n G tri four E eligible k bound prefixOK bad multi canPin
    obtain ⟨_,_,_,_,_,_,owned,_⟩ := bad
    exact repair_if_at_most_one_critical G eligible bound owned.2.1 multi
  obtain ⟨D,eligible,equal,normal⟩ := normal_of_first_repairs G repairs C ⟨min,correct,ready⟩
  refine ⟨D,eligible.1.1,eligible.2.1,equal.le,eligible.2.2,?_⟩
  change {j | BadAt G D j}.ncard < _
  have empty : {j | BadAt G D j} = ∅ := Set.eq_empty_iff_forall_notMem.mpr normal
  simpa only [empty,Set.ncard_empty] using positive

end PEqualNP.Research.GatePinning
