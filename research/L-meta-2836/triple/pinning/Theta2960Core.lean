import CheckedPinTwoCtor
import Mathlib.Data.Fin.VecNotation
import PEqualNP.Defs.MetaComplexityMinimal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2904
open Triple2836.Pinning

namespace Triple2836

/-- Old raw vertices 0 and 4 become false; the others are renumbered 0 through 6. -/
private def sevenLabels : List Stat :=
  [.const false,.wire 0,.wire 1,.wire 2,.const false,.wire 3,.wire 4,.wire 5,.wire 6]

private def padSeven (x : Fin 7 → Bool) : Assignment :=
  ![false,x 0,x 1,x 2,false,x 3,x 4,x 5,x 6]

private def seven (x : Fin 7 → Bool) : Bool :=
  ([(0,1),(1,2),(0,4),(1,5),(2,6),(3,5),(4,6),(6,3)] : List (Fin 7 × Fin 7)).any
    fun e => x e.1 && x e.2

private theorem inputsSeven (x : Fin 7 → Bool) :
    assigned sevenLabels (List.ofFn x) = List.ofFn (padSeven x) := rfl

private theorem seven_agrees (x : Fin 7 → Bool) : theta (padSeven x) = seven x := by
  change (x 0 && x 1 || x 1 && x 2 || x 0 && x 4 || x 1 && x 5 ||
    x 2 && x 6 || x 3 && x 5 || x 4 && x 6 || x 6 && x 3) =
    (x 0 && x 1 || (x 1 && x 2 || (x 0 && x 4 || (x 1 && x 5 ||
    (x 2 && x 6 || (x 3 && x 5 || (x 4 && x 6 || (x 6 && x 3 || false))))))))
  simp only [Bool.or_assoc, Bool.or_false]

private theorem seven_varies : ∃ x y : Fin 7 → Bool, seven x ≠ seven y := by
  exact ⟨fun _ => false, fun i => decide (i.val ≤ 1), by decide⟩

/-- The upstream constant propagator produces a real seven-input circuit.
    Its AND/OR count is bounded even if the source uses arbitrarily many NOTs. -/
theorem strip_theta_dummies (D : Circuit) (fan : FanInTwo D)
    (computes : ∀ x : Assignment, D.eval (List.ofFn x) = theta x) :
    ∃ E : Circuit, FanInTwo E ∧ cost E.gates ≤ cost D.gates ∧ circuitFun 7 E = seven := by
  let a : List Stat × List Gate := (sevenLabels,[])
  let out := elim 7 D.gates a
  have valid : ∀ s ∈ sevenLabels, s.Valid 7 := by simp [sevenLabels,Stat.Valid]
  have semantics (x : Fin 7 → Bool) :
      (out.1.getD D.output (.const false)).val (wiresFrom out.2 (List.ofFn x)) = seven x := by
    have rep := ((inv_elim 7 (List.ofFn x) (by simp) D.gates
      (assigned sevenLabels (List.ofFn x)) a fan
      (assigned_inv 7 sevenLabels (List.ofFn x) (by simp) valid)).2 D.output).2
    change (out.1.getD D.output (.const false)).val (wiresFrom out.2 (List.ofFn x)) =
      D.eval (assigned sevenLabels (List.ofFn x)) at rep
    rw [inputsSeven, computes, seven_agrees] at rep
    exact rep
  cases label : out.1.getD D.output (.const false) with
  | const b =>
    obtain ⟨x,y,diff⟩ := seven_varies
    have ex := semantics x
    have ey := semantics y
    rw [label] at ex ey
    exact (diff (ex.symm.trans ey)).elim
  | wire j =>
    refine ⟨⟨out.2,j⟩,elim_ok 7 D.gates a (by simp [a]),?_,?_⟩
    · simpa [out,a,cost] using elim_cost 7 D.gates a
    · funext x
      have h := semantics x
      rw [label] at h
      exact h

/-- Apply the exact seven-vertex lower bound, expressed as upstream prints it.
    This separate declaration permits checking the transport independently of
    the evaluation cost of the already-published exhaustive proof. -/
theorem theta_of_2960 (lower : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x1 = fun (x3 : Fin (7 : ℕ) → Bool) => [((0 : Fin (7 : ℕ)), (1 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (2 : Fin (7 : ℕ))), ((0 : Fin (7 : ℕ)), (4 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((2 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((3 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((4 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((6 : Fin (7 : ℕ)), (3 : Fin (7 : ℕ)))].any fun (x4 : Fin (7 : ℕ) × Fin (7 : ℕ)) => x3 x4.1 && x3 x4.2) → (11 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (_x5 : ℕ) => Bool.true) Bool.true x4.op) x1.gates) :
    let f := fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 e))
      let q := fun x : Fin 9 → Bool => f (Function.update (Function.update x 0 false) 4 false)
      ∀ D : Circuit, FanInTwo D ∧ D.gates.countP (fun h => h.op.ctorIdx != GateOp.not.ctorIdx) ≤ 10 ∧ (∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = q x) → False := by
  intro f q D ⟨fan,limit,computes⟩
  have graphEq (x : Fin 9 → Bool) : f x = edge x := by
    change (x 0 && x 1 || (x 1 && x 2 || (x 2 && x 3 || (x 3 && x 4 || (x 4 && x 0 || (x 0 && x 5 || (x 1 && x 6 || (x 2 && x 7 || (x 3 && x 8 || (x 5 && x 7 || (x 6 && x 8 || (x 8 && x 5 || false)))))))))))) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
    simp only [Bool.or_assoc, Bool.or_false]
  have thetaEq (x : Assignment) : q x = theta x := by
    change f (Function.update (Function.update x 0 false) 4 false) = _
    rw [graphEq]
    simp [edge,theta,Function.update]
  obtain ⟨E,efan,ecost,ef⟩ := strip_theta_dummies D fan (fun x => (computes x).trans (thetaEq x))
  have count_eq : (fun g : Gate => GateOp.rec (motive := fun _ => Bool)
      true true false (fun _ => true) true g.op) = charged := by
    funext g
    obtain ⟨op,pins⟩ := g
    cases op <;> rfl
  have above := lower E efan ef
  rw [count_eq] at above
  change 11 ≤ cost E.gates at above
  rw [← cost_ctorIdx] at limit
  omega

end Triple2836
