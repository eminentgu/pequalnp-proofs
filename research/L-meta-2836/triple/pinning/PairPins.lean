import PinTwo

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2904
open Triple2836.Pinning

namespace Triple2836.PairPins

inductive Arm | left | right | mirror

private def rawPin : Arm → Fin 9 | .left => 4 | _ => 0
private def hiddenPin : Arm → Fin 9 | .left => 0 | _ => 4
private def partner : Arm → Fin 9 | .left => 3 | .right => 1 | .mirror => 5

/-- The list passed to the original circuit in each of the three pair cases. -/
def bank (a : Arm) (x : Assignment) : List Bool :=
  inputs (pin (hiddenPin a) x) ++ [x 0 || x 4, x (hiddenPin a) || x (partner a)]

private theorem pin_update (v : Fin 9) (x : Assignment) :
    pin v x = Function.update x v false := by
  funext i
  by_cases eq : i = v
  · subst i; simp [pin]
  · simp [pin,eq]

theorem bank_left (x : Assignment) : bank .left x =
    List.ofFn (Function.update x 0 false) ++ [x 0 || x 4,x 0 || x 3] := by
  simp only [bank,inputs_ofFn,pin_update,hiddenPin,partner]

theorem bank_right (x : Assignment) : bank .right x =
    List.ofFn (Function.update x 4 false) ++ [x 0 || x 4,x 4 || x 1] := by
  simp only [bank,inputs_ofFn,pin_update,hiddenPin,partner]

theorem bank_mirror (x : Assignment) : bank .mirror x =
    List.ofFn (Function.update x 4 false) ++ [x 0 || x 4,x 4 || x 5] := by
  simp only [bank,inputs_ofFn,pin_update,hiddenPin,partner]

private def middle (a : Arm) (x : Assignment) : List Bool :=
  inputs (pin (hiddenPin a) x) ++ [x (hiddenPin a), x (hiddenPin a) || x (partner a)]

private def firstDiagram : Arm → List Stat
  | .left => [.wire 0,.wire 1,.wire 2,.wire 3,.const false,.wire 5,.wire 6,.wire 7,.wire 8,
    .wire 9,.wire 10]
  | _ => [.const false,.wire 1,.wire 2,.wire 3,.wire 4,.wire 5,.wire 6,.wire 7,.wire 8,
    .wire 9,.wire 10]

private def secondDiagram (a : Arm) : List Stat :=
  [.const false,.wire 1,.wire 2,.wire 3,.const false,.wire 5,.wire 6,.wire 7,.wire 8,
    .const false,.wire (partner a).val]

private theorem check_first (a : Arm) (x : Assignment) :
    assigned (firstDiagram a) (middle a x) = bank a (pin (rawPin a) x) := by
  cases a <;> simp [assigned,firstDiagram,middle,bank,rawPin,hiddenPin,partner,inputs,pin,Stat.val]

private theorem check_last (a : Arm) (x : Assignment) :
    assigned (secondDiagram a) (inputs x) = middle a (pin (hiddenPin a) (pin (rawPin a) x)) := by
  cases a <;> simp [assigned,secondDiagram,middle,rawPin,hiddenPin,partner,inputs,pin,Stat.val]

private theorem edge_last (a : Arm) (x : Assignment) :
    edge (pin (rawPin a) (pin (hiddenPin a) (pin (rawPin a) x))) = theta x := by
  cases a <;> simp [edge,theta,pin,hiddenPin,rawPin]

private theorem valid_first (a : Arm) : ∀ s ∈ firstDiagram a, s.Valid 11 := by
  cases a <;> simp [firstDiagram,Stat.Valid]

private theorem valid_last (a : Arm) : ∀ s ∈ secondDiagram a, s.Valid 9 := by
  cases a <;> simp [secondDiagram,partner,Stat.Valid]

private def firstLow : Arm → Nat | .left => 1 | _ => 16
private def lastLow : Arm → Nat | .mirror => 40 | _ => 10
private def lastHigh (a : Arm) := lastLow a ||| 2 ^ (hiddenPin a).val

private theorem first_track (a : Arm) :
    tracksCheck (bank a (row (firstLow a))) (bank a (row 17)) (firstDiagram a) = true := by
  cases a <;> decide

private theorem first_diff (a : Arm) : edge (row (firstLow a)) ≠ edge (row 17) := by
  cases a <;> decide

private theorem second_track (a : Arm) :
    tracksCheck (middle a (row (lastLow a))) (middle a (row (lastHigh a))) (secondDiagram a) =
      true := by cases a <;> decide

private theorem second_diff (a : Arm) :
    edge (pin (rawPin a) (row (lastLow a))) ≠ edge (pin (rawPin a) (row (lastHigh a))) := by
  cases a <;> decide

private theorem middle_variation (a : Arm) :
    edge (pin (rawPin a) (row 0)) ≠ edge (pin (rawPin a) (row 6)) := by cases a <;> decide

private theorem variation : theta (row 0) ≠ theta (row 6) := by decide

theorem pair_two (a : Arm) (C : Circuit) (fan : FanInTwo C)
    (exactC : ∀ x : Assignment, C.eval (bank a x) = edge x) :
    ∃ D : Circuit, FanInTwo D ∧ cost D.gates + 2 ≤ cost C.gates ∧
      ∀ x : Assignment, D.eval (List.ofFn x) = theta x := by
  have first (x : Assignment) :
      C.eval (assigned (firstDiagram a) (middle a x)) = edge (pin (rawPin a) x) := by
    rw [check_first,exactC]
  obtain ⟨D,fanD,costD,evalD⟩ := pin_circuit 11 C fan (firstDiagram a) (valid_first a)
    (bank a (row (firstLow a))) (bank a (row 17)) (of_check (first_track a))
    (by rw [exactC,exactC]; exact first_diff a)
    ⟨middle a (row 0),middle a (row 6),rfl,rfl,by rw [first,first]; exact middle_variation a⟩
  have midD (x : Assignment) : D.eval (middle a x) = edge (pin (rawPin a) x) :=
    (evalD _ rfl).trans (first x)
  have reduced (x : Assignment) :
      D.eval (assigned (secondDiagram a) (inputs x)) = theta x := by rw [check_last,midD,edge_last]
  obtain ⟨E,fanE,costE,evalE⟩ := pin_circuit 9 D fanD (secondDiagram a) (valid_last a)
    (middle a (row (lastLow a))) (middle a (row (lastHigh a)))
    (of_check (second_track a))
    (by rw [midD,midD]; exact second_diff a)
    ⟨inputs (row 0),inputs (row 6),rfl,rfl,by rw [reduced,reduced]; exact variation⟩
  exact ⟨E,fanE,by omega,fun x => (evalE (inputs x) rfl).trans (reduced x)⟩

theorem pair_two_13 (a : Arm) (C : Circuit) (fan : FanInTwo C) (bound : C.size ≤ 13)
    (hasNot : ∃ g ∈ C.gates, g.op = GateOp.not)
    (exactC : ∀ x : Assignment, C.eval (bank a x) = edge x) :
    ∃ D : Circuit, FanInTwo D ∧
      D.gates.countP (fun h => @decide (h.op ≠ GateOp.not) (Classical.propDecidable _)) ≤ 10 ∧
      ∀ x : Assignment, D.eval (List.ofFn x) = theta x := by
  obtain ⟨D,fanD,cut,result⟩ := pair_two a C fan exactC
  refine ⟨D,fanD,?_,result⟩
  rw [← cost_spec]
  have := has_not_cost C.gates hasNot
  change C.gates.length ≤ 13 at bound
  omega

end Triple2836.PairPins
