import PinOne
import Restrictions

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2904
open Triple2836.Pinning

namespace Triple2836

def inputs (x : Assignment) : List Bool :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8]

theorem inputs_ofFn (x : Assignment) : inputs x = List.ofFn x := rfl

private def original (j : Fin 9) (x : Assignment) : List Bool :=
  inputs x ++ [false,aux j x]

private def mid (j : Fin 9) (x : Assignment) : List Bool :=
  inputs x ++ [false,x 0 || x j]

def pin (i : Fin 9) (x : Assignment) : Assignment :=
  fun k => if k = i then false else x k

private def firstLabels : List Stat :=
  [.wire 0, .wire 1, .wire 2, .wire 3, .const false, .wire 5, .wire 6,
   .wire 7, .wire 8, .const false, .wire 10]

private def lastLabels (j : Fin 9) : List Stat :=
  [.const false, .wire 1, .wire 2, .wire 3, .const false, .wire 5, .wire 6,
   .wire 7, .wire 8, .const false, .wire j.val]

private theorem firstInputs (j : Fin 9) (j4 : j ≠ 4) (x : Assignment) :
    assigned firstLabels (mid j x) = original j (pin 4 x) := by
  simp [assigned,firstLabels,mid,original,inputs,pin,aux,Stat.val,j4]

private theorem lastInputs (j : Fin 9) (j0 : j ≠ 0) (j4 : j ≠ 4) (x : Assignment) :
    assigned (lastLabels j) (inputs x) = mid j (pin 0 (pin 4 x)) := by
  simp [assigned,lastLabels,mid,pin,Stat.val,j0,j4,inputs]
  change (List.ofFn x)[j.val]'(by simpa only [List.length_ofFn] using j.isLt) = _
  exact List.getElem_ofFn _

private def constFlag : Stat → Bool
  | .const _ => true
  | .wire _ => false

def tracksCheck (l r : List Bool) (labels : List Stat) : Bool :=
  (labels.length == l.length) && (labels.length == r.length) &&
    (List.range labels.length).all fun i =>
      (l.getD i false == r.getD i false) || constFlag (labels.getD i (.const false))

theorem of_check {l r : List Bool} {labels : List Stat} (h : tracksCheck l r labels = true) :
    Tracked l r labels := by
  simp only [tracksCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro i
  by_cases hi : i < labels.length
  · have q := h.2 i (List.mem_range.mpr hi)
    simp only [Bool.or_eq_true] at q
    rcases q with a | a
    · exact Or.inl (beq_iff_eq.mp a)
    · right
      cases e : labels.getD i (.const false) with
      | const b => exact ⟨b,rfl⟩
      | wire k => rw [e] at a; contradiction
  · left
    rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]

private theorem firstTracks : ∀ j : Fin 9,
    tracksCheck (original j (row 1)) (original j (row 17)) firstLabels = true := by decide

private theorem lastTracks : ∀ j : Fin 9, j ≠ 0 → j ≠ 4 →
    tracksCheck (mid j (row (lowRow j))) (mid j (row (lowRow j ||| 1))) (lastLabels j) = true := by
  decide

private theorem firstValid : ∀ s ∈ firstLabels, s.Valid 11 := by
  simp [firstLabels,Stat.Valid]

private theorem lastValid (j : Fin 9) : ∀ s ∈ lastLabels j, s.Valid 9 := by
  simp [lastLabels,Stat.Valid]

private theorem zero_diff (j : Fin 9) (h0 : j ≠ 0) (h4 : j ≠ 4) :
    edge (pin 4 (row (lowRow j))) ≠ edge (pin 4 (row (lowRow j ||| 1))) := by
  revert j
  decide

private theorem firstVariation : edge (pin 4 (row 0)) ≠ edge (pin 4 (row 6)) := by decide
private theorem lastVariation : theta (row 0) ≠ theta (row 6) := by decide

/-- Pin 4 and then 0. Each transformation returns an ordinary project circuit
    and removes at least one non-NOT gate, including when NOT chains precede its uses. -/
theorem pin_two (j : Fin 9) (j0 : j ≠ 0) (j4 : j ≠ 4) (C : Circuit) (fan : FanInTwo C)
    (exactC : ∀ x : Assignment,
      C.eval (List.ofFn x ++ [false, x 0 || x 4 || x j]) = edge x) :
    ∃ D : Circuit, FanInTwo D ∧ cost D.gates + 2 ≤ cost C.gates ∧
      ∀ x : Assignment, D.eval (List.ofFn x) = theta x := by
  have old (x : Assignment) : C.eval (original j x) = edge x := exactC x
  have first (x : Assignment) :
      C.eval (assigned firstLabels (mid j x)) = edge (pin 4 x) := by rw [firstInputs j j4,old]
  have w₄ := coordinate_four j
  obtain ⟨D,fanD,costD,evalD⟩ := pin_circuit 11 C fan firstLabels firstValid
    (original j (row 1)) (original j (row 17)) (of_check (firstTracks j))
    (by rw [old,old,w₄.1,w₄.2.1]; decide)
    ⟨mid j (row 0),mid j (row 6),rfl,rfl,by rw [first,first]; exact firstVariation⟩
  have midD (x : Assignment) : D.eval (mid j x) = edge (pin 4 x) :=
    (evalD _ rfl).trans (first x)
  have reduced (x : Assignment) :
      D.eval (assigned (lastLabels j) (inputs x)) = theta x := by
    rw [lastInputs j j0 j4,midD]
    simp [pin,edge,theta]
  obtain ⟨E,fanE,costE,evalE⟩ := pin_circuit 9 D fanD (lastLabels j) (lastValid j)
    (mid j (row (lowRow j))) (mid j (row (lowRow j ||| 1)))
    (of_check (lastTracks j j0 j4))
    (by rw [midD,midD]; exact zero_diff j j0 j4)
    ⟨inputs (row 0),inputs (row 6),rfl,rfl,by rw [reduced,reduced]; exact lastVariation⟩
  exact ⟨E,fanE,by omega,fun x => (evalE (inputs x) rfl).trans (reduced x)⟩

private theorem cost_le_length (gs : List Gate) : cost gs ≤ gs.length :=
  List.countP_le_length

theorem has_not_cost (gs : List Gate) (h : ∃ g ∈ gs, g.op = GateOp.not) :
    cost gs + 1 ≤ gs.length := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    obtain ⟨a,ha,op⟩ := h
    rcases List.mem_cons.mp ha with rfl | tail
    · have zero : charged a = false := by simp [charged,op]
      simpa [cost,List.countP_cons,zero] using Nat.succ_le_succ (cost_le_length gs)
    · have b := ih ⟨a,tail,op⟩
      have c : cost (g::gs) ≤ cost gs + 1 := by
        cases flag : charged g <;> simp [cost,flag]
      have len : (g::gs).length = gs.length + 1 := rfl
      omega

theorem cost_spec (gs : List Gate) : cost gs =
    gs.countP (fun h => @decide (h.op ≠ GateOp.not) (Classical.propDecidable _)) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨op,pins⟩ := g
    cases op <;> simp_all [cost,charged,List.countP_cons]

/-- The charged budget and cofactor in the pinTwo premise of R-meta-2836-412. -/
theorem pin_two_13 (j : Fin 9) (j0 : j ≠ 0) (j4 : j ≠ 4) (C : Circuit) (fan : FanInTwo C)
    (bound : C.size ≤ 13) (hasNot : ∃ g ∈ C.gates, g.op = GateOp.not)
    (exactC : ∀ x : Assignment, C.eval (List.ofFn x ++ [false,x 0 || x 4 || x j]) = edge x) :
    ∃ D : Circuit, FanInTwo D ∧
      D.gates.countP (fun h => @decide (h.op ≠ GateOp.not) (Classical.propDecidable _)) ≤ 10 ∧
      ∀ x : Assignment, D.eval (List.ofFn x) = theta x := by
  obtain ⟨D,fanD,cut,result⟩ := pin_two j j0 j4 C fan exactC
  refine ⟨D,fanD,?_,result⟩
  rw [← cost_spec]
  have := has_not_cost C.gates hasNot
  change C.gates.length ≤ 13 at bound
  omega

end Triple2836
