import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Research2583.Fano
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Point-line coordinates from the public L-meta-1983 labeling. -/
def flags : List (Fin 7 × Fin 7) := [(0,0), (0,1), (0,3), (1,0), (1,2), (1,6), (2,1), (2,5), (2,6), (3,0), (3,4), (3,5), (4,3), (4,4), (4,6), (5,2), (5,3), (5,5), (6,1), (6,2), (6,4)]
def I (p l : Fin 7) : Prop := (p,l) ∈ flags
instance : DecidableRel I := fun p l => inferInstanceAs (Decidable ((p,l) ∈ flags))

theorem plane_axioms :
    (∀ l : Fin 7, (Finset.univ.filter (fun p => I p l)).card = 3) ∧
    (∀ p p' : Fin 7, p ≠ p' → ∃! l : Fin 7, I p l ∧ I p' l) := by
  unfold ExistsUnique
  decide +kernel

/-- One three-neighbour OR and one AND per point, followed by six output ORs. -/
def stars : Circuit := ⟨[
  ⟨.or,[7,8]⟩,
  ⟨.or,[14,10]⟩,
  ⟨.and,[0,15]⟩,
  ⟨.or,[7,9]⟩,
  ⟨.or,[17,13]⟩,
  ⟨.and,[1,18]⟩,
  ⟨.or,[8,12]⟩,
  ⟨.or,[20,13]⟩,
  ⟨.and,[2,21]⟩,
  ⟨.or,[7,11]⟩,
  ⟨.or,[23,12]⟩,
  ⟨.and,[3,24]⟩,
  ⟨.or,[10,11]⟩,
  ⟨.or,[26,13]⟩,
  ⟨.and,[4,27]⟩,
  ⟨.or,[9,10]⟩,
  ⟨.or,[29,12]⟩,
  ⟨.and,[5,30]⟩,
  ⟨.or,[8,9]⟩,
  ⟨.or,[32,11]⟩,
  ⟨.and,[6,33]⟩,
  ⟨.or,[16,19]⟩,
  ⟨.or,[35,22]⟩,
  ⟨.or,[36,25]⟩,
  ⟨.or,[37,28]⟩,
  ⟨.or,[38,31]⟩,
  ⟨.or,[39,34]⟩], 40⟩
theorem stars_ao : TopForm.IsAO2 14 stars := by decide +kernel
theorem stars_size : stars.size = 27 := rfl

private def edgeTerms (x : Fin 14 → Bool) :=
  flags.any (fun e => x (Fin.castAdd 7 e.1) && x (Fin.natAdd 7 e.2))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
theorem evaluates (x : Fin 14 → Bool) : circuitFun 14 stars x = edgeTerms x := by
  have wf : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13] := rfl
  have gateForm : circuitFun 14 stars x = ((x 0 && (x 7 || x 8 || x 10)) || (x 1 && (x 7 || x 9 || x 13)) || (x 2 && (x 8 || x 12 || x 13)) || (x 3 && (x 7 || x 11 || x 12)) || (x 4 && (x 10 || x 11 || x 13)) || (x 5 && (x 9 || x 10 || x 12)) || (x 6 && (x 8 || x 9 || x 11))) := by
    change stars.eval (List.ofFn x) = _
    rw [wf]
    simp [stars,Circuit.eval,Circuit.wires,GateOp.eval,Bool.or_assoc]
  rw [gateForm]
  change _ = ((x 0 && x 7) || ((x 0 && x 8) || ((x 0 && x 10) || ((x 1 && x 7) || ((x 1 && x 9) || ((x 1 && x 13) || ((x 2 && x 8) || ((x 2 && x 12) || ((x 2 && x 13) || ((x 3 && x 7) || ((x 3 && x 11) || ((x 3 && x 12) || ((x 4 && x 10) || ((x 4 && x 11) || ((x 4 && x 13) || ((x 5 && x 9) || ((x 5 && x 10) || ((x 5 && x 12) || ((x 6 && x 8) || ((x 6 && x 9) || ((x 6 && x 11) || false)))))))))))))))))))))
  simp only [Bool.and_or_distrib_left,Bool.or_assoc,Bool.or_false]

theorem computes (x : Fin (7 + 7) → Bool) :
    circuitFun 14 stars x = decide (∃ p l : Fin 7, I p l ∧
      x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) := by
  rw [evaluates]
  apply Bool.eq_iff_iff.mpr
  simp only [edgeTerms,List.any_eq_true,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨p,l⟩,h,ha,hb⟩; exact ⟨p,l,h,ha,hb⟩
  · rintro ⟨p,l,h,ha,hb⟩; exact ⟨(p,l),h,ha,hb⟩

set_option maxRecDepth 10000 in
theorem each_flag : ∀ p l : Fin 7, I p l →
    ReadK.readsAtMost stars 14 [p.val,7 + l.val] 1 = true := by decide +kernel

end PEqualNP.Research2583.Fano
