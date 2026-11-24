import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 6000 in
set_option maxHeartbeats 800000 in
theorem PEqualNP.Research4387.terminalCut
    (compress : ∀ (base xs : List (BitVec 58)) (t : BitVec 58),
    let start := (0 : BitVec 58) :: BitVec.allOnes 58 :: base
    (∀ (j : Fin xs.length), let pool := start ++ xs.take j
        ∃ a ∈ pool, ∃ b ∈ pool, xs.get j = a &&& b ∨ xs.get j = a ||| b) → t ∈ start ++ xs → t ≠ 0 → t ≠ BitVec.allOnes 58 → t ∉ base →
    ∃ ys : List (BitVec 58), ys.length ≤ xs.length ∧ ys.getLast? = some t ∧
      (∀ j : Fin ys.length, let pool := base ++ ys.take j
        ys.get j ∉ pool ∧ ys.get j ≠ 0 ∧ ys.get j ≠ BitVec.allOnes 58 ∧
          ∃ a ∈ pool, ∃ b ∈ pool, ys.get j = a &&& b ∨ ys.get j = a ||| b))
    (andCase : let base : List (BitVec 58) := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752, 95274182876594239]
    ∀ ys : List (BitVec 58), ys.length ≤ 24 →
      (∀ j : Fin ys.length, let pool := base ++ ys.take j
        ys.get j ∉ pool ∧ ys.get j ≠ 0 ∧ ys.get j ≠ BitVec.allOnes 58 ∧
          ∃ a ∈ pool, ∃ b ∈ pool, ys.get j = a &&& b ∨ ys.get j = a ||| b) →
      (2097151 : BitVec 58) ∉ ys →
      ∀ a ∈ ys, ∀ b ∈ ys, a &&& b ≠ (2097151 : BitVec 58))
    (orCase : let base : List (BitVec 58) := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752, 95274182876594239]
    ∀ ys : List (BitVec 58), ys.length ≤ 24 →
      (∀ j : Fin ys.length, let pool := base ++ ys.take j
        ys.get j ∉ pool ∧ ys.get j ≠ 0 ∧ ys.get j ≠ BitVec.allOnes 58 ∧
          ∃ a ∈ pool, ∃ b ∈ pool, ys.get j = a &&& b ∨ ys.get j = a ||| b) →
      (2097151 : BitVec 58) ∉ ys →
      ∀ a ∈ ys, ∀ b ∈ ys, a ||| b ≠ (2097151 : BitVec 58)) :
    have x1 : List (BitVec (58 : ℕ)) := [(0 : BitVec (58 : ℕ)), BitVec.allOnes (58 : ℕ), (95229015649943559 : BitVec (58 : ℕ)), (63038587666488 : BitVec (58 : ℕ)), (256462815680 : BitVec (58 : ℕ)), (4292497062759936 : BitVec (58 : ℕ)), (8521481482240 : BitVec (58 : ℕ)), (14003410187812864 : BitVec (58 : ℕ)), (55389823207997440 : BitVec (58 : ℕ)), (189297016294081033 : BitVec (58 : ℕ)), (155696362464477250 : BitVec (58 : ℕ)), (218994303132270608 : BitVec (58 : ℕ)), (183565875465490436 : BitVec (58 : ℕ)), (229736628138025984 : BitVec (58 : ℕ)), (270286071508633728 : BitVec (58 : ℕ)), (288160007407550752 : BitVec (58 : ℕ)), (95274182876594239 : BitVec (58 : ℕ))]; ∀ (x2 : List (BitVec (58 : ℕ))),   x2.length ≤ (25 : ℕ) →     (∀ (x4 : Fin x2.length),         have x5 : List (BitVec (58 : ℕ)) := x1 ++ List.take (↑x4) x2;         ∃ x6 ∈ x5, ∃ x7 ∈ x5, x2.get x4 = x6 &&& x7 ∨ x2.get x4 = x6 ||| x7) →       (2097151 : BitVec (58 : ℕ)) ∉ x1 ++ x2 := by
  let base : List (BitVec 58) := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752, 95274182876594239]
  let t : BitVec 58 := 2097151
  have n0 : t ≠ 0 := by decide
  have n1 : t ≠ BitVec.allOnes 58 := by decide
  have ns : t ∉ base := by decide
  have checked : base.all (fun a => decide (a &&& t ≠ t ∧ a ||| t ≠ t)) = true := by decide
  have masks : ∀ a ∈ base, a &&& t ≠ t ∧ a ||| t ≠ t := fun a h =>
    of_decide_eq_true (List.all_eq_true.mp checked a h)
  have produced (a b : BitVec 58) (edge : a &&& b = t ∨ a ||| b = t) : a ∉ base ∧ b ∉ base := by
    rcases edge with e | e
    · have left : a &&& t = t := by rw [← e, ← BitVec.and_assoc, BitVec.and_self]
      have right : b &&& t = t := by rw [← e, BitVec.and_comm a b, ← BitVec.and_assoc, BitVec.and_self]
      exact ⟨fun ha => (masks _ ha).1 left, fun hb => (masks _ hb).1 right⟩
    · have left : a ||| t = t := by rw [← e, ← BitVec.or_assoc, BitVec.or_self]
      have right : b ||| t = t := by rw [← e, BitVec.or_comm a b, ← BitVec.or_assoc, BitVec.or_self]
      exact ⟨fun ha => (masks _ ha).2 left, fun hb => (masks _ hb).2 right⟩
  dsimp only
  intro xs budget legal hit
  obtain ⟨ys, len, last, clean⟩ := compress base xs t legal hit n0 n1 ns
  obtain ⟨pre, rfl⟩ : ∃ pre : List (BitVec 58), ys = pre ++ [t] := by
    induction ys using List.reverseRecOn with
    | nil => simp at last
    | append_singleton pre v _ =>
      have hv : v = t := by simpa using last
      exact ⟨pre, by rw [hv]⟩
  have length : pre.length ≤ 24 := by simp at len; omega
  have preLegal : ∀ j : Fin pre.length, let pool := base ++ pre.take j
        pre.get j ∉ pool ∧ pre.get j ≠ 0 ∧ pre.get j ≠ BitVec.allOnes 58 ∧
          ∃ a ∈ pool, ∃ b ∈ pool, pre.get j = a &&& b ∨ pre.get j = a ||| b := by
    intro j
    have hj := j.isLt
    have h := clean ⟨j.val, by simp⟩
    simpa only [List.get_eq_getElem, List.getElem_append_left hj, List.take_append_of_le_length hj.le] using h
  have final := clean ⟨pre.length, by simp⟩
  simp only [List.take_left, List.get_eq_getElem, List.getElem_concat_length] at final
  obtain ⟨fresh,_,_,a,ha,b,hb,operation⟩ := final
  have op : a &&& b = t ∨ a ||| b = t := operation.imp Eq.symm Eq.symm
  have outside := produced a b op
  have ha' := (List.mem_append.mp ha).resolve_left outside.1
  have hb' := (List.mem_append.mp hb).resolve_left outside.2
  have nt : t ∉ pre := fun h => fresh (List.mem_append_right _ h)
  rcases op with e | e
  · exact (andCase pre length preLegal nt a ha' b hb') e
  · exact (orCase pre length preLegal nt a ha' b hb') e
