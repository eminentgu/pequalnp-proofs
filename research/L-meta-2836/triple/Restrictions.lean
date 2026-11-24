import Std

namespace Triple2836

abbrev Assignment := Fin 9 → Bool

def edge (x : Assignment) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
  x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def theta (x : Assignment) : Bool :=
  x 1 && x 2 || x 2 && x 3 || x 1 && x 6 || x 2 && x 7 ||
  x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def aux (j : Fin 9) (x : Assignment) : Bool := x 0 || x 4 || x j

theorem reduce_edge (x : Assignment) (h4 : x 4 = false) (h0 : x 0 = false) :
    edge x = theta x := by simp [edge, theta, h4, h0]

theorem reduce_aux (j : Fin 9) (x : Assignment) (h4 : x 4 = false) (h0 : x 0 = false) :
    aux j x = x j := by simp [aux, h4, h0]

def row (m : Nat) : Assignment := fun i => m.testBit i.val

/-- The graph outputs differ, although the auxiliary wire and every other raw wire agree. -/
def Witness (j i : Fin 9) (low high : Nat) : Prop :=
  edge (row low) = false ∧ edge (row high) = true ∧
  aux j (row low) = aux j (row high) ∧
  ∀ k : Fin 9, k ≠ i → row low k = row high k

instance (j i : Fin 9) (low high : Nat) : Decidable (Witness j i low high) := by
  unfold Witness
  infer_instance

theorem coordinate_four : ∀ j : Fin 9, Witness j 4 1 17 := by decide

def neighbor (j : Fin 9) : Nat := if j.val = 2 ∨ j.val = 6 then 5 else 1

def lowRow (j : Fin 9) : Nat := 2 ^ j.val ||| 2 ^ neighbor j

theorem coordinate_zero_after_four : ∀ j : Fin 9, j ≠ 0 → j ≠ 4 →
    Witness j 0 (lowRow j) (lowRow j ||| 1) ∧
    row (lowRow j) 4 = false ∧ row (lowRow j ||| 1) 4 = false := by decide

end Triple2836
