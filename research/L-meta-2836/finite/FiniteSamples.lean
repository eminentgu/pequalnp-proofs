import PEqualNP.Defs.MetaComplexity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.ByContra

/-! Finite tests for the three two-OR and seven three-input-OR encodings of L-meta-2836. -/
namespace PEqualNP.Research2836.FiniteSamples

open CircuitLowerBounds MetaComplexity

abbrev Row := Fin 512
abbrev Branch := Fin 10

def bits (x : Row) (i : Fin 9) : Bool := x.val.testBit i.val

def edge (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
  x 6 && x 8 || x 8 && x 5

def thirdVertex (b : Branch) : Fin 9 := ![0, 0, 0, 1, 2, 3, 5, 6, 7, 8] b

def encode (b : Branch) (x : Fin 9 → Bool) : List Bool :=
  match b.val with
  | 0 => List.ofFn (Function.update x 0 false) ++ [x 0 || x 4, x 0 || x 3]
  | 1 => List.ofFn (Function.update x 4 false) ++ [x 0 || x 4, x 4 || x 1]
  | 2 => List.ofFn (Function.update x 4 false) ++ [x 0 || x 4, x 4 || x 5]
  | _ => List.ofFn x ++ [false, x 0 || x 4 || x (thirdVertex b)]

@[simp] theorem length_encode (b : Branch) (x : Fin 9 → Bool) :
    (encode b x).length = 11 := by unfold encode; split <;> simp

def required (b : Branch) (i : Fin 11) : Bool :=
  if b.val = 0 then i != 0 else if b.val < 3 then i != 4 else decide (i.val < 9)

def edgeRows : List Row := [3, 6, 12, 24, 17, 33, 66, 132, 264, 160, 320, 288]
def maximalIndependentRows : List Row := [42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402]
def smallPositive : List Row := [3, 6, 7, 11, 12, 13, 14, 17, 19, 21, 22, 24, 25, 26, 28, 33, 35, 37, 38, 41, 44, 49, 56, 66, 67, 70, 74, 76, 81, 82, 88, 97, 98, 131, 132, 133, 134, 140, 145, 148, 152, 160, 161, 162, 164, 168, 176, 194, 196, 224, 259, 262, 264, 265, 266, 268, 273, 280, 288, 289, 290, 292, 296, 304, 320, 321, 322, 324, 328, 336, 352, 388, 392, 416, 448]
def independentRows : List Row := [0, 1, 2, 4, 5, 8, 9, 10, 16, 18, 20, 32, 34, 36, 40, 42, 48, 50, 52, 64, 65, 68, 69, 72, 73, 80, 84, 96, 100, 104, 112, 116, 128, 129, 130, 136, 137, 138, 144, 146, 192, 193, 200, 201, 208, 256, 257, 258, 260, 261, 272, 274, 276, 384, 385, 386, 400, 402]
private def witnessTable : Array (Array (Row × Row)) := #[
  #[(0, 0), (3, 1), (6, 2), (13, 5), (17, 1), (33, 1), (66, 2), (132, 4), (264, 8), (11, 10), (17, 16)],
  #[(3, 18), (22, 20), (6, 2), (12, 4), (0, 0), (33, 1), (66, 2), (132, 4), (264, 8), (26, 10), (17, 1)],
  #[(17, 16), (3, 1), (6, 2), (12, 4), (0, 0), (176, 144), (66, 2), (132, 4), (264, 8), (56, 40), (17, 1)],
  #[(3, 2), (3, 1), (6, 2), (12, 4), (17, 1), (33, 1), (66, 2), (132, 4), (264, 8), (0, 0), (0, 0)],
  #[(17, 16), (3, 1), (13, 9), (12, 4), (17, 1), (33, 1), (66, 2), (132, 4), (264, 8), (0, 0), (0, 0)],
  #[(11, 10), (3, 1), (6, 2), (13, 5), (17, 1), (33, 1), (66, 2), (132, 4), (264, 8), (0, 0), (0, 0)],
  #[(17, 16), (3, 1), (6, 2), (12, 4), (17, 1), (33, 1), (66, 2), (132, 4), (264, 8), (0, 0), (0, 0)],
  #[(17, 16), (3, 1), (6, 2), (12, 4), (17, 1), (33, 1), (82, 18), (132, 4), (264, 8), (0, 0), (0, 0)],
  #[(17, 16), (3, 1), (6, 2), (12, 4), (17, 1), (33, 1), (66, 2), (133, 5), (264, 8), (0, 0), (0, 0)],
  #[(17, 16), (3, 1), (6, 2), (12, 4), (17, 1), (33, 1), (66, 2), (132, 4), (265, 9), (0, 0), (0, 0)]]

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem sample_sizes : smallPositive.length = 75 ∧ independentRows.length = 58 ∧
    smallPositive.Nodup ∧ independentRows.Nodup := by decide +kernel

theorem samples_exact (x : Row) :
    (x ∈ smallPositive ↔ edge (bits x) = true ∧
      ((List.finRange 9).filter (bits x)).length ≤ 3) ∧
    (x ∈ independentRows ↔ edge (bits x) = false) := by
  revert x; decide +kernel

def subsetRow (x y : Row) : Bool := x.val &&& y.val == x.val

private theorem bounds_by_extrema (x : Row) :
    (edge (bits x) = true → edgeRows.any (fun p => subsetRow p x) = true) ∧
    (edge (bits x) = false → maximalIndependentRows.any (fun n => subsetRow x n) = true) := by
  revert x; decide +kernel

/-- For monotone responses, agreement on the 24 extreme masks determines the whole function. -/
theorem extrema_suffice (respond : Row → Bool)
    (mono : ∀ x y, subsetRow x y = true → respond x = true → respond y = true)
    (onPos : ∀ p ∈ edgeRows, respond p = true)
    (onNeg : ∀ n ∈ maximalIndependentRows, respond n = false) :
    ∀ x, respond x = edge (bits x) := by
  intro x
  cases h : edge (bits x) with
  | true =>
    obtain ⟨p, hp, le⟩ := List.any_eq_true.mp ((bounds_by_extrema x).1 h)
    exact mono p x le (onPos p hp)
  | false =>
    cases e : respond x with
    | false => rfl
    | true =>
      obtain ⟨n, hn, le⟩ := List.any_eq_true.mp ((bounds_by_extrema x).2 h)
      have yes := mono x n le e
      simp [onNeg n hn] at yes

def testPair (b : Branch) (i : Fin 11) : Row × Row := (witnessTable[b.val]!)[i.val]!

theorem private_pair (b : Branch) (i : Fin 11) (h : required b i = true) :
    let p := (testPair b i).1
    let n := (testPair b i).2
    p ∈ smallPositive ∧ n ∈ independentRows ∧
      (encode b (bits p)).getD i false ≠ (encode b (bits n)).getD i false ∧
      ∀ j : Fin 11, j ≠ i →
        (encode b (bits p)).getD j false = (encode b (bits n)).getD j false := by
  revert h i b; decide +kernel

/-- A gate list which never reads address i preserves equality elsewhere. -/
private theorem no_read (gs : List Gate) (i : Nat) (u v : List Bool)
    (never : ∀ g ∈ gs, i ∉ g.inputs) (len : u.length = v.length)
    (agree : ∀ j ≠ i, u.getD j false = v.getD j false) :
    ∀ j ≠ i, (Circuit.wires ⟨gs, 0⟩ u).getD j false = (Circuit.wires ⟨gs, 0⟩ v).getD j false := by
  induction gs generalizing u v with
  | nil => exact agree
  | cons g gs ih =>
    let run (w : List Bool) := g.op.eval (g.inputs.map fun j => w.getD j false)
    have value : run u = run v := by
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro j hj
      apply agree
      exact fun eq => never g (by simp) (eq ▸ hj)
    apply ih (u ++ [run u]) (v ++ [run v]) (fun g hg => never g (by simp [hg]))
    · simp [len]
    · intro j hj
      by_cases hlt : j < u.length
      · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (len ▸ hlt)]
        exact agree j hj
      · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
        rw [len, value]

def Passes (b : Branch) (C : Circuit) : Prop :=
  (∀ p ∈ smallPositive, C.eval (encode b (bits p)) = true) ∧
  (∀ n ∈ independentRows, C.eval (encode b (bits n)) = false)

theorem passes_of_correct (b : Branch) (C : Circuit)
    (ok : ∀ x : Fin 9 → Bool, C.eval (encode b x) = edge x) : Passes b C := by
  constructor
  · intro p hp
    exact (ok (bits p)).trans (((samples_exact p).1.mp hp).1)
  · intro n hn
    exact (ok (bits n)).trans ((samples_exact n).2.mp hn)

/-- Every required input must be the output or be read by a gate, for arbitrary gate operations. -/
theorem uses_required_address (b : Branch) (C : Circuit) (ok : Passes b C)
    (i : Fin 11) (hi : required b i = true) :
    C.output = i.val ∨ ∃ g ∈ C.gates, i.val ∈ g.inputs := by
  obtain ⟨hp, hn, _, outside⟩ := private_pair b i hi
  let p := (testPair b i).1
  let n := (testPair b i).2
  by_contra! absent
  have agree (j : Nat) (hj : j ≠ i.val) :
      (encode b (bits p)).getD j false = (encode b (bits n)).getD j false := by
    by_cases bound : j < 11
    · exact outside ⟨j, bound⟩ (fun eq => hj (congrArg Fin.val eq))
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  have eq := no_read C.gates i.val _ _ absent.2 (by simp) agree C.output absent.1
  change C.eval (encode b (bits p)) = C.eval (encode b (bits n)) at eq
  rw [ok.1 p hp, ok.2 n hn] at eq
  contradiction

private theorem input_wire (gs : List Gate) (x : List Bool) (j : Nat) (hj : j < x.length) :
    (Circuit.wires ⟨gs, 0⟩ x).getD j false = x.getD j false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => x.getD i false)
    change (Circuit.wires ⟨gs, 0⟩ (x ++ [v])).getD j false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hj]

private theorem misses_positive (b : Branch) (j : Fin 11) :
    smallPositive.any (fun x => !(encode b (bits x)).getD j false) = true := by
  revert b j; decide +kernel

theorem output_is_internal (b : Branch) (C : Circuit) (ok : Passes b C) : 11 ≤ C.output := by
  by_contra! low
  obtain ⟨p, hp, bit⟩ := List.any_eq_true.mp (misses_positive b ⟨C.output, low⟩)
  have h := input_wire C.gates (encode b (bits p)) C.output (by simpa)
  change C.eval (encode b (bits p)) = _ at h
  rw [ok.1 p hp] at h
  simp at bit
  change (encode b (bits p)).getD C.output false = false at bit
  cases h.trans bit

/-- A circuit correct on the 133 samples reads every required input in some gate. -/
theorem gate_reads_required (b : Branch) (C : Circuit) (ok : Passes b C)
    (i : Fin 11) (hi : required b i = true) :
    ∃ g ∈ C.gates, i.val ∈ g.inputs := by
  rcases uses_required_address b C ok i hi with out | used
  · have bound := output_is_internal b C ok
    have small := i.isLt
    omega
  · exact used

private def twoORCounter : Circuit :=
  ⟨[⟨.or,[1,3]⟩, ⟨.or,[5,7]⟩, ⟨.and,[11,12]⟩, ⟨.or,[2,7]⟩,
    ⟨.and,[9,14]⟩, ⟨.or,[13,15]⟩, ⟨.not,[16]⟩], 17⟩

private def tripleORCounter : Circuit :=
  ⟨[⟨.or,[0,4]⟩, ⟨.or,[1,3]⟩, ⟨.or,[5,7]⟩, ⟨.and,[12,13]⟩,
    ⟨.or,[2,7]⟩, ⟨.and,[11,15]⟩, ⟨.or,[14,16]⟩, ⟨.not,[17]⟩], 18⟩

def counter (b : Branch) : Circuit := if b.val < 3 then twoORCounter else tripleORCounter

theorem counter_fanin (b : Branch) : FanInTwo (counter b) := by
  unfold counter
  split <;> intro g hg
  · simp [twoORCounter] at hg
    rcases hg with h | h | h | h | h | h | h <;> subst g <;> simp
  · simp [tripleORCounter] at hg
    rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp

private def isNot : Gate → Bool
  | ⟨.not, _⟩ => true
  | _ => false

theorem counter_has_one_not (b : Branch) : ((counter b).gates.filter isNot).length = 1 := by
  unfold counter; split <;> rfl

theorem counter_size (b : Branch) : (counter b).size = (if b.val < 3 then 7 else 8) := by
  unfold counter; split <;> rfl

theorem misleading_extrema (b : Branch) :
    edgeRows.all (fun x => (counter b).eval (encode b (bits x)) == edge (bits x)) = true ∧
    maximalIndependentRows.all (fun x => (counter b).eval (encode b (bits x)) == edge (bits x)) = true ∧
    (counter b).eval (encode b (bits 0)) ≠ edge (bits 0) := by
  revert b; decide +kernel

end PEqualNP.Research2836.FiniteSamples
