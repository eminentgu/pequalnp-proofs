import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.BlindGate

namespace Fano4873

private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step]; omega

theorem extend : ∀ (C : Circuit) (u v : ℕ) (op : GateOp), IsAO2 14 C →
    (∀ g ∈ C.gates, g.inputs.Nodup) → (op = .or ∨ op = .and) →
    u < 14+C.size → v < 14+C.size → u ≠ v →
    ∃ D : Circuit, D.size = C.size+1 ∧ IsAO2 14 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
      D.output = 14+C.size ∧ D.gates[C.size]? = some ⟨op,[u,v]⟩ ∧
      ∀ x : Fin 14 → Bool,
        (∀ i < 14+C.size, wireValue D 14 x i = wireValue C 14 x i) ∧
        wireValue D 14 x D.output = op.eval [wireValue C 14 x u,wireValue C 14 x v] := by
  intro C u v op ao nd hop hu hv ne
  let G : Gate := ⟨op,[u,v]⟩
  let D : Circuit := ⟨C.gates ++ [G],14+C.size⟩
  have sz : D.size = C.size+1 := by simp [D,Circuit.size,G]
  have nd' : ∀ t ∈ D.gates, t.inputs.Nodup := by
    intro t ht
    rcases List.mem_append.mp ht with old | new
    · exact nd t old
    · have : t = G := List.mem_singleton.mp new
      simp [this,G,ne]
  refine ⟨D,sz,⟨?_,?_,?_⟩,nd',rfl,?_,?_⟩
  · intro t ht
    rcases List.mem_append.mp ht with old | new
    · exact ao.1 t old
    · have : t = G := List.mem_singleton.mp new
      simpa [this,G,or_comm] using hop.symm
  · intro j hj i hi
    change j < (C.gates ++ [G]).length at hj
    change i ∈ ((C.gates ++ [G]).getD j _).inputs at hi
    by_cases old : j < C.gates.length
    · rw [List.getD_append _ _ _ _ old] at hi
      exact ao.2.1 j old i hi
    · have e : j = C.gates.length := by simp at hj; omega
      subst j
      rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
      simp [G] at hi
      rcases hi with rfl | rfl <;> assumption
  · intro t ht
    rcases List.mem_append.mp ht with old | new
    · exact ao.2.2 t old
    · have : t = G := List.mem_singleton.mp new
      simp [this,G]
  · simp [D,Circuit.size,G]
  · intro x
    let W := C.wires (List.ofFn x)
    have lengthW : W.length = 14+C.size := by
      change (C.gates.foldl step (List.ofFn x)).length = _
      simp [len,Circuit.size]
    have wires : D.wires (List.ofFn x) = W ++ [op.eval [W.getD u false,W.getD v false]] := by
      simp [D,W,G,Circuit.wires,List.foldl_append]
    constructor
    · intro i hi
      unfold PEqualNP.BlindGate.wireValue
      rw [wires,List.getD_append _ _ _ _ (by omega)]
    · change (D.wires _).getD (14+C.size) false = _
      rw [wires, ← lengthW,List.getD_append_right _ _ _ _ (le_refl _)]
      simp [W,PEqualNP.BlindGate.wireValue]

end Fano4873
