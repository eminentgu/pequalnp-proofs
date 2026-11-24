import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Research1475

/-- Fourteen binary OR gates expose all seven pairs and all seven triples. -/
def fanoPrefix : Circuit := ⟨[⟨.or,[26,38]⟩,
    ⟨.or,[29,41]⟩,
    ⟨.or,[32,23]⟩,
    ⟨.or,[35,26]⟩,
    ⟨.or,[38,29]⟩,
    ⟨.or,[41,32]⟩,
    ⟨.or,[23,35]⟩,
    ⟨.or,[42,41]⟩,
    ⟨.or,[43,23]⟩,
    ⟨.or,[44,26]⟩,
    ⟨.or,[45,29]⟩,
    ⟨.or,[46,32]⟩,
    ⟨.or,[47,35]⟩,
    ⟨.or,[48,38]⟩],55⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem prefix_exists : ∃ P : Circuit, Monotone2 P ∧ P.size ≤ 14 ∧ ∀ x : Fin 42 → Bool,
      P.wires (List.ofFn x) = (let L := fun (j : Fin 7) (d : Nat) => x (Fin.ofNat 42 (21 + (3*j.val + d) % 21))
      List.ofFn x ++ List.ofFn (fun j : Fin 7 => L j 5 || L j 17) ++
        List.ofFn (fun j : Fin 7 => (L j 5 || L j 17) || L j 20)) := by
  refine ⟨fanoPrefix, ?_, by decide, ?_⟩
  · intro g hg
    simp only [fanoPrefix,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp, by decide⟩
  · intro x
    have flat : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, x 26, x 27, x 28, x 29, x 30, x 31, x 32, x 33, x 34, x 35, x 36, x 37, x 38, x 39, x 40, x 41] := rfl
    change _ = List.ofFn x ++ [x 26 || x 38, x 29 || x 41, x 32 || x 23, x 35 || x 26, x 38 || x 29, x 41 || x 32, x 23 || x 35] ++ [(x 26 || x 38) || x 41, (x 29 || x 41) || x 23, (x 32 || x 23) || x 26, (x 35 || x 26) || x 29, (x 38 || x 29) || x 32, (x 41 || x 32) || x 35, (x 23 || x 35) || x 38]
    rw [flat]
    simp [fanoPrefix,Circuit.wires,GateOp.eval,List.any_cons]
/-- After removing the common residue 2 and dividing by three, the seven
selected points meet triples of lines with cyclic offsets 1, 5, and 6. -/
def neighbors (p : Fin 7) : Finset (Fin 7) := {p+1,p+5,p+6}

theorem triples_form_fano :
    (∀ p : Fin 7, (neighbors p).card = 3) ∧
    (∀ p q : Fin 7, p ≠ q → ((neighbors p) ∩ (neighbors q)).card = 1) ∧
    (∀ l : Fin 7, (Finset.univ.filter (fun p : Fin 7 => l ∈ neighbors p)).card = 3) := by
  decide +kernel

end PEqualNP.Research1475
