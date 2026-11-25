import RawTrimData
import MonoMask

namespace VertexPeel.Mask4
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.CoverPromise

open TrimData

set_option maxRecDepth 50000
set_option maxHeartbeats 0

private theorem cheap (k : Nat) : Loc.tau (graph (supers.getD k (0,0)).1) ≤ 3 := by
  have mem : supers.getD k (0,0) ∈ supers := by
    by_cases small : k < supers.length
    · rw [List.getD_eq_getElem _ _ small]
      exact List.getElem_mem small
    · rw [List.getD_eq_default _ _ (by omega : supers.length ≤ k)]
      decide +kernel
  have v := of_decide_eq_true (List.all_eq_true.mp checked _ mem)
  exact (Loc.tau_le _ _ v.2).trans v.1

private theorem kept (z : Code) (size : Loc.tau (graph z) = 4) (xs : List Code) (flags : List Nat)
    (mem : z ∈ xs) : z ∈ trim xs flags := by
  induction xs generalizing flags with
  | nil => simp at mem
  | cons a xs ih =>
    cases flags with
    | nil => exact mem
    | cons k ks =>
      simp only [trim]
      split
      · rename_i h
        rcases List.mem_cons.mp mem with rfl|hmem
        · have le := (tau_mono h.2).trans (cheap k)
          omega
        · exact ih ks hmem
      · exact (List.mem_cons.mp mem).elim (fun eq => List.mem_cons.mpr (Or.inl eq))
          (fun h => List.mem_cons.mpr (Or.inr (ih ks h)))

theorem minimum_four_codes {z : Code} (hz : z ∈ raw8144) (size : Loc.tau (graph z) = 4) :
    z ∈ raw4704 := replay ▸ kept z size raw8144 refs hz

#print axioms minimum_four_codes
end VertexPeel.Mask4
