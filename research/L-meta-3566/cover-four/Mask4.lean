import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Powerset

namespace VertexPeel.Mask4

abbrev Code := BitVec 21

/-- Nonempty four-bit neighborhoods in increasing mask order. -/
def columns (z : Code) : List Nat :=
  ((List.range 15).map Nat.succ).filter fun s => z.getLsbD (6 + (s-1))

def pairIndex (a b : Nat) : Nat :=
  if a = 0 then b-1 else if a = 1 then b+1 else 5

def forward (z : Code) (a b : Nat) : Bool :=
  if b < 4 then z.getLsbD (pairIndex a b) else
  if a < 4 then ((columns z).getD (b-4) 0).testBit a else false

/-- First four input vertices are the cover. The remaining vertex indices follow columns. -/
def adjB (z : Code) (u v : Nat) : Bool :=
  if u < v then forward z u v else if v < u then forward z v u else false

def graph (z : Code) : SimpleGraph (Fin (4 + (columns z).length)) where
  Adj u v := adjB z u.val v.val = true
  symm.symm := by
    intro u v h
    simp only [adjB] at h ⊢
    split at h
    · rename_i less
      simp [less,Nat.not_lt_of_ge (Nat.le_of_lt less),h]
    · rename_i ge
      split at h
      · rename_i less
        simp [less,h]
      · contradiction
  loopless.irrefl := by intro v; simp [adjB]

instance (z : Code) : DecidableRel (graph z).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ = true))

theorem columns_nodup (z : Code) : (columns z).Nodup :=
  (List.Nodup.map Nat.succ_injective (List.nodup_range)).filter _

theorem mem_columns {z : Code} {s : Nat} : s ∈ columns z ↔ 1 ≤ s ∧ s < 16 ∧ z.getLsbD (6 + (s-1)) = true := by
  simp only [columns,List.mem_filter,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨⟨k,hk,rfl⟩,bit⟩
    exact ⟨by omega,by omega,bit⟩
  · rintro ⟨lo,hi,bit⟩
    exact ⟨⟨s-1,by omega,by omega⟩,bit⟩

end VertexPeel.Mask4
