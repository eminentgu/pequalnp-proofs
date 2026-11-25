import Checker
import Packing

namespace Mono94.Case94

def Dead (bound key : Nat) : Prop :=
  ∀ t, t ≤ bound → ¬ Live 511 t (Packing.unpack 12 key).toFinset

def DeadList (bound : Nat) (keys : List Nat) : Prop := ∀ q ∈ keys, Dead bound q

theorem nilDead {k : Nat} : DeadList k [] := by
  intro q h
  cases h

theorem consDead {k q : Nat} {qs : List Nat} (h : Dead k q) (hs : DeadList k qs) :
    DeadList k (q::qs) := by
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hrest
  · exact h
  · exact hs w hrest

theorem stepNode (k key : Nat) (children : List Nat)
    (nd : (Packing.unpack 12 key).Nodup)
    (valid : checkNode (k+1) (Packing.unpack 12 key) (Packing.covered 12 id children) = true)
    (certified : DeadList k children) : Dead (k+1) key := by
  apply checkNode_sound (k+1) (Packing.unpack 12 key) (Packing.covered 12 id children) nd valid
  intro xs _ hit j small
  obtain ⟨q,hq,eq⟩ := Packing.covered_sound hit
  change (Packing.unpack 12 q).toFinset = xs.toFinset at eq
  rw [← eq]
  exact certified q hq j (by omega)

end Mono94.Case94
