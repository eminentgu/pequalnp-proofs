import Mathlib.Data.Finset.Basic

namespace Mono94

abbrev Sig := BitVec 16

def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b

def proper (x : Sig) : Prop := x ≠ 0 ∧ x ≠ BitVec.allOnes 16

def Live (T : Sig) : Nat → Finset Sig → Prop
  | 0, S => S = {T} ∧ proper T
  | k + 1, S => ∃ (U : Finset Sig) (a b : Sig) (d : Bool),
      S = insert a (insert b U) ∧ proper a ∧ proper b ∧ a ≠ b ∧
        bin d a b ∉ S ∧ Live T k (insert (bin d a b) U)

end Mono94
