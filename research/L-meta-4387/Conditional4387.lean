import PEqualNP.Outside.R_meta_4387_184
import CheckedPhysical

/-- The two proved premises leave precisely the physical residual. -/
theorem Packed4387.fromPhysicalResidual (residual : Packed4387.physicalResidual) :
  have x1 : List (BitVec (58 : ℕ)) := [(0 : BitVec (58 : ℕ)), BitVec.allOnes (58 : ℕ), (95229015649943559 : BitVec (58 : ℕ)), (63038587666488 : BitVec (58 : ℕ)), (256462815680 : BitVec (58 : ℕ)), (4292497062759936 : BitVec (58 : ℕ)), (8521481482240 : BitVec (58 : ℕ)), (14003410187812864 : BitVec (58 : ℕ)), (55389823207997440 : BitVec (58 : ℕ)), (189297016294081033 : BitVec (58 : ℕ)), (155696362464477250 : BitVec (58 : ℕ)), (218994303132270608 : BitVec (58 : ℕ)), (183565875465490436 : BitVec (58 : ℕ)), (229736628138025984 : BitVec (58 : ℕ)), (270286071508633728 : BitVec (58 : ℕ)), (288160007407550752 : BitVec (58 : ℕ)), (95274182876594239 : BitVec (58 : ℕ))]; ∀ (x2 : List (BitVec (58 : ℕ))),   x2.length ≤ (25 : ℕ) →     (∀ (x4 : Fin x2.length),         have x5 : List (BitVec (58 : ℕ)) := x1 ++ List.take (↑x4) x2;         ∃ x6 ∈ x5, ∃ x7 ∈ x5, x2.get x4 = x6 &&& x7 ∨ x2.get x4 = x6 ||| x7) →       (2097151 : BitVec (58 : ℕ)) ∉ x1 ++ x2 :=
  PEqualNP.Outside.R_meta_4387_184 (@PEqualNP.Research4387.normalizeChain 58) Packed4387.checkedPhysical residual

#print axioms Packed4387.fromPhysicalResidual
