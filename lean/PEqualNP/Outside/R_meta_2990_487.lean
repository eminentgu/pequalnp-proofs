import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2990_487
  (count : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hq : 2 ≤ q)
    (lines : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1)
    (unique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (mono : PEqualNP.MetaComplexity.Monotone2 C)
    (ordered : ∀ j g, C.gates[j]? = some g →
      ∃ a b, g.inputs=[a,b] ∧ a<b ∧ b<N+N+j)
    (sound : ∀ z : Fin (N+N) → Bool,
      Fintype.card {l : Fin N // z (Fin.natAdd N l)=true} ≤ q →
      (¬∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p)=true ∧ z (Fin.natAdd N l)=true) →
      PEqualNP.MetaComplexity.circuitFun (N+N) C z=false),
    N*(q+1) ≤ 50*C.size + 2*N + (Finset.univ.filter fun e : Fin N × Fin N => I e.1 e.2 ∧ PEqualNP.ReadK.readsAtMost C (N+N) [e.1.val,N+e.2.val] 2 = false).card)
  (dense : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 + x5.size → (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) → (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) → (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) → 99*(x2*(x1+1)) < 200*(Finset.univ.filter fun e : Fin x2 × Fin x2 => x3 e.1 e.2 ∧ PEqualNP.ReadK.readsAtMost x5 (x2+x2) [e.1.val,x2+e.2.val] 2 = false).card → x2 * x1 ≤ (100 : ℕ) * x5.size) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 + x5.size → (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) → (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) → (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q N I inst C hq hn hl hu hm ho hw hp hs
  by_contra! small
  have bound := count q N I C (by omega) hl hu hm hw hs
  have mul := Nat.mul_le_mul_left N hq
  apply (Nat.not_le.mpr small) (dense q N I C hq hn hl hu hm ho hw hp hs ?_)
  rw [Nat.mul_add, Nat.mul_one] at bound ⊢
  omega
