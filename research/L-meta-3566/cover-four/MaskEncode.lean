import Mask4
import CoverCode
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.GetD

namespace VertexPeel.Mask4

set_option maxRecDepth 6000
set_option maxHeartbeats 1500000
open PEqualNP.MetaComplexity.CoverPromise PEqualNP.TopForm VertexPeel.CoverKernel

def subsetAt (s : Nat) : Finset (Fin 4) := Finset.univ.filter (fun i => s.testBit i.val)
def mask (S : Finset (Fin 4)) : Nat :=
  (if 0 ∈ S then 1 else 0) + (if 1 ∈ S then 2 else 0) +
    (if 2 ∈ S then 4 else 0) + (if 3 ∈ S then 8 else 0)

private theorem mask_spec : ∀ S : Finset (Fin 4),
    mask S < 16 ∧ subsetAt (mask S) = S ∧ (mask S = 0 ↔ S = ∅) := by decide +kernel
private theorem subset_spec : ∀ s : Fin 16, mask (subsetAt s.val) = s.val := by decide +kernel

def ends : Nat → Fin 4 × Fin 4
  | 0 => (0,1)
  | 1 => (0,2)
  | 2 => (0,3)
  | 3 => (1,2)
  | 4 => (1,3)
  | _ => (2,3)

private def flag (I : SimpleGraph (Fin 4)) [DecidableRel I.Adj] (S : Finset (Finset (Fin 4)))
    (k : Fin 21) : Bool := if k.val < 6 then decide (I.Adj (ends k.val).1 (ends k.val).2)
    else decide (subsetAt (k.val-5) ∈ S)

def encode (I : SimpleGraph (Fin 4)) [DecidableRel I.Adj] (S : Finset (Finset (Fin 4))) : Code :=
  BitVec.cast (List.length_ofFn) (BitVec.ofBoolListLE (List.ofFn (flag I S)))

private theorem flag_read (I : SimpleGraph (Fin 4)) [DecidableRel I.Adj] (S) (i : Nat) (h : i < 21) :
    (encode I S).getLsbD i = flag I S ⟨i,h⟩ := by
  rw [encode, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem _ _ (by simpa using h : i < (List.ofFn (flag I S)).length),List.getElem_ofFn]

theorem selected (I : SimpleGraph (Fin 4)) [DecidableRel I.Adj] (S : Finset (Finset (Fin 4)))
    {a : Nat} : a ∈ columns (encode I S) ↔ 1 ≤ a ∧ a < 16 ∧ subsetAt a ∈ S := by
  rw [mem_columns]
  by_cases h : 1 ≤ a ∧ a < 16
  · have hi : 6 + (a-1) < 21 := by omega
    rw [flag_read _ _ _ hi]
    simp [flag,show ¬6 + (a-1) < 6 by omega,show 6+(a-1)-5=a by omega]
  · tauto

private theorem inner (I : SimpleGraph (Fin 4)) [DecidableRel I.Adj] (S) (i j : Fin 4) :
    adjB (encode I S) i.val j.val = true ↔ I.Adj i j := by
  have innerRead (u v : Fin 4) (uv : u < v) :
      (encode I S).getLsbD (pairIndex u.val v.val) = decide (I.Adj u v) := by
    have pr : ∀ a b : Fin 4, a < b → pairIndex a.val b.val < 6 ∧
        ends (pairIndex a.val b.val) = (a,b) := by decide +kernel
    obtain ⟨a,b⟩ := pr u v uv
    rw [flag_read _ _ _ (by omega)]
    simp [flag,a,b]
  rcases lt_trichotomy i j with h|rfl|h
  · simp [adjB,forward,j.isLt,innerRead i j h,show i.val < j.val from h]
  · simp [adjB]
  · simp [adjB,forward,i.isLt,innerRead j i h,show j.val < i.val from h,
      show ¬i.val < j.val by omega,I.adj_comm]

private noncomputable def columnEquiv (I : SimpleGraph (Fin 4)) [DecidableRel I.Adj]
    (S : Finset (Finset (Fin 4))) (nz : ∅ ∉ S) :
    {s // s ∈ S} ≃ Fin (columns (encode I S)).length := by
  let L := columns (encode I S)
  have inside (s : {s // s ∈ S}) : mask s.val ∈ L := by
    have ne : mask s.val ≠ 0 := fun eq => nz ((mask_spec s.val).2.2.mp eq ▸ s.property)
    exact (selected I S).mpr ⟨by omega,(mask_spec s.val).1,(mask_spec s.val).2.1.symm ▸ s.property⟩
  let idx (s : {s // s ∈ S}) : Fin L.length :=
    ⟨L.idxOf (mask s.val), List.idxOf_lt_length_of_mem (inside s)⟩
  let val (i : Fin L.length) : {s // s ∈ S} :=
    ⟨subsetAt L[i.val], ((selected I S).mp (List.getElem_mem i.isLt)).2.2⟩
  refine ⟨idx,val,?_,?_⟩
  · intro s
    apply Subtype.ext
    have hidx := List.idxOf_lt_length_of_mem (inside s)
    change subsetAt (L[L.idxOf (mask s.val)]'hidx) = s.val
    rw [List.getElem_idxOf,(mask_spec _).2.1]
  · intro i
    apply Fin.ext
    have bound := ((selected I S).mp (List.getElem_mem i.isLt)).2.1
    change L.idxOf (mask (subsetAt L[i.val])) = i.val
    rw [subset_spec ⟨_,bound⟩,(columns_nodup _).idxOf_getElem]

private theorem column_val (I : SimpleGraph (Fin 4)) [DecidableRel I.Adj] (S) (nz : ∅ ∉ S)
    (s : {s // s ∈ S}) :
    (columns (encode I S)).getD (columnEquiv I S nz s).val 0 = mask s.val := by
  rw [List.getD_eq_getElem _ _ (columnEquiv I S nz s).isLt]
  apply List.getElem_idxOf

/-- Recover the actual, unpadded, labeled bit-code graph with the exact adjacency relation. -/
noncomputable def codeIso (I : SimpleGraph (Fin 4)) [DecidableRel I.Adj]
    (S : Finset (Finset (Fin 4))) (nz : ∅ ∉ S) : CoverCode.graph I S ≃g graph (encode I S) := by
  let e := columnEquiv I S nz
  let flat := (Equiv.sumCongr (Equiv.refl (Fin 4)) e).trans finSumFinEquiv
  refine ⟨flat,?_⟩
  rintro (i|s) (j|q)
  · exact inner I S i j
  · change adjB (encode I S) i.val (4+(e q).val) = true ↔ i ∈ q.val
    have lt : i.val < 4 + (e q).val := by omega
    simp only [adjB,lt,ite_true,forward,show ¬4 + (e q).val < 4 by omega,ite_false,i.isLt,
      Nat.add_sub_cancel_left]
    rw [column_val I S nz q]
    have eq (v : Finset (Fin 4)) : (mask v).testBit i.val = true ↔ i ∈ v := by
      have h : i ∈ subsetAt (mask v) ↔ i ∈ v := Iff.of_eq (congrArg (fun T => i ∈ T) (mask_spec v).2.1)
      simpa only [subsetAt,Finset.mem_filter,Finset.mem_univ,true_and] using h
    exact eq q.val
  · change adjB (encode I S) (4+(e s).val) j.val = true ↔ j ∈ s.val
    have lt : j.val < 4 + (e s).val := by omega
    simp only [adjB,show ¬4+(e s).val < j.val by omega,lt,ite_true,forward,
      show ¬4+(e s).val < 4 by omega,ite_false,j.isLt,Nat.add_sub_cancel_left]
    rw [column_val I S nz s]
    have h : j ∈ subsetAt (mask s.val) ↔ j ∈ s.val := Iff.of_eq (congrArg (fun T => j ∈ T) (mask_spec s.val).2.1)
    simpa only [subsetAt,Finset.mem_filter,Finset.mem_univ,true_and] using h
  · change adjB (encode I S) (4+(e s).val) (4+(e q).val) = true ↔ False
    unfold adjB forward
    split <;> simp [show ¬4+(e s).val < 4 by omega,show ¬4+(e q).val < 4 by omega]

theorem exists_code {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (K : Finset (Fin n)) (cover : IsVertexCover G K) (card : K.card = 4)
    (sq : NoFourCycle G) (noTwins : ¬TwinLeaves G) (active : ∀ v, 0 < G.degree v) :
    ∃ z : Code, Nonempty (G ≃g graph z) := by
  classical
  obtain ⟨I,S,nz,⟨iso⟩⟩ := CoverCode.exists_code G K cover card sq noTwins active
  exact ⟨encode I S,⟨iso.trans (codeIso I S nz)⟩⟩

#print axioms exists_code
end VertexPeel.Mask4
