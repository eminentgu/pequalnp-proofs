import Mask4
import CycleCover
import CoverThreeCore
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.GetD

namespace VertexPeel.Mask4
open PEqualNP.TopForm VertexPeel.CoverThreeCore
set_option maxHeartbeats 2000000
set_option maxRecDepth 5000

private theorem bit_mono {m z : Code} (sub : z &&& m = m) (k : ℕ) (on : m.getLsbD k = true) :
    z.getLsbD k = true := by
  have eq := congrArg (fun v : Code => v.getLsbD k) sub
  simpa [on] using eq

private theorem column_mono {m z : Code} (sub : z &&& m = m) {s : Nat} (mem : s ∈ columns m) :
    s ∈ columns z := by
  obtain ⟨lo,hi,bit⟩ := mem_columns.mp mem
  exact mem_columns.mpr ⟨lo,hi,bit_mono sub _ bit⟩

private def pos {m z : Code} (sub : z &&& m = m) (i : Fin (columns m).length) :
    Fin (columns z).length :=
  ⟨(columns z).idxOf (columns m)[i.val],List.idxOf_lt_length_of_mem (column_mono sub (List.getElem_mem _))⟩

private theorem lookup {m z : Code} (sub : z &&& m = m) (i : Fin (columns m).length) :
    (columns z).getD (pos sub i).val 0 = (columns m).getD i.val 0 := by
  rw [List.getD_eq_getElem _ _ (pos sub i).isLt,List.getD_eq_getElem _ _ i.isLt]
  apply List.getElem_idxOf

theorem mono_embedding {m z : Code} (sub : z &&& m = m) :
    ∃ f : Fin (4 + (columns m).length) ↪ Fin (4 + (columns z).length),
      ∀ a b, (graph m).Adj a b → (graph z).Adj (f a) (f b) := by
  let ir := pos sub
  have inj : Function.Injective ir := by
    intro i j e
    have eq := (lookup sub i).symm.trans ((congrArg (fun r : Fin (columns z).length =>
      (columns z).getD r.val 0) e).trans (lookup sub j))
    rw [List.getD_eq_getElem _ _ i.isLt,List.getD_eq_getElem _ _ j.isLt] at eq
    exact Fin.ext (by simpa only [(columns_nodup m).idxOf_getElem] using congrArg (columns m).idxOf eq)
  let pair := (Function.Embedding.refl (Fin 4)).sumMap (⟨ir,inj⟩ : Fin (columns m).length ↪ Fin (columns z).length)
  let f := finSumFinEquiv.symm.toEmbedding.trans (pair.trans finSumFinEquiv.toEmbedding)
  have fmap (x : Fin 4 ⊕ Fin (columns m).length) : f (finSumFinEquiv x) = finSumFinEquiv (pair x) := by
    change finSumFinEquiv (pair (finSumFinEquiv.symm (finSumFinEquiv x))) = _
    rw [Equiv.symm_apply_apply]
  refine ⟨f,?_⟩
  intro a b edge
  obtain ⟨a,rfl⟩ := finSumFinEquiv.surjective a
  obtain ⟨b,rfl⟩ := finSumFinEquiv.surjective b
  change adjB m _ _ = true at edge
  change adjB z _ _ = true
  rw [fmap,fmap]
  rcases a with a|a <;> rcases b with b|b
  · change adjB m a.val b.val = true at edge
    change adjB z a.val b.val = true
    unfold adjB forward at *
    split at edge
    · rename_i lt
      simpa [lt,b.isLt] using bit_mono sub _ (by simpa [b.isLt] using edge : m.getLsbD (pairIndex a.val b.val) = true)
    · rename_i ge
      split at edge
      · rename_i lt
        simpa [ge,lt,a.isLt] using bit_mono sub _ (by simpa [a.isLt] using edge : m.getLsbD (pairIndex b.val a.val) = true)
      · contradiction
  · change adjB m a.val (4+b.val) = true at edge
    change adjB z a.val (4+(ir b).val) = true
    have h (x : Nat) : a.val < 4+x := by omega
    have col := lookup sub b
    rw [List.getD_eq_getElem _ _ (pos sub b).isLt,List.getD_eq_getElem _ _ b.isLt] at col
    simpa [adjB,forward,h,a.isLt,ir,col] using edge
  · change adjB m (4+a.val) b.val = true at edge
    change adjB z (4+(ir a).val) b.val = true
    have h (x : Nat) : b.val < 4+x := by omega
    have h' (x : Nat) : ¬4+x < b.val := by omega
    have col := lookup sub a
    rw [List.getD_eq_getElem _ _ (pos sub a).isLt,List.getD_eq_getElem _ _ a.isLt] at col
    simpa [adjB,forward,h,h',b.isLt,ir,col] using edge
  · change adjB m (4+a.val) (4+b.val) = true at edge
    unfold adjB forward at edge
    split at edge <;> simp at edge

theorem girth_of_injection {m n : ℕ} {A : SimpleGraph (Fin m)} {B : SimpleGraph (Fin n)}
    [DecidableRel A.Adj] [DecidableRel B.Adj] (f : Fin m ↪ Fin n)
    (hom : ∀ a b, A.Adj a b → B.Adj (f a) (f b)) (tri : NoTriangles B) (sq : NoFourCycle B) :
    NoTriangles A ∧ NoFourCycle A := by
  refine ⟨fun a b c ab bc ca => tri _ _ _ (hom _ _ ab) (hom _ _ bc) (hom _ _ ca),?_⟩
  intro a b ne
  apply le_trans _ (sq (f a) (f b) (f.injective.ne ne))
  apply Finset.card_le_card_of_injOn f
  · intro v mem
    obtain ⟨_,ab,bc⟩ := Finset.mem_filter.mp mem
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hom _ _ ab,hom _ _ bc⟩
  · exact f.injective.injOn

/-- Choosing more pattern bits preserves every edge and can only increase the cover number. -/
theorem tau_mono {m z : Code} (sub : z &&& m = m) :
    PEqualNP.MetaComplexity.Loc.tau (graph m) ≤ PEqualNP.MetaComplexity.Loc.tau (graph z) := by
  classical
  obtain ⟨f,hom⟩ := mono_embedding sub
  obtain ⟨T,cover,size⟩ := PEqualNP.MetaComplexity.Loc.tau_attained (graph z)
  let U := Finset.univ.filter (fun i => f i ∈ T)
  have c : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover (graph m) U := by
    intro a b ab
    simpa [U] using cover _ _ (hom _ _ ab)
  have maps : U.map f ⊆ T := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
    exact (Finset.mem_filter.mp hj).2
  have count : U.card ≤ T.card := by simpa using Finset.card_le_card maps
  exact (PEqualNP.MetaComplexity.Loc.tau_le _ _ c).trans (count.trans_eq size)

end VertexPeel.Mask4
