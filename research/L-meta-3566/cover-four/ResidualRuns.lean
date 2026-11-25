import ResidualGraphs
import PEqualNP.Outside.L_meta_579

namespace VertexPeel.CoverFourResidual

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
    PEqualNP.Library.Peel
abbrev TinyRun {n} (G : SimpleGraph (Fin n)) (q0 q1 q2 q3 q4 q5 : Fin n) :=
  [q1,q2,q3,q4].Nodup ∧ q0 ∉ [q1,q2,q3,q4] ∧ q5 ∉ [q1,q2,q3,q4] ∧
  (∀ w, G.Adj q1 w ↔ w=q0 ∨ w=q2) ∧ (∀ w, G.Adj q2 w ↔ w=q1 ∨ w=q3) ∧
  (∀ w, G.Adj q3 w ↔ w=q2 ∨ w=q4) ∧ (∀ w, G.Adj q4 w ↔ w=q3 ∨ w=q5)

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a b c d e f : Fin n) :
    Decidable (TinyRun G a b c d e f) := by
  unfold TinyRun
  infer_instance

private theorem runLower {n k s : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (deg : ∀ u, G.degree u ≤ 3)
    (noTri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬G.Adj c a)
    (noSquare : ∀ a b c d : Fin n, a ≠ c → b ≠ d → G.Adj a b →
        G.Adj b c → G.Adj c d → ¬G.Adj d a)
    (runs : ∀ X : Finset (Fin n), (∃ i j, (delVerts G X).Adj i j) →
      GoodLeaf (delVerts G X) ∨ ∃ a b c d e f, TinyRun (delVerts G X) a b c d e f)
    (nonempty : ∃ i j, G.Adj i j)
    (covers : ∀ T : Finset (Fin n), (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card)
    (target : s+1 ≤ G.edgeFinset.card+k) : Lower G s := by
  have girth (v : Fin n) (p : G.Walk v v) (cycle : p.IsCycle) : 5 ≤ p.length := by
    have lo := cycle.three_le_length
    by_contra! short
    have h0 := p.adj_getVert_succ (i := 0) (by omega)
    have h1 := p.adj_getVert_succ (i := 1) (by omega)
    have h2 := p.adj_getVert_succ (i := 2) (by omega)
    by_cases three : p.length = 3
    · have end3 : p.getVert 3 = p.getVert 0 := by rw [← three,p.getVert_length,p.getVert_zero]
      change G.Adj (p.getVert 2) (p.getVert 3) at h2
      exact noTri _ _ _ h0 h1 (end3 ▸ h2)
    · have four : p.length = 4 := by omega
      have h3 := p.adj_getVert_succ (i := 3) (by omega)
      have ne02 : p.getVert 0 ≠ p.getVert 2 := by
        intro e
        have : 0 = 2 := cycle.getVert_injOn' (by simp) (by simp; omega) e
        contradiction
      have ne13 : p.getVert 1 ≠ p.getVert 3 := by
        intro e
        have : 1 = 3 := cycle.getVert_injOn' (by simp; omega) (by simp; omega) e
        contradiction
      have end4 : p.getVert 4 = p.getVert 0 := by rw [← four,p.getVert_length,p.getVert_zero]
      change G.Adj (p.getVert 3) (p.getVert 4) at h3
      exact noSquare _ _ _ _ ne02 ne13 h0 h1 h2 (end4 ▸ h3)


  intro C mono correct
  have d (u : Fin n) : (G.neighborSet u).ncard ≤ 3 := by
    rw [Set.ncard_eq_toFinset_card']
    exact deg u
  have allowed : FanInTwo C := by
    intro g hg
    obtain ⟨op,fan⟩ := mono g hg
    refine ⟨?_,fan⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢
    tauto
  have small : HasCircuitSize n (Helpers.Forest.F G ∅) C.size := by
    refine ⟨C,allowed,le_rfl,?_⟩
    intro x
    simpa [Helpers.Forest.F,circuitFun,graphFun] using congrFun correct x
  have h := PEqualNP.Outside.L_meta_579 n k C.size G ∅ d girth runs
    (fun _ _ _ => Finset.notMem_empty _) (Or.inr nonempty) covers small
  simp only [Finset.card_empty,zero_add] at h
  rw [Set.ncard_eq_toFinset_card'] at h
  change G.edgeFinset.card + k ≤ C.size + 1 at h
  omega

set_option maxHeartbeats 0
set_option synthInstance.maxSize 4096
set_option maxRecDepth 100000

private abbrev H0 := PEqualNP.EdgeOwnership.edgeGraph 7 (table 0).2

theorem lower0 : Lower (graph 0) 9 := by
  apply runLower H0 (k:=4)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro X e
    have cert : ∀ X : Finset (Fin 7), (∃ u v, (delVerts H0 X).Adj u v) →
        GoodLeaf (delVerts H0 X) ∨ TinyRun (delVerts H0 X) 5 0 1 6 3 5 := by decide +kernel
    rcases cert X e with good | r0
    · exact Or.inl good
    · exact Or.inr ⟨5,0,1,6,3,5,r0⟩
  · exact ⟨0,1,by decide⟩
  · decide +kernel
  · decide +kernel

private abbrev H1 := PEqualNP.EdgeOwnership.edgeGraph 7 (table 1).2

theorem lower1 : Lower (graph 1) 10 := by
  apply runLower H1 (k:=4)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro X e
    have cert : ∀ X : Finset (Fin 7), (∃ u v, (delVerts H1 X).Adj u v) →
        GoodLeaf (delVerts H1 X) ∨ TinyRun (delVerts H1 X) 5 0 1 6 3 5 ∨ TinyRun (delVerts H1 X) 6 1 0 5 3 6 := by decide +kernel
    rcases cert X e with good | r0 | r1
    · exact Or.inl good
    · exact Or.inr ⟨5,0,1,6,3,5,r0⟩
    · exact Or.inr ⟨6,1,0,5,3,6,r1⟩
  · exact ⟨0,1,by decide⟩
  · decide +kernel
  · decide +kernel

private abbrev H3 := PEqualNP.EdgeOwnership.edgeGraph 7 (table 3).2

theorem lower3 : Lower (graph 3) 10 := by
  apply runLower H3 (k:=4)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro X e
    have cert : ∀ X : Finset (Fin 7), (∃ u v, (delVerts H3 X).Adj u v) →
        GoodLeaf (delVerts H3 X) ∨ TinyRun (delVerts H3 X) 4 0 1 5 3 6 := by decide +kernel
    rcases cert X e with good | r0
    · exact Or.inl good
    · exact Or.inr ⟨4,0,1,5,3,6,r0⟩
  · exact ⟨0,1,by decide⟩
  · decide +kernel
  · decide +kernel

private abbrev H5 := PEqualNP.EdgeOwnership.edgeGraph 8 (table 5).2

theorem lower5 : Lower (graph 5) 11 := by
  apply runLower H5 (k:=4)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro X e
    have cert : ∀ X : Finset (Fin 8), (∃ u v, (delVerts H5 X).Adj u v) →
        GoodLeaf (delVerts H5 X) ∨ TinyRun (delVerts H5 X) 7 2 6 1 5 0 := by decide +kernel
    rcases cert X e with good | r0
    · exact Or.inl good
    · exact Or.inr ⟨7,2,6,1,5,0,r0⟩
  · exact ⟨0,4,by decide⟩
  · decide +kernel
  · decide +kernel

private abbrev H6 := PEqualNP.EdgeOwnership.edgeGraph 8 (table 6).2

theorem lower6 : Lower (graph 6) 10 := by
  apply runLower H6 (k:=4)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro X e
    have cert : ∀ X : Finset (Fin 8), (∃ u v, (delVerts H6 X).Adj u v) →
        GoodLeaf (delVerts H6 X) ∨ TinyRun (delVerts H6 X) 6 1 5 2 7 3 := by decide +kernel
    rcases cert X e with good | r0
    · exact Or.inl good
    · exact Or.inr ⟨6,1,5,2,7,3,r0⟩
  · exact ⟨0,4,by decide⟩
  · decide +kernel
  · decide +kernel

private abbrev H7 := PEqualNP.EdgeOwnership.edgeGraph 8 (table 7).2

theorem lower7 : Lower (graph 7) 11 := by
  apply runLower H7 (k:=4)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro X e
    have cert : ∀ X : Finset (Fin 8), (∃ u v, (delVerts H7 X).Adj u v) →
        GoodLeaf (delVerts H7 X) ∨ TinyRun (delVerts H7 X) 6 1 5 2 7 3 ∨ TinyRun (delVerts H7 X) 7 2 5 1 6 3 := by decide +kernel
    rcases cert X e with good | r0 | r1
    · exact Or.inl good
    · exact Or.inr ⟨6,1,5,2,7,3,r0⟩
    · exact Or.inr ⟨7,2,5,1,6,3,r1⟩
  · exact ⟨0,4,by decide⟩
  · decide +kernel
  · decide +kernel

private abbrev H9 := PEqualNP.EdgeOwnership.edgeGraph 8 (table 9).2

theorem lower9 : Lower (graph 9) 11 := by
  apply runLower H9 (k:=4)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro X e
    have cert : ∀ X : Finset (Fin 8), (∃ u v, (delVerts H9 X).Adj u v) →
        GoodLeaf (delVerts H9 X) ∨ TinyRun (delVerts H9 X) 5 0 4 1 6 3 := by decide +kernel
    rcases cert X e with good | r0
    · exact Or.inl good
    · exact Or.inr ⟨5,0,4,1,6,3,r0⟩
  · exact ⟨0,4,by decide⟩
  · decide +kernel
  · decide +kernel

end VertexPeel.CoverFourResidual
