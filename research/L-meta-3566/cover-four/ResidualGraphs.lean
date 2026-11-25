import Equivalence
import PEqualNP.MetaComplexity.Helpers.PermInputs

namespace VertexPeel.CoverFourResidual

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
    PEqualNP.TopForm PEqualNP.EdgeOwnership VertexPeel.CoverCircuit

/-- The rows are in the order and vertex labelling of `critical.txt`. -/
abbrev table : Fin 17 → ℕ × List (ℕ × ℕ) :=
  ![(7, [(0, 1), (0, 5), (1, 6), (2, 4), (3, 5), (3, 6)]),
    (7, [(0, 1), (0, 5), (1, 6), (2, 4), (2, 6), (3, 5), (3, 6)]),
    (7, [(0, 1), (0, 4), (0, 5), (1, 6), (2, 4), (2, 6), (3, 5), (3, 6)]),
    (7, [(0, 1), (0, 4), (1, 5), (2, 4), (2, 6), (3, 5), (3, 6)]),
    (8, [(0, 4), (0, 5), (0, 6), (1, 5), (1, 7), (2, 6), (2, 7), (3, 7)]),
    (8, [(0, 4), (0, 5), (0, 7), (1, 5), (1, 6), (2, 6), (2, 7), (3, 7)]),
    (8, [(0, 4), (1, 5), (1, 6), (2, 5), (2, 7), (3, 6), (3, 7)]),
    (8, [(0, 4), (0, 7), (1, 5), (1, 6), (2, 5), (2, 7), (3, 6), (3, 7)]),
    (8, [(0, 4), (0, 5), (0, 6), (1, 4), (1, 7), (2, 5), (2, 7), (3, 6), (3, 7)]),
    (8, [(0, 4), (0, 5), (1, 4), (1, 6), (2, 5), (2, 7), (3, 6), (3, 7)]),
    (8, [(0, 1), (0, 4), (0, 6), (1, 5), (1, 7), (2, 6), (2, 7), (3, 7)]),
    (8, [(0, 1), (0, 4), (0, 6), (1, 5), (1, 7), (2, 4), (2, 5), (3, 6), (3, 7)]),
    (8, [(0, 1), (0, 4), (0, 6), (1, 5), (2, 4), (2, 5), (2, 7), (3, 6), (3, 7)]),
    (8, [(0, 3), (0, 4), (0, 5), (1, 2), (1, 4), (1, 6), (2, 5), (2, 7), (3, 6), (3, 7)]),
    (9, [(0, 4), (0, 5), (0, 7), (1, 4), (1, 6), (1, 8), (2, 5), (2, 6), (3, 7), (3, 8)]),
    (9, [(0, 1), (0, 4), (0, 6), (1, 5), (1, 7), (2, 4), (2, 5), (2, 8), (3, 6), (3, 7), (3, 8)]),
    (10, [(0, 4), (0, 5), (0, 7), (1, 4), (1, 6), (1, 8), (2, 5), (2, 6), (2, 9), (3, 7), (3, 8), (3, 9)])]

instance (i : Fin 17) : NeZero (table i).1 := by
  constructor
  exact (by decide +kernel : ∀ j : Fin 17, (table j).1 ≠ 0) i

abbrev graph (i : Fin 17) := edgeGraph (table i).1 (table i).2

abbrev Exact {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C →
    circuitFun n C = graphFun G ∅ → SavesAt G z C

abbrev Lower {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  ∀ C : Circuit, Monotone2 C → circuitFun n C = graphFun G ∅ → k ≤ C.size

theorem lowerTransfer {m n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ρ : Fin n → Fin m) (F : (Fin m → Bool) → Bool)
    (same : ∀ x, graphFun G ∅ (x ∘ ρ) = F x)
    (bound : ∀ s, HasCircuitSize m F s → k ≤ s) : Lower G k := by
  intro C mono correct
  have allowed : FanInTwo C := by
    intro g hg
    obtain ⟨op,fan⟩ := mono g hg
    refine ⟨?_,fan⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢
    tauto
  have small : HasCircuitSize n (graphFun G ∅) C.size :=
    ⟨C,allowed,le_rfl,fun x => congrFun correct x⟩
  have perm := Helpers.PermInputs.relabel_size ρ (graphFun G ∅) C.size small
  rw [show (fun x => graphFun G ∅ (x ∘ ρ)) = F from funext same] at perm
  exact bound _ perm

theorem lowerExact {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : Finset (Fin n)) (cover : ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T)
    (size : G.edgeFinset.card + T.card ≤ k + 1) (edges : 2 ≤ G.edgeFinset.card)
    (bound : Lower G k) : Exact G := by
  obtain ⟨z,pos,left⟩ := nonemptyCut G edges
  refine ⟨z,pos,?_⟩
  intro C ao cor
  have mono : Monotone2 C := by
    intro g hg
    obtain h | h := ao.1 g hg <;> simp [h,ao.2.2 g hg]
  exact atVertexOfCoverBound G z left C ⟨T,cover,size.trans (Nat.add_le_add_right (bound C mono cor) _)⟩

end VertexPeel.CoverFourResidual
