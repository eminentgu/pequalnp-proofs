import Mask4
import ResidualGraphs
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace VertexPeel.CoverFourClass
open PEqualNP.MetaComplexity.CoverPromise
open scoped Sym2
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def Exit (z : Mask4.Code) : Prop :=
  let G := Mask4.graph z
  G.IsAcyclic ∨ (∃ a, G.degree a = 1 ∧ ∀ S, IsVertexCover (G.deleteIncidenceSet a) S → 4 ≤ S.card) ∨
    ∃ i : Fin 17, Nonempty (G ≃g CoverFourResidual.graph i)

/-- In a rooted forest, the subtree of a child separates the ends of each edge. -/
theorem forestCert {n : ℕ} (G : SimpleGraph (Fin n)) (subtree : Fin n → Nat)
    (valid : ∀ u v : Fin n, G.Adj u v →
      let mask := if (subtree u).testBit v.val then subtree v else subtree u
      mask.testBit u.val ≠ mask.testBit v.val ∧
      ∀ a b : Fin n, G.Adj a b → mask.testBit a.val ≠ mask.testBit b.val →
        (a = u ∧ b = v) ∨ (a = v ∧ b = u)) : G.IsAcyclic := by
  apply SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mpr
  intro u v uv
  obtain ⟨distinct, cuts⟩ := valid u v uv
  apply SimpleGraph.isBridge_iff.mpr
  intro reach
  apply distinct
  let c (w : Fin n) := (if (subtree u).testBit v.val then subtree v else subtree u).testBit w.val
  have eq {x y} (h : (G.deleteEdges {s(u,v)}).Reachable x y) : c x = c y := by
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => rfl
    | tail _ e ih =>
      apply ih.trans
      by_contra bad
      obtain ⟨ab, other⟩ := SimpleGraph.deleteEdges_adj.mp e
      apply other
      exact Set.mem_singleton_iff.mpr (Sym2.eq_iff.mpr (cuts _ _ ab bad))
  exact eq reach

/-- Four disjoint surviving edges force four vertices in every cover after deleting a leaf. -/
theorem matchingCert {n : ℕ} (G : SimpleGraph (Fin n)) (a : Fin n)
    (l r : Fin 4 → Fin n) (edge : ∀ i, G.Adj (l i) (r i) ∧ l i ≠ a ∧ r i ≠ a)
    (distinct : ∀ i j, i ≠ j → l i ≠ l j ∧ l i ≠ r j ∧ r i ≠ l j ∧ r i ≠ r j) :
    ∀ S, IsVertexCover (G.deleteIncidenceSet a) S → 4 ≤ S.card := by
  intro S cover
  let pick (i : Fin 4) := if l i ∈ S then l i else r i
  have mem (i) : pick i ∈ S := by
    have h := cover _ _ (SimpleGraph.deleteIncidenceSet_adj.mpr (edge i))
    by_cases hl : l i ∈ S
    · simpa [pick,hl] using hl
    · simpa [pick,hl] using h.resolve_left hl
  have inj : Function.Injective pick := by
    intro i j h
    by_contra ne
    obtain ⟨a,b,c,d⟩ := distinct i j ne
    unfold pick at h
    split at h <;> split at h <;> contradiction
  let f (i : Fin 4) : ↥S := ⟨pick i, mem i⟩
  have fi : Function.Injective f := fun _ _ eq => inj (congrArg Subtype.val eq)
  simpa using Fintype.card_le_of_injective f fi

theorem smallCert {n : ℕ} (G : SimpleGraph (Fin n)) (a : Fin n)
    (valid : ∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ≠ a → v ≠ a → u ∈ S ∨ v ∈ S) →
      4 ≤ S.card) : ∀ S, IsVertexCover (G.deleteIncidenceSet a) S → 4 ≤ S.card := by
  intro S cover
  exact valid S fun u v h hu hv => cover u v (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨h,hu,hv⟩)

theorem isoCert {n : ℕ} (G H : SimpleGraph (Fin n)) (h : ∀ u v, G.Adj u v ↔ H.Adj u v) :
    Nonempty (G ≃g H) := by
  have eq : G = H := SimpleGraph.ext (funext fun u => funext fun v => propext (h u v))
  subst H
  exact ⟨SimpleGraph.Iso.refl⟩
end VertexPeel.CoverFourClass
