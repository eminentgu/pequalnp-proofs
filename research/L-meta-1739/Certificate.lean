import OrderedMatching

namespace Research.CyclicBounds

open SimpleGraph Research.LeafCharge PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4837_aux GraphCircuit4837
open scoped Classical

/-- A pseudoforest contributes its full edge count. Each preceding active vertex deletion
contributes one if an edge survives it. The budget bounds the OR count plus one. -/
inductive OrCertificate {n} : SimpleGraph (Fin n) → ℕ → Prop where
  | base (G) (sparse : GraphInduction4837.sparse G) : OrCertificate G G.edgeSet.ncard
  | delete {G : SimpleGraph (Fin n)} (v : Fin n) {b : ℕ} (active : v ∈ G.support)
      (survives : G.degree v < G.edgeSet.ncard) (next : OrCertificate (G.deleteIncidenceSet v) b) :
      OrCertificate G (b+1)

theorem orBound {n b} {G : SimpleGraph (Fin n)} (cert : OrCertificate G b)
    (no4 : GraphInduction4837.noFour G) (C : Circuit) (hm : Monotone2 C)
    (det : detects G C) (A : Finset ℕ) (cover : covers C A) : b ≤ A.card+1 := by
  induction cert generalizing C A with
  | base G sparse => exact PEqualNP.Outside.L_meta_4837 _ G C A sparse no4 hm det cover
  | @delete G v b active survives next ih =>
    obtain ⟨D,B,hcard,mono,ev,allOr⟩ := Leaf4837.restrict_one C v A hm cover
      (one_bit det active) (accepts_without det v survives)
    have h := ih (GraphInduction4837.noFour_subgraph (G.deleteIncidenceSet_le v) no4)
      D mono (PaidGraph4837.after_restriction det ev) B allOr
    omega

theorem combine {n a b} {G : SimpleGraph (Fin n)} (hf : NoSquare G) (cert : OrCertificate G b)
    (C : Circuit) (hm : Monotone2 C) (det : detects G C) (bound : a ≤ ands C.gates) :
    b + a ≤ C.size + 1 := by
  obtain ⟨A,sub,size,mem⟩ := gateIndices C.gates
  have o := orBound cert (noSquareWalk hf) C hm det (Finset.range C.gates.length \ A) (by
    intro j g hj op
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_range.mpr (List.getElem?_eq_some_iff.mp hj).1,?_⟩
    intro m
    have bad := (mem j g hj).mp m
    simp [op,isAnd] at bad)
  rw [Finset.card_sdiff_of_subset sub,Finset.card_range] at o
  have cardle := Finset.card_le_card sub
  rw [Finset.card_range] at cardle
  change b + a ≤ C.gates.length + 1
  omega

theorem orderedTotal {n k b} {G : SimpleGraph (Fin n)} (hf : NoSquare G) (cert : OrCertificate G b)
    (L R : Fin k → Fin n) (edge : ∀ j, G.Adj (L j) (R j))
    (indep : ∀ i j, ¬G.Adj (L i) (L j)) (order : ∀ i j, i<j → ¬G.Adj (L i) (R j))
    (C : Circuit) (hm : Monotone2 C) (det : detects G C) : b+k ≤ C.size+1 :=
  combine hf cert C hm det (orderedMatchingAnd G L R edge indep order C hm det)

end Research.CyclicBounds
