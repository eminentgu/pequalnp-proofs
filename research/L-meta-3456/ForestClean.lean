import ForestCoverBudget
import CoverNormalization
import PEqualNP.MetaComplexity.L104

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Local3456.Forest

/-- The singleton-clean normalization problem holds for every bipartite forest, with
    unequal side sizes, isolated vertices, and unrestricted fanout and NOT gates in the input circuit. -/
theorem normalize {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (C : Circuit) (forest : (incidenceGraph I).IsAcyclic) (legal : FanInTwo C)
    (correct : ∀ z, circuitFun (n+m) C z = true ↔
      ∃ p l, I p l ∧ z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (n+m) D ∧ D.size ≤ C.size ∧
      (∀ z, circuitFun (n+m) D z = true ↔
        ∃ p l, I p l ∧ z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true) ∧
      ∀ j < D.size, (gateAt D j).op = .and → ∀ k : Fin (n+m), singleWire D k (n+m+j) = false := by
  let E := Finset.univ.filter (fun e : Fin n × Fin m => I e.1 e.2)
  obtain ⟨A,B,cover,budget⟩ := cover_budget PEqualNP.MetaComplexity.L104 I C forest legal correct
  obtain ⟨D,dm,db,size,computes,clean⟩ := normalize_at_cover_cost n m E A B C cover budget
  refine ⟨D,dm,db,size,?_,clean⟩
  intro z
  simpa [E] using computes z

/-- The point and line singleton conditions in L-meta-3456 follow with their original wire indices. -/
theorem normalize_equal_sides (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (forest : (incidenceGraph I).IsAcyclic) (mono : Monotone2 C)
    (correct : ∀ z, circuitFun (N+N) C z = true ↔
      ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size ≤ C.size ∧
      (∀ z, circuitFun (N+N) D z = true ↔
        ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      ∀ j < D.gates.length, (gateAt D j).op = .and →
        (∀ p : Fin N, (D.wires (List.ofFn (fun k : Fin (N+N) => decide (k=Fin.castAdd N p)))).getD (N+N+j) false = false) ∧
        ∀ l : Fin N, (D.wires (List.ofFn (fun k : Fin (N+N) => decide (k=Fin.natAdd N l)))).getD (N+N+j) false = false := by
  have legal : FanInTwo C := by
    intro g hg
    obtain ⟨op,arity⟩ := mono g hg
    refine ⟨?_,arity⟩
    rcases op with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  obtain ⟨D,dm,db,sz,sem,clean⟩ := normalize I C forest legal correct
  refine ⟨D,dm,db,sz,sem,?_⟩
  intro j hj hand
  exact ⟨fun p => clean j hj hand (Fin.castAdd N p),fun l => clean j hj hand (Fin.natAdd N l)⟩

end PEqualNP.Local3456.Forest
