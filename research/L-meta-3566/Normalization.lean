import Equivalence
import PEqualNP.Library.Helpers.PeelableSanity
import PEqualNP.Outside.L_meta_7241

namespace VertexPeel

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.CoverPromise PEqualNP.Library.Peel
open CoverCircuit

abbrev PairSound {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
    ∀ a b, ¬ G.Adj a b → gateVal n C j (pairInput a b) = false

-- An AND in this compiler can only turn on when the input contains an actual edge.
theorem pairSoundCompiler {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : Finset (Fin n)) (cover : IsVertexCover G T) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ PairSound G D ∧
      D.size ≤ G.edgeFinset.card + T.card - 1 := by
  classical
  obtain ⟨D,ao,correct,size,owners⟩ := CoverCircuit.main n G T cover
  refine ⟨D,ao,?_,?_,size⟩
  · funext x
    simpa [circuitFun,graphFun] using correct x
  · intro j hj hop a b hn
    apply Bool.eq_false_iff.mpr
    intro on
    have op : D.gates[j].op = GateOp.and := by simpa [gateAt, List.getD, hj] using hop
    have eqg : D.gates[j]? = some D.gates[j] := List.getElem?_eq_getElem hj
    obtain ⟨u,v,adj,hu,hv⟩ := owners j D.gates[j] eqg op (pairInput a b) on
    simp only [pairInput, decide_eq_true_eq] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact adj.ne rfl
    · exact hn adj
    · exact hn adj.symm
    · exact adj.ne rfl

-- For each size budget the numerical question and semantic normalization are equivalent.
theorem budget_iff_pairSound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (square : NoFourCycle G) (k : ℕ) :
    (∃ T : Finset (Fin n), IsVertexCover G T ∧ G.edgeFinset.card + T.card ≤ k + 1) ↔
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ PairSound G D ∧ D.size ≤ k := by
  constructor
  · rintro ⟨T,cover,bound⟩
    obtain ⟨D,ao,ev,sound,size⟩ := pairSoundCompiler G T cover
    exact ⟨D,ao,ev,sound,by omega⟩
  · rintro ⟨D,ao,ev,sound,size⟩
    obtain ⟨T,cover,bound⟩ := PEqualNP.Outside.L_meta_7241 n G D square ao ev sound
    exact ⟨T,cover,by omega⟩

abbrev Normalization : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∃ color : Fin n → Bool, ∀ u v, G.Adj u v → color u ≠ color v) →
    NoFourCycle G → 2 ≤ G.edgeFinset.card →
    ∀ C : Circuit, IsAO2 n C → circuitFun n C = graphFun G ∅ →
      ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ PairSound G D ∧ D.size ≤ C.size

theorem exactPeel_iff_normalization : ExactPeel ↔ Normalization := by
  rw [exactPeel_iff_globalLower]
  constructor
  · intro lower n G inst bip square edges C ao ev
    exact (budget_iff_pairSound G square C.size).mp (lower n G bip square edges C ao ev)
  · intro norm n G inst bip square edges C ao ev
    exact (budget_iff_pairSound G square C.size).mpr (norm n G bip square edges C ao ev)

-- On a peelable graph every vertex whose deletion leaves an edge works, for every circuit.
theorem peelableAtVertex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (peelable : Peelable G) (z : Fin n) (remaining : 0 < (G.deleteIncidenceSet z).edgeFinset.card)
    (C : Circuit) (ao : IsAO2 n C) (correct : circuitFun n C = graphFun G ∅) :
    SavesAt G z C := by
  classical
  obtain ⟨T,cover,card⟩ := Loc.tau_attained G
  have allowed : FanInTwo C := by
    intro g hg
    rcases ao.1 g hg with h | h
    · simp [h, (ao.2.2 g hg)]
    · simp [h, (ao.2.2 g hg)]
  have small : HasCircuitSize n (Helpers.Forest.F G ∅) C.size := by
    refine ⟨C,allowed,le_rfl,?_⟩
    intro x
    simpa [Helpers.Forest.F,circuitFun,graphFun] using congrFun correct x
  have bound := Scratch.a1_peelable n G ∅ peelable (fun _ _ _ => Finset.notMem_empty _) C.size small
  simp only [Loc.Phi1, Finset.card_empty, zero_add] at bound
  rw [Set.ncard_eq_toFinset_card'] at bound
  change G.edgeFinset.card + Loc.tau G ≤ C.size + 1 at bound
  exact atVertexOfCoverBound G z remaining C ⟨T,cover,by omega⟩

theorem peelableGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (peelable : Peelable G) (edges : 2 ≤ G.edgeFinset.card) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C →
      circuitFun n C = graphFun G ∅ → SavesAt G z C := by
  obtain ⟨z,hz,left⟩ := nonemptyCut G edges
  exact ⟨z,hz,peelableAtVertex G peelable z left⟩

end VertexPeel

#print axioms VertexPeel.budget_iff_pairSound
#print axioms VertexPeel.exactPeel_iff_normalization
#print axioms VertexPeel.peelableGraph
