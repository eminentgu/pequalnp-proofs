import PEqualNP.Research.L_meta_1774.CoveredOwnership

namespace PEqualNP.Outside.L_meta_1774

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.MetaComplexity.CoverPromise

abbrev AllUseful {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) :=
  ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ∃ u v, G.Adj u v ∧ Owns n C j u v

noncomputable abbrev Defects {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) :=
  (disjointOwners G C).ncard

abbrev StepAt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :=
  ∀ C : Circuit, IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ → AllUseful G C →
    0 < Defects G C → ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size ≤ C.size ∧ AllUseful G D ∧ Defects G D < Defects G C

abbrev NormalAt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :=
  ∀ C : Circuit, IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ → AllUseful G C →
    ∃ D : Circuit, IsMinimalMonoCircuit n D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size = C.size ∧ AllUseful G D ∧ Defects G D = 0

theorem step_iff_normal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    StepAt G ↔ NormalAt G := by
  classical
  constructor
  · intro step C hmin correct ready
    let P (k : ℕ) := ∃ D : Circuit, IsMinimalMonoCircuit n D ∧
      circuitFun n D = graphFun G ∅ ∧ D.size = C.size ∧ AllUseful G D ∧ Defects G D = k
    have inhabited : ∃ k, P k := ⟨_,C,hmin,correct,rfl,ready,rfl⟩
    obtain ⟨D,dmin,dcorrect,dequal,dready,count⟩ := Nat.find_spec inhabited
    refine ⟨D,dmin,dcorrect,dequal,dready,?_⟩
    by_contra positive
    obtain ⟨E,emon,ecorrect,esz,eready,edown⟩ := step D dmin dcorrect dready (Nat.pos_of_ne_zero positive)
    have same : circuitFun n E = circuitFun n D := ecorrect.trans dcorrect.symm
    have eqsize : E.size = D.size := le_antisymm esz (dmin.2 E emon same)
    have emin : IsMinimalMonoCircuit n E := by
      refine ⟨emon,?_⟩
      intro F fmon fev
      rw [eqsize]
      exact dmin.2 F fmon (fev.trans same)
    have least := Nat.find_min' inhabited (show P (Defects G E) from
        ⟨E,emin,ecorrect,eqsize.trans dequal,eready,rfl⟩)
    omega
  · intro normal C hmin correct ready pos
    obtain ⟨D,m,e,s,r,z⟩ := normal C hmin correct ready
    exact ⟨D,m.1,e,s.le,r,by omega⟩

abbrev SufficientCover {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) :=
  ∃ T : Finset (Fin n), IsVertexCover G T ∧ G.edgeSet.ncard + T.card - 1 ≤ C.size

theorem step_of_deficient_cases {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (deficient : ∀ C : Circuit, IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
      AllUseful G C → ¬ SufficientCover G C → 0 < Defects G C →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
        AllUseful G D ∧ Defects G D < Defects G C) : StepAt G := by
  classical
  intro C hmin correct ready positive
  by_cases existsCover : SufficientCover G C
  · obtain ⟨T,cover,bound⟩ := existsCover
    exact coveredDescent G C T cover bound positive
  · exact deficient C hmin correct ready existsCover positive

abbrev Exact1774 : Prop := ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →     PEqualNP.TopForm.NoFourCycle x2 →       have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ x7 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11;       have x7 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => {x8 : ℕ | ∃ (x9 : Fin x1) (x10 : Fin x1) (x11 : Fin x1) (x12 : Fin x1), x2.Adj x9 x10 ∧ x2.Adj x11 x12 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x8 x9 x10 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x8 x11 x12 ∧ x9 ≠ x11 ∧ x9 ≠ x12 ∧ x10 ≠ x11 ∧ x10 ≠ x12}.ncard;       ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x8 → PEqualNP.MetaComplexity.circuitFun x1 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x6 x8 → (0 : ℕ) < x7 x8 → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 ∧ PEqualNP.MetaComplexity.circuitFun x1 x13 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x13.size ≤ x8.size ∧ x6 x13 ∧ x7 x13 < x7 x8

theorem exact_iff_normal : Exact1774 ↔
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      PEqualNP.TopForm.NoFourCycle G → NormalAt G := by
  constructor
  · intro h n G inst triangle square
    exact (step_iff_normal G).mp (h n G triangle square)
  · intro h n G inst triangle square
    exact (step_iff_normal G).mpr (h n G triangle square)

end PEqualNP.Outside.L_meta_1774

#print axioms PEqualNP.Outside.L_meta_1774.exact_iff_normal
#print axioms PEqualNP.Outside.L_meta_1774.step_of_deficient_cases
