import Bicyclic

namespace VertexPeel.Bicyclic

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.CoverPromise
  PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_1774
open VertexPeel.CoverCircuit

/-- Isolated inputs can be added in any number. Sparsity uses only nonisolated vertices. -/
theorem support_numerical {n : ℕ} (G : SimpleGraph (Fin n)) [d : DecidableRel G.Adj]
    (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v) (sq : NoFourCycle G)
    (leafless : ∀ v, G.degree v ≠ 1)
    (sparse : G.edgeFinset.card ≤ (CoverThreeCore.active G).card + 1) :
    StableExtension.Numerical G (Loc.tau G) := by
  intro inst C mono ok
  have same : inst = d := Subsingleton.elim _ _
  subst inst
  classical
  by_cases empty : ¬ ∃ a b, G.Adj a b
  · have emptyC : IsVertexCover G ∅ := fun a b ab => (empty ⟨a,b,ab⟩).elim
    have zero := Loc.tau_le G ∅ emptyC
    have edgeless : G.edgeFinset = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro e
      induction e using Sym2.inductionOn with
      | _ a b => exact fun h => empty ⟨a,b,G.mem_edgeFinset.mp h⟩
    simp [edgeless] at zero ⊢
    omega
  obtain ⟨a,b,ab⟩ := not_not.mp empty
  let A := CoverThreeCore.active G
  let m := A.card
  let p := A.equivFin.symm
  let f : Fin m ↪ Fin n := p.toEmbedding.trans (Function.Embedding.subtype _)
  let H := G.comap f
  have active' (v : Fin n) (hv : v ∈ A) : v ∈ Set.range f := by
    obtain ⟨i,eq⟩ := p.surjective ⟨v,hv⟩
    exact ⟨i,congrArg Subtype.val eq⟩
  have full (u v : Fin n) (e : G.Adj u v) : u ∈ Set.range f ∧ v ∈ Set.range f :=
    ⟨active' _ (CoverThreeCore.active_of_adj G e),active' _ (CoverThreeCore.active_of_adj G e.symm)⟩
  have mapG : H.map f = G := by
    apply le_antisymm (SimpleGraph.map_comap_le _ _)
    intro u v e
    obtain ⟨⟨x,rfl⟩,⟨y,rfl⟩⟩ := full u v e
    exact (SimpleGraph.map_adj f _ _ _).mpr ⟨x,y,e,rfl,rfl⟩
  obtain ⟨a',_⟩ := (full a b ab).1
  have : Nonempty (Fin m) := ⟨a'⟩
  have card : H.edgeFinset.card = G.edgeFinset.card := by
    calc H.edgeFinset.card = H.edgeSet.ncard := by rw [← SimpleGraph.coe_edgeFinset,Set.ncard_coe_finset]
         _ = (H.map f).edgeSet.ncard := by rw [SimpleGraph.edgeSet_map,Set.ncard_image_of_injective _ f.sym2Map.injective]
         _ = G.edgeSet.ncard := congrArg (fun J => J.edgeSet.ncard) mapG
         _ = G.edgeFinset.card := by rw [← SimpleGraph.coe_edgeFinset,Set.ncard_coe_finset]
  have deg (v : Fin m) : 2 ≤ H.degree v := by
    have positive : 0 < G.degree (f v) := (Finset.mem_filter.mp (p v).property).2
    have du : H.degree v = G.degree (f v) := by
      calc H.degree v = (H.neighborSet v).ncard := (H.ncard_neighborSet v).symm
           _ = ((H.map f).neighborSet (f v)).ncard := by rw [SimpleGraph.neighborSet_map,Set.ncard_image_of_injective _ f.injective]
           _ = (G.neighborSet (f v)).ncard := by rw [mapG]
           _ = G.degree (f v) := G.ncard_neighborSet _
    have := leafless (f v)
    omega
  obtain ⟨col,proper⟩ := bip
  have bipH : ∃ c : Fin m → Bool, ∀ u v, H.Adj u v → c u ≠ c v :=
    ⟨col ∘ f,fun u v uv => proper (f u) (f v) uv⟩
  have sqH : NoFourCycle H := by
    intro x y xy
    apply le_trans _ (sq (f x) (f y) (f.injective.ne xy))
    apply Finset.card_le_card_of_injOn f
    · intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hv).2⟩
    · exact f.injective.injOn
  have lo := @bipartite_numerical _ H _ bipH sqH deg (card ▸ sparse)
  obtain ⟨T,ct,sz⟩ := Loc.tau_attained H
  have cG : IsVertexCover G (T.map f) := by
    intro u v e
    obtain ⟨⟨x,rfl⟩,⟨y,rfl⟩⟩ := full _ _ e
    exact (ct x y e).imp (fun hx => Finset.mem_map.mpr ⟨x,hx,rfl⟩)
      (fun hy => Finset.mem_map.mpr ⟨y,hy,rfl⟩)
  have minG := Loc.tau_le _ _ cG
  rw [Finset.card_map,sz] at minG
  let emb : H ↪g G := ⟨f,Iff.rfl⟩
  have result := IsolatedCore.core_lower H G emb full (s := H.edgeFinset.card + Loc.tau H - 1)
    (fun D dm dc => by have := lo D dm dc; omega) C mono ok
  omega

/-- The same subclass permits the ownership exchange on a minimum circuit. -/
theorem support_ownership {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v) (sq : NoFourCycle G)
    (leafless : ∀ v, G.degree v ≠ 1)
    (sparse : G.edgeFinset.card ≤ (CoverThreeCore.active G).card + 1) : StepAt G := by
  intro C minimum correct _ positive
  obtain ⟨S,c,sc⟩ := Loc.tau_attained G
  have bound := support_numerical G bip sq leafless sparse C minimum.1 correct
  apply coveredDescent G C S c _ positive
  rw [Set.ncard_eq_toFinset_card']
  change G.edgeFinset.card + S.card - 1 ≤ C.size
  omega

/-- A single vertex supplies both savings bounds to every AO₂ circuit on the original inputs. -/
theorem support_vertex_deletion {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v) (sq : NoFourCycle G)
    (leafless : ∀ v, G.degree v ≠ 1) (sparse : G.edgeFinset.card ≤ (CoverThreeCore.active G).card + 1)
    (edges : 2 ≤ G.edgeFinset.card) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C →
      circuitFun n C = graphFun G ∅ → SavesAt G z C := by
  obtain ⟨z,hz,rem⟩ := nonemptyCut G edges
  obtain ⟨S,c,sc⟩ := Loc.tau_attained G
  refine ⟨z,hz,?_⟩
  intro C ao correct
  have mono : Monotone2 C := fun g hg =>
    ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ao.1 g hg,(ao.2.2 g hg).le⟩
  have bound := support_numerical G bip sq leafless sparse C mono correct
  exact atVertexOfCoverBound G z rem C ⟨S,c,by omega⟩

end VertexPeel.Bicyclic
#print axioms VertexPeel.Bicyclic.support_numerical
#print axioms VertexPeel.Bicyclic.support_ownership
#print axioms VertexPeel.Bicyclic.support_vertex_deletion
