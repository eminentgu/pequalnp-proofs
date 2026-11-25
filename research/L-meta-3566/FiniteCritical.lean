import CriticalSupport
import IsolatedCore
import CoverThreeCore

namespace VertexPeel.FiniteCritical

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.CoverPromise PEqualNP.TopForm
open VertexPeel.CoverKernel VertexPeel.CriticalSupport VertexPeel.CoverThreeCore

private theorem full_map {m n : ℕ} {G : SimpleGraph (Fin n)} (f : Fin m ↪ Fin n)
    (full : ∀ a b, G.Adj a b → a ∈ Set.range f ∧ b ∈ Set.range f) :
    (G.comap f).map f = G := by
  apply le_antisymm (SimpleGraph.map_comap_le _ _)
  intro a b edge
  obtain ⟨⟨u,rfl⟩,⟨v,rfl⟩⟩ := full a b edge
  exact (SimpleGraph.map_adj f _ _ _).mpr ⟨u,v,edge,rfl,rfl⟩

private theorem tau_full {m n : ℕ} {G : SimpleGraph (Fin n)} (f : Fin m ↪ Fin n)
    (full : ∀ a b, G.Adj a b → a ∈ Set.range f ∧ b ∈ Set.range f) :
    Loc.tau (G.comap f) = Loc.tau G := by
  classical
  apply Nat.le_antisymm
  · obtain ⟨T,c,s⟩ := Loc.tau_attained G
    let U := Finset.univ.filter fun i => f i ∈ T
    have within : U.map f ⊆ T := by
      intro v hv
      obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hv
      exact (Finset.mem_filter.mp hu).2
    have card : U.card ≤ T.card := by simpa using Finset.card_le_card within
    have cover : IsVertexCover (G.comap f) U := by
      intro a b edge
      simpa [U] using c _ _ edge
    exact (Loc.tau_le _ U cover).trans (s ▸ card)
  · obtain ⟨T,c,s⟩ := Loc.tau_attained (G.comap f)
    have cover : IsVertexCover G (T.map f) := by
      intro a b edge
      obtain ⟨⟨u,rfl⟩,⟨v,rfl⟩⟩ := full a b edge
      exact (c u v edge).imp (fun h => Finset.mem_map.mpr ⟨u,h,rfl⟩)
        (fun h => Finset.mem_map.mpr ⟨v,h,rfl⟩)
    simpa [← s] using Loc.tau_le _ _ cover

private theorem square_comap {m n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (f : Fin m ↪ Fin n) (sq : NoFourCycle G) : NoFourCycle (G.comap f) := by
  classical
  intro a b ne
  apply le_trans _ (sq (f a) (f b) (f.injective.ne ne))
  apply Finset.card_le_card_of_injOn f
  · intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩
  · exact f.injective.injOn

private theorem critical_comap {m n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (f : Fin m ↪ Fin n) (full : ∀ a b, G.Adj a b → a ∈ Set.range f ∧ b ∈ Set.range f)
    (hc : AllLeavesCritical G) : AllLeavesCritical (G.comap f) := by
  intro a deg
  obtain ⟨u,edge,only⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp deg
  have one : G.degree (f a) = 1 := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
    ⟨f u,edge,by
      intro v h
      obtain ⟨w,rfl⟩ := (full _ _ h).2
      exact congrArg f (only w h)⟩
  have fullCut : ∀ i j, (G.deleteIncidenceSet (f a)).Adj i j → i ∈ Set.range f ∧ j ∈ Set.range f :=
    fun i j e => full i j (G.deleteIncidenceSet_le _ e)
  have commute : (G.comap f).deleteIncidenceSet a = (G.deleteIncidenceSet (f a)).comap f := by
    ext i j
    simp [SimpleGraph.deleteIncidenceSet_adj, SimpleGraph.comap_adj, f.injective.eq_iff]
  rw [commute,tau_full f fullCut,tau_full f full]
  exact hc _ one

/-- The numerical lower bound only needs finitely many graph orders at each fixed t.
The minimum cover, degree-one criticality and both forbidden-cycle conditions survive
removing isolated vertices; circuit size is preserved by the retraction. -/
theorem of_small_order {n t : ℕ} (G : SimpleGraph (Fin n)) [base : DecidableRel G.Adj]
    (tri : NoTriangles G) (sq : NoFourCycle G) (size : Loc.tau G = t) (big : 3 ≤ t)
    (small : ∀ m, m ≤ t + t.choose 2 → ∀ (H : SimpleGraph (Fin m)) [DecidableRel H.Adj],
      NoTriangles H → NoFourCycle H → Loc.tau H = t → AllLeavesCritical H →
      (∀ a, 0 < H.degree a) → StableExtension.Numerical H t) :
    StableExtension.Numerical G t := by
  rw [← size]
  intro dec D dm dc
  have instEq : dec = base := Subsingleton.elim _ _
  subst dec
  apply of_critical G (fun J => NoTriangles J ∧ Loc.tau J = t) _ _ ⟨tri,size⟩ sq (size ▸ big) D dm dc
  · intro J a _ prop _ _ same
    exact ⟨fun i j k ij jk ki => prop.1 i j k (J.deleteIncidenceSet_le a ij)
      (J.deleteIncidenceSet_le a jk) (J.deleteIncidenceSet_le a ki), same.trans prop.2⟩
  · intro J decJ prop sqJ hc bound inst C mono correct
    have eq : inst = decJ := Subsingleton.elim _ _
    subst inst
    let A := CoverKernel.active J
    let m := A.card
    let p := A.equivFin.symm
    let f : Fin m ↪ Fin n := p.toEmbedding.trans (Function.Embedding.subtype _)
    have inA (v) (h : v ∈ A) : v ∈ Set.range f := by
      obtain ⟨i,hi⟩ := p.surjective ⟨v,h⟩
      exact ⟨i,congrArg Subtype.val hi⟩
    have full : ∀ a b, J.Adj a b → a ∈ Set.range f ∧ b ∈ Set.range f := by
      intro a b edge
      exact ⟨inA a (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(J.degree_pos_iff_exists_adj a).mpr ⟨b,edge⟩⟩),
        inA b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(J.degree_pos_iff_exists_adj b).mpr ⟨a,edge.symm⟩⟩)⟩
    let H := J.comap f
    have activeH (a : Fin m) : 0 < H.degree a := by
      obtain ⟨v,e⟩ := (J.degree_pos_iff_exists_adj _).mp (Finset.mem_filter.mp (p a).property).2
      obtain ⟨u,rfl⟩ := (full _ _ e).2
      exact (H.degree_pos_iff_exists_adj a).mpr ⟨u,e⟩
    have tauH : Loc.tau H = t := (tau_full f full).trans prop.2
    have U : IsVertexCover H Finset.univ := fun _ _ _ => Or.inl (Finset.mem_univ _)
    have hpos := Loc.tau_le H _ U
    rw [tauH,Finset.card_univ,Fintype.card_fin] at hpos
    have : Nonempty (Fin m) := ⟨⟨0,by omega⟩⟩
    have domains : m ≤ t + t.choose 2 := by simpa [m,A,prop.2] using bound
    have lo := small m domains H (fun i j k ab bc ca => prop.1 (f i) (f j) (f k) ab bc ca)
      (square_comap f sqJ) tauH (critical_comap f full hc) activeH
    let emb : H ↪g J := ⟨f, Iff.rfl⟩
    have sizeH := IsolatedCore.core_lower H J emb full (s := H.edgeFinset.card + t - 1)
      (fun D dm dc => by have := lo D dm dc; omega) C mono correct
    have cardEq : H.edgeFinset.card = J.edgeFinset.card := by
      classical
      have heq : H.map f = J := full_map f full
      have counts (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] : K.edgeSet.ncard = K.edgeFinset.card := by
        rw [← SimpleGraph.coe_edgeFinset,Set.ncard_coe_finset]
      calc H.edgeFinset.card = H.edgeSet.ncard := by rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
           _ = (H.map f).edgeSet.ncard := by rw [SimpleGraph.edgeSet_map,Set.ncard_image_of_injective _ f.sym2Map.injective]
           _ = J.edgeSet.ncard := congrArg (fun K : SimpleGraph (Fin n) => K.edgeSet.ncard) heq
           _ = J.edgeFinset.card := counts _
    rw [prop.2]
    omega

#print axioms of_small_order
end VertexPeel.FiniteCritical
