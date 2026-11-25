import StableExtension
import Pendant
import ThreeGatePeel
import PEqualNP.MetaComplexity.Helpers.LocGraph
import PEqualNP.MetaComplexity.L104

namespace VertexPeel.ForestExtension

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.MetaComplexity.CoverPromise PEqualNP.TopForm PEqualNP.Outside.L_meta_1774
open StableExtension CoverCircuit

variable {n : ℕ}

/-- The two subgraphs have disjoint sets of incident vertices, on a common ambient type. -/
def Apart (H F : SimpleGraph (Fin n)) : Prop := ∀ a b c, H.Adj a b → F.Adj a c → False

private theorem at_forest {H F : SimpleGraph (Fin n)} (sep : Apart H F) {z w}
    (e : F.Adj z w) (v : Fin n) : (H ⊔ F).Adj z v ↔ F.Adj z v :=
  ⟨fun h => h.resolve_left (fun hv => sep z v w hv e), Or.inr⟩

private theorem delete_union {H F : SimpleGraph (Fin n)} (sep : Apart H F) {z w}
    (e : F.Adj z w) : (H ⊔ F).deleteIncidenceSet z = H ⊔ F.deleteIncidenceSet z := by
  ext u v
  simp only [SimpleGraph.deleteIncidenceSet_adj, SimpleGraph.sup_adj]
  constructor
  · rintro ⟨h|h,hu,hv⟩
    · exact Or.inl h
    · exact Or.inr ⟨h,hu,hv⟩
  · rintro (h|⟨h,hu,hv⟩)
    · exact ⟨Or.inl h,fun eq => sep z v w (eq ▸ h) e,fun eq => sep z u w (eq ▸ h.symm) e⟩
    · exact ⟨Or.inr h,hu,hv⟩

/-- Charge a peeled vertex against a sharp bound for its residual graph. -/
theorem lift_cut (G : SimpleGraph (Fin n)) [base : DecidableRel G.Adj] (z : Fin n)
    (cut : ∀ C, IsAO2 n C → circuitFun n C = graphFun G ∅ → SavesAt G z C)
    (old : Numerical (G.deleteIncidenceSet z) (Loc.tau (G.deleteIncidenceSet z))) :
    Numerical G (Loc.tau G) := by
  intro inst C mono correct
  have same : inst = base := Subsingleton.elim _ _
  subst inst
  classical
  obtain ⟨A,ao,ac,small⟩ : ∃ A : Circuit, IsAO2 n A ∧ circuitFun n A = graphFun G ∅ ∧ A.size ≤ C.size := by
    apply PEqualNP.Outside.L_meta_1527 n G base C mono
    intro x
    change circuitFun n C x = true ↔ _
    rw [correct]
    simp [graphFun]
  obtain ⟨D,dao,dev,save,bonus⟩ := cut A ao ac
  have dc : circuitFun n D = graphFun (G.deleteIncidenceSet z) ∅ := by
    rw [dev]
    funext x
    simp [graphFun,SimpleGraph.deleteIncidenceSet]
  have dmono : Monotone2 D := by
    intro g hg
    exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using dao.1 g hg,(dao.2.2 g hg).le⟩
  obtain ⟨S,cov,eq⟩ := Loc.tau_attained (G.deleteIncidenceSet z)
  have bound := old D dmono dc
  rw [← eq] at bound
  obtain ⟨T,tCov,tb⟩ := VertexPeel.charge G z S A.size D.size cov bound save bonus
  have minc := Loc.tau_le G T tCov
  omega

private theorem degree_one (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {a b : Fin n}
    (ab : G.Adj a b) (only : ∀ w, G.Adj a w → w = b) : G.degree a = 1 := by
  have pair : G.neighborFinset a = {b} := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_singleton]
    exact ⟨only w,fun e => e ▸ ab⟩
  rw [← G.card_neighborFinset_eq_degree,pair,Finset.card_singleton]

private theorem edge_card_inst (G : SimpleGraph (Fin n)) (i j : Fintype G.edgeSet) :
    (@SimpleGraph.edgeFinset _ G i).card = (@SimpleGraph.edgeFinset _ G j).card := by
  rw [Subsingleton.elim i j]

private theorem degree_inst (G : SimpleGraph (Fin n)) (v : Fin n) (i j : Fintype (G.neighborSet v)) :
    @SimpleGraph.degree _ G v i = @SimpleGraph.degree _ G v j := by
  rw [Subsingleton.elim i j]

private structure Sharp (G : SimpleGraph (Fin n)) : Prop where
  bound : Numerical G (Loc.tau G)

/-- A nonempty forest component supplies a valid vertex for all circuits,
even when the disjoint core is an arbitrary graph with an edge. -/
theorem peel_in_forest (H F : SimpleGraph (Fin n)) [DecidableRel (H ⊔ F).Adj]
    (core : ∃ a b, H.Adj a b) (sep : Apart H F) (acyc : F.IsAcyclic)
    (present : ∃ a b, F.Adj a b) :
    ∃ z w, F.Adj z w ∧ ∀ C : Circuit, IsAO2 n C →
      circuitFun n C = graphFun (H ⊔ F) ∅ → SavesAt (H ⊔ F) z C := by
  classical
  let G := H ⊔ F
  obtain ⟨l,p,lp,onlyL,shape⟩ := Helpers.Forest.forest_good_leaf F acyc present
  have leafEdge : G.Adj l p := Or.inr lp
  have only (w : Fin n) (e : G.Adj l w) := onlyL w ((at_forest sep lp w).mp e)
  obtain ⟨a,b,ab⟩ := core
  have survives {z w : Fin n} (zw : F.Adj z w) : ∃ u v, G.Adj u v ∧ u ≠ z ∧ v ≠ z :=
    ⟨a,b,Or.inl ab,fun eq => sep z b w (eq ▸ ab) zw,fun eq => sep z a w (eq ▸ ab.symm) zw⟩
  rcases shape with ⟨q,neighbors⟩ | ⟨s,sl,ps,onlyS⟩
  · by_cases other : ∃ q, F.Adj p q ∧ q ≠ l
    · obtain ⟨v,pv,vl⟩ := other
      have degree : G.degree p ≤ 2 := by
        have sub : G.neighborFinset p ⊆ {l,q} := by
          intro w hw
          have h := neighbors w ((at_forest sep lp.symm w).mp ((G.mem_neighborFinset _ _).mp hw))
          simpa using h
        have count := Finset.card_le_card sub
        have sizePair := Finset.card_insert_le l ({q} : Finset _)
        simp only [Finset.card_singleton] at sizePair
        simpa only [G.card_neighborFinset_eq_degree] using count.trans sizePair
      refine ⟨p,l,lp.symm,?_⟩
      intro C ao correct
      obtain ⟨D,dao,dc,save⟩ := ThreeGatePeel.cut_joint G C ao correct leafEdge (Or.inr pv) vl only (survives lp.symm)
      refine ⟨D,dao,dc.trans ?_,?_,?_⟩
      · funext x
        simp [G,graphFun,SimpleGraph.deleteIncidenceSet]
      · exact (Nat.add_le_add_left ((degree_inst G p _ _).trans_le degree) _).trans (by omega)
      · intro _
        exact (Nat.add_le_add_right (Nat.add_le_add_left ((degree_inst G p _ _).trans_le degree) _) 1).trans (by omega)
    · have onlyP (w : Fin n) (e : G.Adj p w) : w = l :=
        by_contra fun ne => other ⟨w,(at_forest sep lp.symm w).mp e,ne⟩
      have different : s(a,b) ≠ s(l,p) := by
        intro eq
        rcases Sym2.eq_iff.mp eq with ⟨ha,_⟩ | ⟨_,hb⟩
        · exact sep l b p (ha ▸ ab) lp
        · exact sep l a p (hb ▸ ab.symm) lp
      have many : 2 ≤ G.edgeFinset.card := Finset.one_lt_card.mpr
        ⟨s(a,b),by simpa using (show G.Adj a b from Or.inl ab),s(l,p),by simpa using leafEdge,different⟩
      exact ⟨l,p,lp,(Leaves.isolatedEdgeAt G l p leafEdge only onlyP (many.trans_eq (edge_card_inst _ _ _))).2⟩
  · have only' (w : Fin n) (e : G.Adj s w) := onlyS w ((at_forest sep ps.symm w).mp e)
    exact ⟨l,p,lp, Leaves.stableLeaf G l (degree_one G leafEdge only)
      (Leaves.sharedNeighborStable G l s p sl.symm leafEdge (Or.inr ps.symm) only only')⟩

private theorem with_core (H F : SimpleGraph (Fin n)) (core : ∃ a b, H.Adj a b)
    (bound : Numerical H (Loc.tau H)) (sep : Apart H F) (acyc : F.IsAcyclic) :
    Sharp (H ⊔ F) := by
  classical
  generalize size : F.edgeFinset.card = k
  induction k using Nat.strong_induction_on generalizing F with
  | ind k ih =>
    by_cases present : ∃ a b, F.Adj a b
    · let G := H ⊔ F
      obtain ⟨z,w,zw,cut⟩ := peel_in_forest H F core sep acyc present
      have residual {z w : Fin n} (zw : F.Adj z w) :
          Sharp (G.deleteIncidenceSet z) := by
        change Sharp ((H ⊔ F).deleteIncidenceSet z)
        rw [delete_union sep zw]
        have deg := (F.degree_pos_iff_exists_adj z).mpr ⟨w,zw⟩
        have pos : 0 < F.edgeFinset.card := Finset.card_pos.mpr ⟨s(z,w),by simpa using zw⟩
        have few : (F.deleteIncidenceSet z).edgeFinset.card < k := by
          rw [F.card_edgeFinset_deleteIncidenceSet]
          omega
        exact ih _ few _ (fun a b c h e => sep a b c h (F.deleteIncidenceSet_le z e))
          (SimpleGraph.IsAcyclic.anti (F.deleteIncidenceSet_le z) acyc) (edge_card_inst _ _ _)
      exact ⟨@lift_cut n G _ z cut (@Sharp.bound _ _ (residual zw))⟩
    · have empty : F = ⊥ := by ext x y; exact ⟨fun e => (present ⟨x,y,e⟩).elim,False.elim⟩
      subst F
      rw [sup_bot_eq]
      exact ⟨@bound⟩

/-- A forest satisfies the sharp edge-plus-cover lower bound, including the edgeless case. -/
theorem forest_numerical (F : SimpleGraph (Fin n)) (acyc : F.IsAcyclic) :
    Numerical F (Loc.tau F) := by
  intro inst C mono correct
  classical
  by_cases edge : ∃ a b, F.Adj a b
  · have fan : FanInTwo C := by
      intro g hg
      obtain ⟨op,arity⟩ := mono g hg
      refine ⟨?_,arity⟩
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢
      tauto
    have has : HasCircuitSize n (fun x : Fin n → Bool =>
        decide (∃ i j, F.Adj i j ∧ x i = true ∧ x j = true)) C.size := by
      refine ⟨C,fan,le_rfl,?_⟩
      intro x
      simpa [circuitFun,graphFun] using congrFun correct x
    have lo := PEqualNP.MetaComplexity.L104 n (Loc.tau F) C.size F acyc edge (Loc.tau_le F) has
    have count : F.edgeSet.ncard = F.edgeFinset.card := by
      rw [← SimpleGraph.coe_edgeFinset,Set.ncard_coe_finset]
    omega
  · have noEdges : F.edgeFinset = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e
      induction e using Sym2.ind with
      | _ a b => simpa using (show ¬ F.Adj a b from fun ab => edge ⟨a,b,ab⟩)
    have τ := Loc.tau_le F ∅ (fun a b e => (edge ⟨a,b,e⟩).elim)
    rw [noEdges,Finset.card_empty,zero_add]
    simp only [Finset.card_empty, Nat.le_zero] at τ
    omega

/-- Adding any vertex-disjoint forest preserves the sharp edge-plus-cover circuit bound.
The numbers of vertices, components and edges of the forest are unrestricted. -/
theorem add_forest (H F : SimpleGraph (Fin n)) (sep : Apart H F) (acyc : F.IsAcyclic)
    (bound : Numerical H (Loc.tau H)) : Numerical (H ⊔ F) (Loc.tau (H ⊔ F)) := by
  by_cases edge : ∃ a b, H.Adj a b
  · exact (with_core H F edge bound sep acyc).bound
  · have empty : H = ⊥ := by ext x y; exact ⟨fun e => (edge ⟨x,y,e⟩).elim,False.elim⟩
    subst H
    have sharp : Sharp (⊥ ⊔ F) := by
      rw [bot_sup_eq]
      exact ⟨@forest_numerical n F acyc⟩
    exact sharp.bound

/-- Card 3566 whenever some nontrivial component is a tree. The remainder of the
graph can have arbitrary cycles and arbitrary cover number. -/
theorem vertex_of_forest_component (H F : SimpleGraph (Fin n)) [DecidableRel (H ⊔ F).Adj]
    (sep : Apart H F) (acyc : F.IsAcyclic) (present : ∃ a b, F.Adj a b)
    (edges : 2 ≤ (H ⊔ F).edgeFinset.card) :
    ∃ z : Fin n, 0 < (H ⊔ F).degree z ∧ ∀ C : Circuit, IsAO2 n C →
      circuitFun n C = graphFun (H ⊔ F) ∅ → SavesAt (H ⊔ F) z C := by
  by_cases core : ∃ a b, H.Adj a b
  · obtain ⟨z,w,zw,cut⟩ := peel_in_forest H F core sep acyc present
    exact ⟨z,((H ⊔ F).degree_pos_iff_exists_adj z).mpr ⟨w,Or.inr zw⟩,cut⟩
  · have empty : H = ⊥ := by ext x y; exact ⟨fun e => (core ⟨x,y,e⟩).elim,False.elim⟩
    have allForest : (H ⊔ F).IsAcyclic := by rw [empty,bot_sup_eq]; exact acyc
    obtain ⟨z,zpos,rem⟩ := nonemptyCut (H ⊔ F) edges
    refine ⟨z,zpos,?_⟩
    intro C ao correct
    have mono : Monotone2 C := fun g hg =>
      ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ao.1 g hg,(ao.2.2 g hg).le⟩
    obtain ⟨T,c,count⟩ := Loc.tau_attained (H ⊔ F)
    have low := forest_numerical (H ⊔ F) allForest C mono correct
    exact atVertexOfCoverBound (H ⊔ F) z rem C ⟨T,c,by omega⟩

/-- Minimum cover size adds over the two vertex-disjoint pieces. -/
theorem tau_union (H F : SimpleGraph (Fin n)) (sep : Apart H F) :
    Loc.tau (H ⊔ F) = Loc.tau H + Loc.tau F := by
  classical
  apply Nat.le_antisymm
  · obtain ⟨A,ca,eqA⟩ := Loc.tau_attained H
    obtain ⟨B,cb,eqB⟩ := Loc.tau_attained F
    have cover : IsVertexCover (H ⊔ F) (A ∪ B) := by
      intro u v e
      rcases e with eh|ef
      · exact (ca u v eh).imp (Finset.mem_union_left B) (Finset.mem_union_left B)
      · exact (cb u v ef).imp (Finset.mem_union_right A) (Finset.mem_union_right A)
    have minimal := Loc.tau_le (H ⊔ F) (A ∪ B) cover
    have count := Finset.card_union_le A B
    omega
  · obtain ⟨T,cover,size⟩ := Loc.tau_attained (H ⊔ F)
    let active (v : Fin n) : Prop := ∃ w, H.Adj v w
    have ch : IsVertexCover H (T.filter active) := by
      intro u v e
      have hu : active u := ⟨v,e⟩
      have hv : active v := ⟨u,e.symm⟩
      exact (cover u v (Or.inl e)).imp (fun mem => Finset.mem_filter.mpr ⟨mem,hu⟩)
        (fun mem => Finset.mem_filter.mpr ⟨mem,hv⟩)
    have cf : IsVertexCover F (T.filter (fun v => ¬active v)) := by
      intro u v e
      have hu : ¬active u := fun ⟨w,h⟩ => sep u w v h e
      have hv : ¬active v := fun ⟨w,h⟩ => sep v w u h e.symm
      exact (cover u v (Or.inr e)).imp (fun mem => Finset.mem_filter.mpr ⟨mem,hu⟩)
        (fun mem => Finset.mem_filter.mpr ⟨mem,hv⟩)
    have ha := Loc.tau_le H _ ch
    have hb := Loc.tau_le F _ cf
    have split := Finset.card_filter_add_card_filter_not (s := T) active
    omega

end VertexPeel.ForestExtension

#print axioms VertexPeel.ForestExtension.peel_in_forest
#print axioms VertexPeel.ForestExtension.add_forest
#print axioms VertexPeel.ForestExtension.tau_union

#print axioms VertexPeel.ForestExtension.vertex_of_forest_component
