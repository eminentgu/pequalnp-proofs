import PseudoforestAND

namespace VertexPeel.PivotAND
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.Core PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_1774 PEqualNP.MetaComplexity.CoverPromise
open VertexPeel.AndSeparation VertexPeel.RowGraph VertexPeel.RowCharge VertexPeel.CoverCircuit
variable {n : ℕ}

private theorem at_edge (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (ao : IsAO2 n C)
    (ok : circuitFun n C = graphFun G ∅) {y s : Fin n} (edge : G.Adj y s) :
    ∃ j, lit C y j ∧ wval C (unit y) (in0 C j) = wval C (unit s) (in1 C j) ∧
      wval C (unit y) (in1 C j) = wval C (unit s) (in0 C j) := by
  classical
  let z (i : Fin n) := decide (i=y ∨ i=s)
  have ev (a : Fin n → Bool) : wval C a C.output = graphFun G ∅ a := congrFun ok a
  have yes : ∃ u v, G.Adj u v ∧ z u = true ∧ z v = true := ⟨y,s,edge,by simp [z],by simp [z]⟩
  obtain ⟨j,_,hand,ne,sw,op⟩ := opposing_ancestor C ao (unit y) (unit s) z
    (fun i h => by rcases of_decide_eq_true h with rfl|rfl; exact Or.inl (by simp [unit]); exact Or.inr (by simp [unit]))
    C.output (by rw [ev]; simp [graphFun,unit]) (by rw [ev]; simp [graphFun,unit]) (by rw [ev]; simp [graphFun,yes])
  refine ⟨j,⟨hand,?_⟩,sw,op⟩
  rw [op]
  cases a : wval C (unit y) (in0 C j) <;> cases b : wval C (unit s) (in0 C j) <;> simp_all

/-- Along two consecutive edges with distinguishable endpoints, at least one of
those three singleton inputs lights more than one AND. No global deficit is needed. -/
theorem path_two_lit (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (ao : IsAO2 n C)
    (ok : circuitFun n C = graphFun G ∅) {a b c t : Fin n} (ab : G.Adj a b) (cb : G.Adj c b)
    (at' : G.Adj a t) (ct : ¬G.Adj c t) :
    ∃ x∈({a,b,c}:Finset _), ∃ i j, i≠j ∧ lit C x i ∧ lit C x j := by
  classical
  by_contra! unique
  have once {x : Fin n} (mem : x∈({a,b,c}:Finset _)) {i j : ℕ} (hi : lit C x i) (hj : lit C x j) : i=j := by
    by_contra ne; exact unique _ mem _ _ ne hi hj
  have bLit {x : Fin n} {j : ℕ} (h : lit C x j) (sw : wval C (unit x) (in0 C j) = wval C (unit b) (in1 C j))
      (os : wval C (unit x) (in1 C j) = wval C (unit b) (in0 C j)) : lit C b j :=
    ⟨h.1,h.2.elim (fun x0 => Or.inr (sw.symm.trans x0)) (fun x1 => Or.inl (os.symm.trans x1))⟩
  obtain ⟨i,ai,s0,s1⟩ := at_edge G C ao ok ab
  obtain ⟨j,cj,t0,t1⟩ := at_edge G C ao ok cb
  have eq := once (by simp : b∈({a,b,c}:Finset _)) (bLit ai s0 s1) (bLit cj t0 t1)
  subst j
  obtain ⟨k,ak,_,off0,off1⟩ := private_port G C ao ok at' ct
  have eq := once (by simp : a∈({a,b,c}:Finset _)) ai ak
  subst k
  rcases ai.2 with h|h
  · exact Bool.noConfusion ((t0.trans (s0.symm.trans h)).symm.trans (off0 h))
  · exact Bool.noConfusion ((t1.trans (s1.symm.trans h)).symm.trans (off1 h))

/-- On one color class the pigeonhole count uses whole AND gates: the opposite
ports of a gate cannot serve two different vertices having only one lit gate. -/
theorem two_lit_on_side (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (ao : IsAO2 n C)
    (ok : circuitFun n C = graphFun G ∅) (A : Finset (Fin n))
    (active : ∀ x∈A, ∃ t, G.Adj x t)
    (privateN : ∀ x∈A, ∀ y∈A, x ≠ y → ∃ t, G.Adj x t ∧ ¬G.Adj y t)
    (oppSide : ∀ x∈A, ∀ y∈A, ∀ t s, G.Adj x t → G.Adj y s → ¬G.Adj t s)
    (few : (physical C).card < A.card) : ∃ x∈A, ∃ i j, i ≠ j ∧ lit C x i ∧ lit C x j := by
  classical
  by_contra! unique
  have one (x : ↥A) : ∃ j, lit C x.val j := by
    obtain ⟨t,e⟩ := active x.val x.property
    obtain ⟨j,h,_⟩ := at_edge G C ao ok e
    exact ⟨j,h⟩
  choose J hit using one
  have only (x : A) {j : ℕ} (h : lit C x.val j) : j=J x := by
    by_contra ne
    exact unique x.val x.property _ _ ne h (hit x)
  let addr (x : A) : ↥(physical C) := ⟨J x,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hit x).1.1,(hit x).1⟩⟩
  have inj : Function.Injective addr := by
    intro x y eq
    by_contra ne
    have jj : J x=J y := congrArg Subtype.val eq
    obtain ⟨t,xt,yt⟩ := privateN x.val x.property y.val y.property (fun h => ne (Subtype.ext h))
    obtain ⟨j,jx,dx,off0,off1⟩ := private_port G C ao ok xt yt
    have je := only x jx
    obtain ⟨s,ys⟩ := active y.val y.property
    obtain ⟨k,ky,sw,os⟩ := at_edge G C ao ok ys
    have ke : k=j := ((only y ky).trans jj.symm).trans je.symm
    subst k
    obtain ⟨m,mx,_,out0,out1⟩ := private_port G C ao ok xt (oppSide y.val y.property x.val x.property s t ys xt)
    have me : m=j := (only x mx).trans je.symm
    subst m
    rcases jx.2 with left|right
    · have y0 := off0 left
      have s0 := out0 left
      exact ky.2.elim (fun h => Bool.noConfusion (h.symm.trans y0)) (fun h => Bool.noConfusion (h.symm.trans (os.trans s0)))
    · have y1 := off1 right
      have s1 := out1 right
      exact ky.2.elim (fun h => Bool.noConfusion (h.symm.trans (sw.trans s1))) (fun h => Bool.noConfusion (h.symm.trans y1))
  have bound := Fintype.card_le_of_injective addr inj
  simp at bound
  omega

/-- Any bipartite graph whose vertices on one side have degree at most two, with
arbitrary degrees on the other side and no global sparsity assumption. -/
theorem side_degree_two_and_lower (G : SimpleGraph (Fin n)) [base : DecidableRel G.Adj]
    (c : Fin n → Bool) (proper : ∀ u v, G.Adj u v → c u ≠ c v)
    (low : ∀ v, c v=false → G.degree v ≤ 2) (sq : NoFourCycle G)
    (C : Circuit) (ao : IsAO2 n C) (correct : circuitFun n C = graphFun G ∅) :
    Loc.tau G ≤ (physical C).card := by
  classical
  apply paid_induction G _ C ao correct
  intro H inst sub D dao dc few
  by_cases leaf : ∃ x, H.degree x=1
  · obtain ⟨x,d⟩ := leaf
    obtain ⟨t,xt⟩ := (H.degree_pos_iff_exists_adj x).mp (by omega)
    obtain ⟨j,hit,_⟩ := at_edge H D dao dc xt
    exact ⟨x,by omega,{j},by simp [d],fun i hi => (Finset.mem_singleton.mp hi) ▸ hit⟩
  let A := Finset.univ.filter (fun x => c x=false ∧ 0 < H.degree x)
  have enter {x y} (xy : H.Adj x y) (side : c x=false) : x∈A :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,side,(H.degree_pos_iff_exists_adj x).mpr ⟨y,xy⟩⟩
  have cover : IsVertexCover H A := by
    intro u v uv
    have diff := proper _ _ (sub uv)
    cases hu : c u with
    | false => exact Or.inl (enter uv hu)
    | true => exact Or.inr (enter uv.symm (by cases hv : c v <;> simp_all))
  have active (x : Fin n) (ha : x∈A) : ∃ t, H.Adj x t := (H.degree_pos_iff_exists_adj x).mp (Finset.mem_filter.mp ha).2.2
  have small (x : Fin n) (ha : x∈A) : H.degree x=2 := by
    have pair := (Finset.mem_filter.mp ha).2
    have upper := (H.degree_le_of_le sub).trans (low x pair.1)
    have ne : H.degree x≠1 := fun eq => leaf ⟨_,eq⟩
    omega
  have other {x t : Fin n} (h : x∈A) (xt : H.Adj x t) : c t = true := by
    have d := proper _ _ (sub xt)
    have h0 := (Finset.mem_filter.mp h).2.1
    cases ht : c t <;> simp_all
  obtain ⟨x,hx,i,j,ij,hi,hj⟩ := two_lit_on_side H D dao dc A active
    (fun x hx y _ ne => distinct_neighbors H (square_mono sub sq) x y ne (small x hx).ge)
    (fun _ hx _ hy _ _ xt ys e => proper _ _ (sub e) ((other hx xt).trans (other hy ys).symm))
    (few.trans_le (Loc.tau_le H A cover))
  refine ⟨x,by rw [small x hx]; decide,{i,j},by simp [ij,small x hx],?_⟩
  intro k hk
  rcases Finset.mem_insert.mp hk with rfl|hh
  · exact hi
  · exact (Finset.mem_singleton.mp hh) ▸ hj

#print axioms path_two_lit
#print axioms side_degree_two_and_lower
#print axioms two_lit_on_side
end VertexPeel.PivotAND
