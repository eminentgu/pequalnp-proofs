import PivotDistinct
import PendantFeedbackSet
import MixedFoldAnd

namespace VertexPeel.PivotAND
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.Core PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_1774 PEqualNP.MetaComplexity.CoverPromise
open VertexPeel.AndSeparation VertexPeel.RowGraph VertexPeel.RowCharge VertexPeel.CoverCircuit
open VertexPeel.OrderedMatching
variable {n : ℕ}

/-- Splitting the active vertices across a bipartition gives two covers. -/
theorem double_cover_le_active (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v) : 2 * Loc.tau G ≤ (CoverThreeCore.active G).card := by
  classical
  obtain ⟨c,proper⟩ := bip
  let A := CoverThreeCore.active G
  have covers (b : Bool) : IsVertexCover G (A.filter fun v => c v=b) := by
    intro u v uv
    have hu : u∈A := CoverThreeCore.active_of_adj G uv
    have hv : v∈A := CoverThreeCore.active_of_adj G uv.symm
    have diff := proper u v uv
    cases p : c u <;> cases q : c v <;> cases b <;> simp_all
  have h1 := Loc.tau_le G _ (covers true)
  have h2 := Loc.tau_le G _ (covers false)
  have ca := Finset.card_filter_add_card_filter_not (s:=A) (p:=fun v => c v=true)
  simp only [Bool.not_eq_true] at ca
  change 2*Loc.tau G ≤ A.card
  omega

theorem distinct_neighbors (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (sq : NoFourCycle G)
    (x y : Fin n) (ne : x≠y) (degree : 2 ≤ G.degree x) : ∃ t, G.Adj x t ∧ ¬G.Adj y t := by
  classical
  by_contra! none
  have sub : G.neighborFinset x ⊆ Finset.univ.filter (fun t => G.Adj x t ∧ G.Adj y t) := by
    intro t ht
    have e := (G.mem_neighborFinset _ _).mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,e,none t e⟩
  have count := (Finset.card_le_card sub).trans (sq x y ne)
  rw [G.card_neighborFinset_eq_degree] at count
  omega

/-- Under a strict AND deficit, some active vertex lights at least as many
distinct physical AND gates as it has neighbors. -/
theorem paid_vertex (G : SimpleGraph (Fin n)) [base : DecidableRel G.Adj] (C : Circuit) (ao : IsAO2 n C)
    (correct : circuitFun n C = graphFun G ∅) (sp : Pseudoforest.Sparse G)
    (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v) (sq : NoFourCycle G)
    (few : (physical C).card < Loc.tau G) : ∃ x, 0 < G.degree x ∧
      ∃ L : Finset ℕ, G.degree x ≤ L.card ∧ ∀ j∈L, lit C x j := by
  classical
  by_cases leaf : ∃ x, G.degree x=1
  · obtain ⟨x,d⟩ := leaf
    obtain ⟨t,xt⟩ := (G.degree_pos_iff_exists_adj x).mp (by omega)
    obtain ⟨j,hit,_⟩ := private_port G C ao correct xt (G.loopless.irrefl t)
    exact ⟨x,by omega,{j},by simp [d],fun i hi => (Finset.mem_singleton.mp hi) ▸ hit⟩
  let A := CoverThreeCore.active G
  have active (x : Fin n) (h : x∈A) : ∃ t, G.Adj x t :=
    (G.degree_pos_iff_exists_adj x).mp (Finset.mem_filter.mp h).2
  have d (x : Fin n) (h : x∈A) : G.degree x=2 := by
    have raw := GraphInduction599.regular_of_no_leaf G sp (fun y eq => leaf ⟨y,by convert eq using 1; congr 1; apply Subsingleton.elim⟩) x (active x h)
    convert raw using 1; congr 1; apply Subsingleton.elim
  have low := double_cover_le_active G bip
  obtain ⟨x,hx,i,j,ij,hi,hj⟩ := two_lit G C ao correct A active
    (fun x hx y _ ne => distinct_neighbors G sq x y ne (d x hx).ge) (by change 2*(physical C).card < (CoverThreeCore.active G).card; omega)
  refine ⟨x,by rw [d x hx]; decide,{i,j},by simp [ij,d x hx],?_⟩
  intro k hk
  rcases Finset.mem_insert.mp hk with rfl|hh
  · exact hi
  · exact (Finset.mem_singleton.mp hh) ▸ hj

theorem square_mono {G H : SimpleGraph (Fin n)} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (sub : H ≤ G) (sq : NoFourCycle G) : NoFourCycle H := by
  intro a b ne
  apply le_trans (Finset.card_le_card ?_) (sq a b ne)
  intro u hu
  obtain ⟨_,au,bu⟩ := Finset.mem_filter.mp hu
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,sub au,sub bu⟩

/-- Adding a cut vertex set to any cover of the residual graph covers the original graph. -/
theorem cover_cutSet (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    Loc.tau G ≤ Loc.tau (cutSet G S) + S.card := by
  classical
  obtain ⟨T,hT,card⟩ := Loc.tau_attained (cutSet G S)
  have cov : IsVertexCover G (T ∪ S) := by
    intro a b e
    by_cases au : a∈S
    · exact Or.inl (Finset.mem_union_right _ au)
    by_cases bu : b∈S
    · exact Or.inr (Finset.mem_union_right _ bu)
    exact (hT a b ⟨e,au,bu⟩).imp (Finset.mem_union_left _) (Finset.mem_union_left _)
  have bound := (Loc.tau_le G _ cov).trans (Finset.card_union_le _ _)
  omega

/-- Fix the pivot to one and every neighbor to zero. -/
def setPivot (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n) (a : Fin n → Bool) (v : Fin n) : Bool :=
  if v=x then true else if G.Adj x v then false else a v

theorem pivot_eval (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n)
    [DecidableRel (cutSet G (G.neighborFinset x)).Adj] (a : Fin n → Bool) :
    graphFun G ∅ (setPivot G x a) = graphFun (cutSet G (G.neighborFinset x)) ∅ a := by
  classical
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false]
  apply congrArg _
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨u,v,e,hu,hv⟩
    have cold (z : Fin n) (hz : setPivot G x a z=true) : ¬G.Adj x z := by
      intro ez; simp [setPivot,ez,ez.ne.symm] at hz
    have ux : u ≠ x := fun eq => cold v hv (eq ▸ e)
    have vx : v ≠ x := fun eq => cold u hu (eq ▸ e.symm)
    exact ⟨u,v,⟨e,by simpa using cold u hu,by simpa using cold v hv⟩,by simpa [setPivot,ux,cold u hu] using hu,by simpa [setPivot,vx,cold v hv] using hv⟩
  · rintro ⟨u,v,⟨e,nu,nv⟩,hu,hv⟩
    have ux : u ≠ x := fun eq => nv ((G.mem_neighborFinset _ _).mpr (eq ▸ e))
    have vx : v ≠ x := fun eq => nu ((G.mem_neighborFinset _ _).mpr (eq ▸ e.symm))
    exact ⟨u,v,e,by simpa [setPivot,ux,show ¬G.Adj x u from fun t => nu ((G.mem_neighborFinset _ _).mpr t)] using hu,
      by simpa [setPivot,vx,show ¬G.Adj x v from fun t => nv ((G.mem_neighborFinset _ _).mpr t)] using hv⟩

private theorem card_irrel (G : SimpleGraph (Fin n)) (i j : Fintype G.edgeSet) :
    (@SimpleGraph.edgeFinset _ G i).card = (@SimpleGraph.edgeFinset _ G j).card := by rw [Subsingleton.elim i j]

/-- A fixed error budget is carried through every restriction. A pivot need
only be supplied when the deficit exceeds this one global budget. -/
theorem paid_induction_offset (G : SimpleGraph (Fin n)) [base : DecidableRel G.Adj] (offset : Nat)
    (pay : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj], H ≤ G → ∀ (D : Circuit), IsAO2 n D →
      circuitFun n D = graphFun H ∅ → (physical D).card + offset < Loc.tau H → ∃ x, 0 < H.degree x ∧
      ∃ L : Finset ℕ, H.degree x ≤ L.card ∧ ∀ j∈L, lit D x j)
    (C : Circuit) (ao : IsAO2 n C) (correct : circuitFun n C = graphFun G ∅) : Loc.tau G ≤ (physical C).card + offset := by
  classical
  generalize size : G.edgeFinset.card = k
  induction k using Nat.strong_induction_on generalizing G C with
  | ind k ih =>
    by_contra! few
    obtain ⟨x,pos,L,charge,on⟩ := pay G le_rfl C ao correct few
    let S := G.neighborFinset x
    let H := cutSet G S
    have sub : H ≤ G := fun _ _ h => h.1
    obtain ⟨t,xt⟩ := (G.degree_pos_iff_exists_adj x).mp pos
    have strict : H < G := lt_of_le_of_ne sub (by
      intro eq
      have gone : ¬H.Adj x t := fun h => h.2.2 ((G.mem_neighborFinset _ _).mpr xt)
      exact gone (eq ▸ xt))
    have small : H.edgeFinset.card < k := (Finset.card_lt_card (SimpleGraph.edgeFinset_strict_mono strict)).trans_eq size
    have bound := cover_cutSet G S
    have budget : S.card ≤ L.card := charge
    by_cases rem : ∃ a b, H.Adj a b
    · let r := setPivot G x
      have raw (i : Fin n) : MixedFold.Const (MixedFold.val C r i.val) ∨ MixedFold.val C r i.val = fun z => z i := by
        have ev (z : Fin n → Bool) : MixedFold.val C r i.val z = r z i := ZeroFold.wval_in C (r z) i
        by_cases ix : i=x
        · exact Or.inl ⟨true,funext fun z => (ev z).trans (by simp [r,setPivot,ix])⟩
        by_cases adj : G.Adj x i
        · exact Or.inl ⟨false,funext fun z => (ev z).trans (by simp [r,setPivot,ix,adj])⟩
        exact Or.inr (funext fun z => (ev z).trans (by simp [r,setPivot,ix,adj]))
      have ev : MixedFold.val C r C.output = graphFun H ∅ := by
        funext z
        exact (congrFun correct (r z)).trans (pivot_eval G x z)
      have vari : ¬MixedFold.Const (MixedFold.val C r C.output) := by
        obtain ⟨a,b,ab⟩ := rem
        rintro ⟨q,eq⟩
        have yes : graphFun H ∅ (fun _ => true) = true := by simpa [graphFun] using (show ∃ u v, H.Adj u v from ⟨a,b,ab⟩)
        have no : graphFun H ∅ (fun _ => false) = false := by simp [graphFun]
        rw [←ev,eq] at yes no
        exact Bool.noConfusion (yes.symm.trans no)
      obtain ⟨D,dao,dc,save⟩ := compile_lit C ao r raw vari x (fun _ => by simp [r,setPivot]) L on
      have lower := ih H.edgeFinset.card small H (fun K _ h => pay K (h.trans sub)) D dao (dc.trans ev) (card_irrel _ _ _)
      change Loc.tau G ≤ Loc.tau H + S.card at bound
      omega
    · have cov : IsVertexCover H ∅ := fun u v uv => (rem ⟨u,v,uv⟩).elim
      have zero := Loc.tau_le H ∅ cov
      have incl : L ⊆ physical C := fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (on _ hj).1.1,(on _ hj).1⟩
      have num := Finset.card_le_card incl
      change Loc.tau G ≤ Loc.tau H + S.card at bound
      simp only [Finset.card_empty] at zero
      omega

/-- A paid pivot in each deficient realization of each subgraph yields the global AND bound. -/
theorem paid_induction (G : SimpleGraph (Fin n)) [base : DecidableRel G.Adj]
    (pay : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj], H ≤ G → ∀ (D : Circuit), IsAO2 n D →
      circuitFun n D = graphFun H ∅ → (physical D).card < Loc.tau H → ∃ x, 0 < H.degree x ∧
      ∃ L : Finset ℕ, H.degree x ≤ L.card ∧ ∀ j∈L, lit D x j)
    (C : Circuit) (ao : IsAO2 n C) (correct : circuitFun n C = graphFun G ∅) : Loc.tau G ≤ (physical C).card := by
  apply (Nat.add_zero (physical C).card) ▸ paid_induction_offset G 0 _ C ao correct
  intro H inst sub D dao eval short
  exact pay H sub D dao eval (by simpa using short)

/-- The entire sparse class, with arbitrarily many disconnected cycle components and isolated inputs. -/
theorem pseudoforest_and_lower (G : SimpleGraph (Fin n)) [base : DecidableRel G.Adj] (sp : Pseudoforest.Sparse G)
    (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v) (sq : NoFourCycle G)
    (C : Circuit) (ao : IsAO2 n C) (correct : circuitFun n C = graphFun G ∅) : Loc.tau G ≤ (physical C).card := by
  apply paid_induction G _ C ao correct
  intro H inst sub D dao dc few
  obtain ⟨c,col⟩ := bip
  exact paid_vertex H D dao dc (GraphInduction599.sparse_subgraph sub sp)
    ⟨c,fun u v e => col _ _ (sub e)⟩ (square_mono sub sq) few

/-- Combine a bound on physical ANDs with the OR bound of L-meta-599. -/
theorem numerical_from_ands (G : SimpleGraph (Fin n)) [base : DecidableRel G.Adj] (sp : Pseudoforest.Sparse G)
    (sq : NoFourCycle G) (andLower : ∀ E : Circuit, IsAO2 n E → circuitFun n E = graphFun G ∅ →
      Loc.tau G ≤ (physical E).card) : StableExtension.Numerical G (Loc.tau G) := by
  intro inst C mono ok
  have eq : inst=base := Subsingleton.elim _ _
  subst inst
  classical
  have zero : circuitFun n C (fun _ => false) = false := (congrFun ok _).trans (by simp [graphFun])
  obtain ⟨E,ao,smaller,same⟩ := PEqualNP.Outside.L_meta_4342 n C mono zero
  have ec := same.trans ok
  have andBound := andLower E ao ec
  let rest := Finset.range E.size \ physical E
  have reads (j : ℕ) (g : Gate) (atj : E.gates[j]? = some g) (hor : g.op = .or) : j ∈ rest := by
    obtain ⟨hj,rfl⟩ := List.getElem?_eq_some_iff.mp atj
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hj,?_⟩
    intro h
    have hand := (Finset.mem_filter.mp (show j∈physical E from h)).2.2
    simp [gateAt,hj,hor] at hand
  have em : Monotone2 E := fun g hg =>
    ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ao.1 g hg,(ao.2.2 g hg).le⟩
  have ev (x : Fin n → Bool) : E.eval (List.ofFn x) = true ↔ ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true := by
    have h := congrFun ec x
    change E.eval (List.ofFn x) = graphFun G ∅ x at h
    simp [h,graphFun]
  have orBound := PEqualNP.Outside.L_meta_599 n G E rest sp (Pseudoforest.no_four_walk G sq) em ev reads
  have edges : G.edgeSet.ncard = G.edgeFinset.card := by rw [← SimpleGraph.coe_edgeFinset,Set.ncard_coe_finset]
  have budget : rest.card + (physical E).card = E.size :=
    (Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)).trans (Finset.card_range _)
  omega

/-- On every square-free bipartite pseudoforest, AND gates pay for a minimum cover and
OR gates pay for all but one edge. -/
theorem pseudoforest_numerical (G : SimpleGraph (Fin n)) [base : DecidableRel G.Adj] (sp : Pseudoforest.Sparse G)
    (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v) (sq : NoFourCycle G) :
    StableExtension.Numerical G (Loc.tau G) := by
  exact @numerical_from_ands n G base sp sq (pseudoforest_and_lower G sp bip sq)

/-- Ownership descent with no component count or cover-number bound. -/
theorem pseudoforest_ownership (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (sp : Pseudoforest.Sparse G)
    (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v) (sq : NoFourCycle G) : StepAt G := by
  intro C minimum correct _ positive
  obtain ⟨S,cover,card⟩ := Loc.tau_attained G
  have bound := pseudoforest_numerical G sp bip sq C minimum.1 correct
  apply coveredDescent G C S cover _ positive
  rw [Set.ncard_eq_toFinset_card']
  change G.edgeFinset.card + S.card - 1 ≤ C.size
  omega

/-- One vertex works for every realization and for both requested deletion budgets. -/
theorem pseudoforest_vertex (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (sp : Pseudoforest.Sparse G)
    (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v) (sq : NoFourCycle G) (many : 2 ≤ G.edgeFinset.card) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C → circuitFun n C = graphFun G ∅ → SavesAt G z C := by
  obtain ⟨z,hz,rem⟩ := nonemptyCut G many
  obtain ⟨S,cover,card⟩ := Loc.tau_attained G
  refine ⟨z,hz,?_⟩
  intro C ao correct
  have mono : Monotone2 C := fun g hg =>
    ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ao.1 g hg,(ao.2.2 g hg).le⟩
  have bound := pseudoforest_numerical G sp bip sq C mono correct
  exact atVertexOfCoverBound G z rem C ⟨S,cover,by omega⟩

#print axioms pseudoforest_numerical
#print axioms pseudoforest_ownership
#print axioms pseudoforest_vertex
#print axioms paid_induction
#print axioms paid_vertex
#print axioms pivot_eval
#print axioms pseudoforest_and_lower
end VertexPeel.PivotAND
