import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace VertexPeel.CoverThreeCore
open PEqualNP.TopForm PEqualNP.MetaComplexity.CoverPromise SimpleGraph

variable {n : ℕ}
abbrev NoTriangles (G : SimpleGraph (Fin n)) : Prop :=
  ∀ x y z, G.Adj x y → G.Adj y z → ¬ G.Adj z x

def active (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Finset (Fin n) :=
  Finset.univ.filter fun v => 0 < G.degree v

theorem active_of_adj (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {u v} (e : G.Adj u v) :
    u ∈ active G := by simp [active,(G.degree_pos_iff_exists_adj u).mpr ⟨v,e⟩]

private theorem four (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (sq : NoFourCycle G)
    {x y p q : Fin n} (xy : x≠y) (pq : p≠q)
    (xp : G.Adj x p) (xq : G.Adj x q) (yp : G.Adj y p) (yq : G.Adj y q) : False := by
  exact pq (Finset.card_le_one.mp (sq x y xy) p (by simp [xp,yp]) q (by simp [xq,yq]))

/-- Outside a three-vertex cover each active vertex needs a different
    unordered pair of cover vertices if there are no leaves or four-cycles. -/
theorem support_le_six (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (sq : NoFourCycle G)
    (noLeaf : ∀ u, G.degree u≠1) (K : Finset (Fin n)) (cover : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G K)
    (small : K.card ≤ 3) : (active G).card ≤ 6 := by
  classical
  let S := active G \ K
  have pick (v : Fin n) (hv : v∈S) : ∃ P ⊆ G.neighborFinset v, P.card=2 := by
    obtain ⟨h,_⟩ := Finset.mem_sdiff.mp hv
    have positive : 0<G.degree v := (Finset.mem_filter.mp h).2
    apply Finset.exists_subset_card_eq
    change 2 ≤ G.degree v
    have ne := noLeaf v
    omega
  let f (v : Fin n) := if hv : v∈S then (pick v hv).choose else ∅
  have prop (v : Fin n) (hv : v∈S) : f v ⊆ G.neighborFinset v ∧ (f v).card=2 := by
    simpa [f,hv] using (pick v hv).choose_spec
  have bound : S.card ≤ (K.powersetCard 2).card := by
    apply Finset.card_le_card_of_injOn f
    · intro v hv
      have h := prop v hv
      refine Finset.mem_powersetCard.mpr ⟨?_,h.2⟩
      intro u hu
      exact (cover v u ((G.mem_neighborFinset _ _).mp (h.1 hu))).resolve_left (Finset.mem_sdiff.mp hv).2
    · intro x hx y hy eq
      by_contra ne
      have xp := prop x hx
      have yp := prop y hy
      obtain ⟨p,hp,q,hq,pq⟩ := Finset.one_lt_card.mp (by omega : 1 < (f x).card)
      exact four G sq ne pq ((G.mem_neighborFinset _ _).mp (xp.1 hp))
        ((G.mem_neighborFinset _ _).mp (xp.1 hq)) ((G.mem_neighborFinset _ _).mp (yp.1 (eq ▸ hp)))
        ((G.mem_neighborFinset _ _).mp (yp.1 (eq ▸ hq)))
  have sub : active G ⊆ S ∪ K := by
    intro v hv
    by_cases k : v∈K
    · exact Finset.mem_union_right _ k
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hv,k⟩)
  have tot := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  rw [Finset.card_powersetCard] at bound
  have cnt : K.card.choose 2 ≤ 3 := (Nat.choose_le_choose 2 small).trans (by decide)
  omega

/-- A branching vertex in a triangle- and four-cycle-free leafless graph
    forces at least seven active vertices within distance two. -/
theorem degree_le_two (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (tri : NoTriangles G)
    (sq : NoFourCycle G) (noLeaf : ∀ u, G.degree u≠1) (small : (active G).card ≤ 6)
    (w : Fin n) : G.degree w ≤ 2 := by
  classical
  let N := G.neighborFinset w
  have child (u : Fin n) (h : u ∈ N) : ∃ t, G.Adj u t ∧ t≠w := by
    have a := (G.mem_neighborFinset _ _).mp h
    have pos := (G.degree_pos_iff_exists_adj u).mpr ⟨w,a.symm⟩
    have deg : 1 < (G.neighborFinset u).card := by change 1<G.degree u; have := noLeaf u; omega
    obtain ⟨t,tb,ne⟩ := Finset.exists_mem_ne deg w
    exact ⟨t,(G.mem_neighborFinset _ _).mp tb,ne⟩
  let f (u : Fin n) := if h : u∈N then (child u h).choose else w
  have fp (u : Fin n) (h : u∈N) : G.Adj u (f u) ∧ f u≠w := by
    simpa [f,h] using (child u h).choose_spec
  have inj : (N : Set (Fin n)).InjOn f := by
    intro x hx y hy eq
    by_contra xy
    have xf := fp x hx
    have yf := fp y hy
    exact four G sq xy xf.2 xf.1 ((G.mem_neighborFinset _ _).mp hx).symm
      (eq ▸ yf.1) ((G.mem_neighborFinset _ _).mp hy).symm
  let T := N.image f
  have diff : Disjoint N T := Finset.disjoint_left.mpr (by
    intro t ht img
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp img
    exact tri w u _ ((G.mem_neighborFinset _ _).mp hu) (fp u hu).1 ((G.mem_neighborFinset _ _).mp ht).symm)
  have wn : w∉N := by simp [N]
  have wt : w∉T := by
    intro h
    obtain ⟨u,du,eq⟩ := Finset.mem_image.mp h
    exact (fp u du).2 eq
  by_contra! big
  have sub : insert w (N∪T) ⊆ active G := by
    intro t ht
    rcases Finset.mem_insert.mp ht with e|h
    · exact e ▸ (by simp [active,show 0<G.degree w by omega])
    rcases Finset.mem_union.mp h with hn | hi
    · exact active_of_adj G ((G.mem_neighborFinset _ _).mp hn).symm
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hi
    exact active_of_adj G (fp u hu).1.symm
  have ineq := Finset.card_le_card sub
  have ct : T.card=N.card := Finset.card_image_of_injOn inj
  simp [wn,wt,Finset.card_union_of_disjoint diff,ct] at ineq
  change 2 < N.card at big
  omega


abbrev CoreCycle (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  ∃ f : Fin k → Fin n, Function.Injective f ∧
    (∀ i j, G.Adj (f i) (f j) ↔ (cycleGraph k).Adj i j) ∧
    (∀ a b, G.Adj a b → (∃ i, f i=a) ∧ ∃ j, f j=b) ∧ G.edgeFinset.card=k

private theorem notThree (G : SimpleGraph (Fin n)) (tri : NoTriangles G)
    (q : (cycleGraph 3).Copy G) : False := by
  have e (i j : Fin 3) (h : (cycleGraph 3).Adj i j) : G.Adj (q i) (q j) := q.toHom.map_rel' h
  exact tri _ _ _ (e 0 1 (by decide)) (e 1 2 (by decide)) (e 2 0 (by decide))

private theorem notFour (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (sq : NoFourCycle G)
    (q : (cycleGraph 4).Copy G) : False := by
  have e (i j : Fin 4) (h : (cycleGraph 4).Adj i j) : G.Adj (q i) (q j) := q.toHom.map_rel' h
  exact four G sq (fun eq => (by decide : (0 : Fin 4) ≠ 2) (q.injective eq))
    (fun eq => (by decide : (1 : Fin 4) ≠ 3) (q.injective eq))
    (e 0 1 (by decide)) (e 0 3 (by decide)) (e 2 1 (by decide)) (e 2 3 (by decide))

private theorem cycle_degree {k : ℕ} (hk : 3≤k) (i : Fin k) : (cycleGraph k).degree i = 2 := by
  obtain ⟨m,rfl⟩ : ∃ m, k=m+3 := ⟨k-3,by omega⟩
  exact cycleGraph_degree_three_le

/-- In a leafless graph with at most six active vertices and all active
    degrees equal to two, a 5- or 6-cycle includes every edge. -/
private theorem from_copy (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {k : ℕ}
    (hk : 5≤k) (q : (cycleGraph k).Copy G) (small : (active G).card ≤ 6)
    (deg : ∀ u, G.degree u ≤ 2) : k≤6 ∧ CoreCycle G k := by
  classical
  let f (i : Fin k) := q i
  have inj : Function.Injective f := q.injective
  let T := Finset.univ.image f
  have ct : T.card=k := by simp [T,Finset.card_image_of_injective _ inj]
  have nb (i : Fin k) : ((cycleGraph k).neighborFinset i).image f = G.neighborFinset (f i) := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
      exact (G.mem_neighborFinset _ _).mpr (q.toHom.map_rel' (((cycleGraph k).mem_neighborFinset _ _).mp hj))
    · rw [Finset.card_image_of_injective _ inj,(cycleGraph k).card_neighborFinset_eq_degree,
        cycle_degree (by omega)]
      exact deg (f i)
  have active_f (i : Fin k) : f i ∈ active G := by
    have sz := congrArg Finset.card (nb i)
    rw [Finset.card_image_of_injective _ inj,(cycleGraph k).card_neighborFinset_eq_degree,
      cycle_degree (by omega),G.card_neighborFinset_eq_degree] at sz
    simp [active,← sz]
  have sub : T ⊆ active G := by
    intro u hu
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hu
    exact active_f i
  have bound := Finset.card_le_card sub
  have lift (i : Fin k) (u : Fin n) (e : G.Adj (f i) u) : ∃ j, f j=u ∧ (cycleGraph k).Adj i j := by
    have mem := (G.mem_neighborFinset _ _).mpr e
    rw [← nb i] at mem
    obtain ⟨j,hj,ev⟩ := Finset.mem_image.mp mem
    exact ⟨j,ev,((cycleGraph k).mem_neighborFinset _ _).mp hj⟩
  have eq : active G=T := by
    apply Finset.Subset.antisymm _ sub
    intro u au
    by_contra out
    obtain ⟨v,uv⟩ := (G.degree_pos_iff_exists_adj u).mp (Finset.mem_filter.mp au).2
    have outv : v ∉ T := by
      intro vt
      obtain ⟨i,_,vi⟩ := Finset.mem_image.mp vt
      obtain ⟨j,ju,_⟩ := lift i u (vi ▸ uv.symm)
      exact out (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,ju⟩)
    have ex : insert u (insert v T) ⊆ active G :=
      Finset.insert_subset au (Finset.insert_subset (active_of_adj G uv.symm) sub)
    have big := Finset.card_le_card ex
    simp [out,outv,uv.ne,ct] at big
    omega
  have activeTwo (u : Fin n) (hu : u∈active G) : G.degree u=2 := by
    rw [eq] at hu
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hu
    change (G.neighborFinset (f i)).card = 2
    rw [← nb i,Finset.card_image_of_injective _ inj,(cycleGraph k).card_neighborFinset_eq_degree,
      cycle_degree (by omega)]
  have sum : (∑ u, G.degree u) = ∑ u ∈ active G, G.degree u := by
    rw [active,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro u _
    split <;> omega
  have compt : (∑ u ∈ active G, G.degree u)=k*2 := by
    calc
      _ = ∑ _u ∈ active G, 2 := Finset.sum_congr rfl activeTwo
      _ = _ := by simp [eq,ct]
  have hand := G.sum_degrees_eq_twice_card_edges
  have pre (u : Fin n) (hu : u∈active G) : ∃ i, f i=u := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (eq ▸ hu)
    exact ⟨i,hi⟩
  refine ⟨by omega,f,inj,?_,?_,by omega⟩
  · intro i j
    constructor
    · intro e
      obtain ⟨t,te,adj⟩ := lift i (f j) e
      exact inj te ▸ adj
    · exact q.toHom.map_rel'
  · intro a b ab
    exact ⟨pre a (active_of_adj G ab),pre b (active_of_adj G ab.symm)⟩

/-- A cyclic triangle- and four-cycle-free graph of vertex cover size at
    most three and with no degree-one vertices consists of an induced C5 or
    C6 and isolated vertices. The witness hits both endpoints of every edge. -/
theorem classify (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (tri : NoTriangles G)
    (sq : NoFourCycle G) (noLeaf : ∀ u, G.degree u≠1) (K : Finset (Fin n))
    (cover : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G K) (small : K.card≤3)
    (cyclic : ¬G.IsAcyclic) : ∃ k, (k=5 ∨ k=6) ∧ CoreCycle G k := by
  obtain ⟨v,p,cycle⟩ := SimpleGraph.not_isAcyclic_iff_exists_isCycle.mp cyclic
  have len := cycle.three_le_length
  obtain ⟨q⟩ := (SimpleGraph.cycleGraph_isContained_iff (n:=p.length) (by omega)).mpr ⟨v,p,cycle,rfl⟩
  have three : p.length ≠ 3 := fun e => notThree G tri (e ▸ q)
  have four' : p.length ≠ 4 := fun e => notFour G sq (e ▸ q)
  have six := support_le_six G sq noLeaf K cover small
  obtain ⟨le,core⟩ := from_copy G (by omega : 5≤p.length) q six (degree_le_two G tri sq noLeaf six)
  exact ⟨p.length,by omega,core⟩

end VertexPeel.CoverThreeCore
#print axioms VertexPeel.CoverThreeCore.classify
