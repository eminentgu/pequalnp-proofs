import PEqualNP.Outside.L_meta_615
import CoverThree

/-! # Lower bounds from a graph with at most one edge beyond its order

In a minimum vertex cover every vertex has an outside neighbor. Thus the total
internal degree on the internally active part of the cover is bounded by its
order plus the total degree excess above two. With minimum degree two and at
most one more edge than vertex, the excess is at most two. The strict edge
count needed by the upstream branch-slot proof follows even when the graph
has several components. The bound on cover size is automatic for bipartite
graphs and is needed only when there are exactly `n+1` edges.
-/

namespace VertexPeel.Bicyclic

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.CoverPromise
  PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_1774 PEqualNP.Outside.L615Aux.Counting
open scoped BigOperators Sym2

/-- Inside a minimum cover, deleting internally isolated vertices leaves more
    vertices than edges if the whole graph has minimum degree two and at most
    one more edge than vertex. -/
private theorem inside_strict {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (degree : ∀ v, 2 ≤ G.degree v) (sparse : G.edgeFinset.card ≤ n + 1)
    (S : Finset (Fin n)) (external : ∀ v ∈ S, ∃ w, G.Adj v w ∧ w ∉ S) :
    let I := G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S)
    let A := S.filter (fun v => ∃ w ∈ S, G.Adj v w)
    I.Nonempty → I.card < A.card := by
  classical
  let I := G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S)
  let A := S.filter (fun v => ∃ w ∈ S, G.Adj v w)
  change I.Nonempty → I.card < A.card
  intro hi
  let H : SimpleGraph A := G.induce (A : Set (Fin n))
  have internal : I = G.edgeFinset.filter (fun e => e.toFinset ⊆ A) := by
    ext e
    induction e using Sym2.inductionOn with
    | _ a b =>
      simp only [I,Finset.mem_filter,G.mem_edgeFinset]
      constructor
      · rintro ⟨ab,mem⟩
        have aS := mem a (Sym2.mem_mk_left ..)
        have bS := mem b (Sym2.mem_mk_right ..)
        refine ⟨ab,?_⟩
        intro v hv
        rcases Sym2.mem_iff.mp (Sym2.mem_toFinset.mp hv) with rfl|rfl
        · exact Finset.mem_filter.mpr ⟨aS,b,bS,ab⟩
        · exact Finset.mem_filter.mpr ⟨bS,a,aS,ab.symm⟩
      · rintro ⟨ab,sub⟩
        exact ⟨ab,fun v hv => (Finset.mem_filter.mp (sub (Sym2.mem_toFinset.mpr hv))).1⟩
  have cardI : I.card = H.edgeFinset.card := by
    rw [internal]
    exact G.card_filter_edgeFinset_toFinset_subset A
  have smallDeg (v : A) : H.degree v < G.degree v := by
    obtain ⟨w,edge,out⟩ := external v (Finset.mem_filter.mp v.property).1
    have cmp : (H.neighborFinset v).card ≤ ((G.neighborFinset v).erase w).card := by
      apply Finset.card_le_card_of_injOn (fun x : A => (x : Fin n))
      · intro x hx
        refine Finset.mem_erase.mpr ⟨?_,(G.mem_neighborFinset _ _).mpr ((H.mem_neighborFinset _ _).mp hx)⟩
        exact fun eq => out (eq ▸ (Finset.mem_filter.mp x.property).1)
      · exact Subtype.val_injective.injOn
    exact lt_of_le_of_lt cmp (Finset.card_erase_lt_of_mem ((G.mem_neighborFinset _ _).mpr edge))
  have degTotal : ∑ v, (2 + (G.degree v - 2)) = ∑ v, G.degree v :=
    Finset.sum_congr rfl (fun v _ => by have := degree v; omega)
  rw [Finset.sum_add_distrib,G.sum_degrees_eq_twice_card_edges] at degTotal
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at degTotal
  have diff : ∑ v, (G.degree v - 2) ≤ 2 := by omega
  have localDiff := (Finset.sum_le_univ_sum_of_nonneg (s := A) (f := fun v => G.degree v - 2)
    (fun _ => Nat.zero_le _)).trans diff
  have count : (∑ v : A, H.degree v) ≤ ∑ v : A, (1 + (G.degree (v : Fin n) - 2)) :=
    Finset.sum_le_sum (fun v _ => by have := smallDeg v; omega)
  rw [H.sum_degrees_eq_twice_card_edges,Finset.sum_add_distrib] at count
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,smul_eq_mul,mul_one] at count
  rw [Finset.sum_coe_sort A (fun v => G.degree v-2)] at count
  by_cases large : 3 ≤ A.card
  · omega
  have bound := H.card_edgeFinset_le_card_choose_two
  change H.edgeFinset.card ≤ (Fintype.card A).choose 2 at bound
  rw [Fintype.card_coe] at bound
  have pos := Finset.card_pos.mpr hi
  interval_cases k : A.card <;> simp_all

/-- The sharp cover-circuit lower bound for graphs of minimum degree two with
    at most one more edge than vertex, with the half-order cover restriction
    needed only in the equality case. -/
theorem numerical {n : ℕ} (G : SimpleGraph (Fin n)) [base : DecidableRel G.Adj]
    (sq : NoFourCycle G) (degree : ∀ v, 2 ≤ G.degree v)
    (sparse : G.edgeFinset.card ≤ n+1) (half : G.edgeFinset.card = n+1 → 2 * Loc.tau G ≤ n+1) :
    StableExtension.Numerical G (Loc.tau G) := by
  intro inst C mono correct
  have same : inst = base := Subsingleton.elim _ _
  subst inst
  classical
  have noSquare : NoSquare G := by
    intro a b c d ac bd ab bc cd da
    exact bd (Finset.card_le_one.mp (sq a c ac) b (by simp [ab,bc.symm]) d (by simp [da.symm,cd]))
  have deg (v : Fin n) : 2 ≤ (G.neighborSet v).ncard := by
    rw [Set.ncard_eq_toFinset_card']
    exact degree v
  have minC (T : Finset (Fin n)) (c : ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) :
      Loc.tau G ≤ T.card := Loc.tau_le G T c
  have eval : PEqualNP.Outside.L615Aux.Wires.GraphEval C G := by
    intro x
    have h := congrFun correct x
    change C.eval (List.ofFn x) = true ↔ _
    change C.eval (List.ofFn x) = graphFun G ∅ x at h
    simp [h,graphFun]
  have weak := thetaLowerWithinOne G C deg noSquare minC mono eval
  by_contra! bad
  have full : G.edgeFinset.card = n+1 := by omega
  have tight : C.size+1 = n+Loc.tau G := by omega
  obtain ⟨S,sel,cov,sc,_⟩ := tight_branch_cover deg noSquare minC mono eval tight
  have minS : ∀ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) → S.card ≤ T.card :=
    sc ▸ minC
  apply PEqualNP.Outside.L615Aux.Theta.total_slots_impossible G S cov minS full (sc ▸ half full)
  · exact inside_strict G degree sparse S (fun _ hv => PEqualNP.Outside.L615Aux.Theta.outside_of_minimal S cov minS hv)
  · exact fun _ hv => tight_neighbor_slots deg noSquare minC mono eval tight S sel hv

private theorem half_of_bipartite {n : ℕ} (G : SimpleGraph (Fin n))
    (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v) : 2 * Loc.tau G ≤ n := by
  classical
  obtain ⟨c,proper⟩ := bip
  let S := Finset.univ.filter fun v => c v = true
  have covS : IsVertexCover G S := by
    intro u v edge
    have := proper _ _ edge
    simpa [S] using (by cases a:c u <;> cases b:c v <;> simp_all : c u = true ∨ c v = true)
  have covT : IsVertexCover G Sᶜ := by
    intro u v edge
    have := proper _ _ edge
    simpa [S] using (by cases a:c u <;> cases b:c v <;> simp_all : c u = false ∨ c v = false)
  have a := Loc.tau_le G S covS
  have b := Loc.tau_le G Sᶜ covT
  have h := Finset.card_compl_add_card S
  simp only [Fintype.card_fin] at h
  omega

theorem bipartite_numerical {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v) (sq : NoFourCycle G)
    (degree : ∀ v, 2 ≤ G.degree v) (sparse : G.edgeFinset.card ≤ n+1) :
    StableExtension.Numerical G (Loc.tau G) :=
  @numerical n G _ sq degree sparse (fun _ => by have := half_of_bipartite G bip; omega)

open VertexPeel.CoverCircuit

/-- The numerical certificate yields the ownership descent in its original circuit model. -/
theorem ownership {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (sq : NoFourCycle G) (degree : ∀ v, 2 ≤ G.degree v) (sparse : G.edgeFinset.card ≤ n+1)
    (half : G.edgeFinset.card = n+1 → 2 * Loc.tau G ≤ n+1) : StepAt G := by
  intro C minimum correct _ positive
  obtain ⟨S,c,sc⟩ := Loc.tau_attained G
  have bound := numerical G sq degree sparse half C minimum.1 correct
  apply coveredDescent G C S c _ positive
  rw [Set.ncard_eq_toFinset_card']
  change G.edgeFinset.card + S.card - 1 ≤ C.size
  omega

/-- A common deletion vertex for every correct exact binary circuit. -/
theorem vertex_deletion {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v) (sq : NoFourCycle G)
    (degree : ∀ v, 2 ≤ G.degree v) (sparse : G.edgeFinset.card ≤ n+1) (edges : 2 ≤ G.edgeFinset.card) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C →
      circuitFun n C = graphFun G ∅ → SavesAt G z C := by
  obtain ⟨z,hz,rem⟩ := nonemptyCut G edges
  obtain ⟨S,c,sc⟩ := Loc.tau_attained G
  refine ⟨z,hz,?_⟩
  intro C ao correct
  have mono : Monotone2 C := fun g hg =>
    ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ao.1 g hg,(ao.2.2 g hg).le⟩
  have bound := bipartite_numerical G bip sq degree sparse C mono correct
  exact atVertexOfCoverBound G z rem C ⟨S,c,by omega⟩

end VertexPeel.Bicyclic

#print axioms VertexPeel.Bicyclic.numerical
#print axioms VertexPeel.Bicyclic.bipartite_numerical
#print axioms VertexPeel.Bicyclic.ownership
#print axioms VertexPeel.Bicyclic.vertex_deletion
