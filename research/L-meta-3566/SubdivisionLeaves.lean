import SubdivisionAND
import ConnectedSubdivision
import Bicyclic
import PendantPathPeel

namespace VertexPeel.PivotAND
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.Core PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_1774 PEqualNP.MetaComplexity.CoverPromise
open VertexPeel.AndSeparation VertexPeel.RowGraph VertexPeel.RowCharge VertexPeel.CoverCircuit
variable {n : ℕ}

private theorem stable_by_residual_degree (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (cross : ∀ u v, G.Adj u v → (u ∈ A ↔ v ∉ A))
    (z : Fin n) (outside : z ∉ A) (d : ℕ) (positive : 0<d)
    (lower : ∀ u∈A, d ≤ ((G.neighborFinset u).erase z).card)
    (upper : ∀ v∉A, G.degree v≤d) : Leaves.CoverStable G z := by
  classical
  intro S cover
  have coverA : IsVertexCover G A := by
    intro u v uv
    by_cases h : u ∈ A
    · exact Or.inl h
    · exact Or.inr (not_not.mp (fun nv => h ((cross _ _ uv).mpr nv)))
  have lo (u : Fin n) (hu : u ∈ A \ S) : d ≤ ((S \ A).bipartiteAbove G.Adj u).card := by
    obtain ⟨ua,us⟩ := Finset.mem_sdiff.mp hu
    have uz : u ≠ z := fun e => outside (e ▸ ua)
    have sub : (G.neighborFinset u).erase z ⊆ (S \ A).bipartiteAbove G.Adj u := by
      intro v hv
      obtain ⟨vz,hv⟩ := Finset.mem_erase.mp hv
      have uv := (G.mem_neighborFinset u v).mp hv
      have vs := (cover u v (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨uv,uz,vz⟩)).resolve_left us
      exact (Finset.mem_bipartiteAbove G.Adj).mpr ⟨Finset.mem_sdiff.mpr ⟨vs,(cross _ _ uv).mp ua⟩,uv⟩
    exact (lower u ua).trans (Finset.card_le_card sub)
  have hi (v : Fin n) (hv : v ∈ S \ A) : ((A \ S).bipartiteBelow G.Adj v).card ≤ d := by
    have sub : (A \ S).bipartiteBelow G.Adj v ⊆ G.neighborFinset v := by
      intro u hu
      exact (G.mem_neighborFinset v u).mpr ((Finset.mem_bipartiteBelow G.Adj).mp hu).2.symm
    exact (Finset.card_le_card sub).trans (by simpa using upper _ (Finset.mem_sdiff.mp hv).2)
  have count := Finset.card_nsmul_le_card_nsmul G.Adj lo hi
  have bound : (A \ S).card ≤ (S \ A).card := by
    simpa [Nat.nsmul_eq_mul, Nat.mul_le_mul_right_iff positive] using count
  exact ⟨A,coverA,Finset.card_sdiff_le_card_sdiff_iff.mp bound⟩

private theorem sole (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {a b : Fin n} (ab : G.Adj a b)
    (one : G.degree a=1) (v : Fin n) (e : G.Adj a v) : v=b :=
  Finset.card_le_one.mp (show (G.neighborFinset a).card≤1 from one.le) v ((G.mem_neighborFinset _ _).mpr e)
    b ((G.mem_neighborFinset _ _).mpr ab)

/-- On any graph with one side of degree at most two, a single leaf anywhere gives a
vertex for the full two-budget deletion theorem, including disconnected graphs. -/
theorem side_degree_two_leaf_vertex (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → Bool) (proper : ∀ u v, G.Adj u v → c u ≠ c v) (low : ∀ v, c v=false → G.degree v≤2)
    (someLeaf : ∃ v, G.degree v=1) (many : 2≤G.edgeFinset.card) :
    ∃ z : Fin n, 0<G.degree z ∧ ∀ C : Circuit, IsAO2 n C → circuitFun n C = graphFun G ∅ → SavesAt G z C := by
  classical
  by_cases cheap : ∃ a b, G.Adj a b ∧ G.degree a=1 ∧ G.degree b≤2
  · obtain ⟨a,b,ab,da,db⟩ := cheap
    by_cases two : G.degree b=2
    · exact PendantPathPeel.peel_pendant_path G ab da two
    · have pos := (G.degree_pos_iff_exists_adj b).mpr ⟨a,ab.symm⟩
      exact ⟨a,Leaves.isolatedEdgeAt G a b ab (sole G ab da) (sole G ab.symm (by omega)) many⟩
  obtain ⟨l,dl⟩ := someLeaf
  obtain ⟨p,lp⟩ := (G.degree_pos_iff_exists_adj l).mp (by omega)
  have big {a b} (ab : G.Adj a b) (da : G.degree a=1) : 3≤G.degree b := by
    by_contra! small; exact cheap ⟨a,b,ab,da,by omega⟩
  have dp := big lp dl
  have cp : c p=true := by cases h : c p; have := low p h; omega; rfl
  have cl : c l=false := by have diff := proper _ _ lp; cases h : c l <;> simp_all
  let A := Finset.univ.filter (fun u => c u = true ∧ 0<G.degree u)
  have mem {u v} (uv : G.Adj u v) : u∈A ↔ c u=true := by
    simp [A,(G.degree_pos_iff_exists_adj u).mpr ⟨v,uv⟩]
  have cross (u v : Fin n) (uv : G.Adj u v) : u∈A ↔ v∉A := by
    rw [mem uv,mem uv.symm]; have diff := proper u v uv; cases a : c u <;> cases b : c v <;> simp_all
  have stable : Leaves.CoverStable G l := by
    apply stable_by_residual_degree G A cross l (by simp [A,cl]) 2 (by decide)
    · intro u h
      have props := (Finset.mem_filter.mp h).2
      by_cases ul : l∈G.neighborFinset u
      · have ul' := (G.mem_neighborFinset _ _).mp ul
        have deg := big ul'.symm dl
        have cut := Finset.card_erase_add_one ul
        rw [G.card_neighborFinset_eq_degree] at cut
        omega
      · rw [Finset.erase_eq_of_notMem ul,G.card_neighborFinset_eq_degree]
        by_contra! small
        have one : G.degree u = 1 := by omega
        obtain ⟨v,uv⟩ := (G.degree_pos_iff_exists_adj u).mp props.2
        have cf : c v=false := by have diff := proper _ _ uv; cases h : c v <;> simp_all
        have := big uv one; have := low v cf; omega
    · intro v outside
      by_cases cold : c v=false
      · exact low _ cold
      · have off : ¬0<G.degree v := by intro pos; exact outside (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by cases h : c v <;> simp_all⟩)
        omega
  exact ⟨l,by omega,Leaves.stableLeaf G l dl stable⟩

/-- Every connected square-free bipartite graph with degree at most two on one side
has a single witness for both deletion budgets in every correct circuit. -/
theorem connected_side_degree_two_vertex (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → Bool) (proper : ∀ u v, G.Adj u v → c u ≠ c v) (low : ∀ v, c v=false → G.degree v≤2)
    (connected : G.Preconnected) (sq : NoFourCycle G) (many : 2≤G.edgeFinset.card) :
    ∃ z : Fin n, 0<G.degree z ∧ ∀ C : Circuit, IsAO2 n C → circuitFun n C = graphFun G ∅ → SavesAt G z C := by
  classical
  by_cases leaf : ∃ v, G.degree v=1
  · exact side_degree_two_leaf_vertex G c proper low leaf many
  obtain ⟨e,he⟩ := Finset.card_pos.mp (show 0 < G.edgeFinset.card by omega)
  have someEdge : ∃ a b, G.Adj a b := by induction e using Sym2.inductionOn with | _ a b => exact ⟨a,b,G.mem_edgeFinset.mp he⟩
  obtain ⟨a,b,ab⟩ := someEdge
  have lower (v : Fin n) : 2≤G.degree v := by
    have pos : 0 < G.degree v := by
      by_cases eq : v=a
      · subst v; exact (G.degree_pos_iff_exists_adj a).mpr ⟨b,ab⟩
      · exact (connected v a).degree_pos_left eq
    have ne : G.degree v ≠ 1 := fun h => leaf ⟨v,h⟩
    omega
  let A := Finset.univ.filter (fun u => c u=true)
  have cross (u v : Fin n) (uv : G.Adj u v) : (u∈A ↔ v∉A) := by
    have diff := proper _ _ uv
    cases h : c u <;> cases hh : c v <;> simp_all [A]
  by_cases branch : ∃ u∈A, 2 < G.degree u
  · have ex : ∃ u, u∉A := by
      by_cases ha : a∈A
      · exact ⟨b,(cross _ _ ab).mp ha⟩
      · exact ⟨a,ha⟩
    apply ConnectedSubdivision.peel_connected_subdivision G A ex cross connected sq (fun u _ => lower u) branch
    intro u hu
    have side : c u=false := by cases col : c u <;> simp_all [A]
    exact Nat.le_antisymm (low _ side) (lower _)
  · have degrees (v : Fin n) : G.degree v=2 := by
      apply Nat.le_antisymm _ (lower _)
      by_cases h : v∈A
      · by_contra! lt; exact branch ⟨_,h,lt⟩
      · exact low v (by cases col : c v <;> simp_all [A])
    have sum := G.sum_degrees_eq_twice_card_edges
    simp only [degrees,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at sum
    exact Bicyclic.vertex_deletion G ⟨c,proper⟩ sq lower (by omega) many

#print axioms connected_side_degree_two_vertex
#print axioms side_degree_two_leaf_vertex
end VertexPeel.PivotAND
