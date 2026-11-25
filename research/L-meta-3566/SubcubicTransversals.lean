import CubicPorts
import PortHallGirth
import NormalizeCount

namespace VertexPeel.PivotAND
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.Core PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.CoverPromise
open VertexPeel.NeighborPorts VertexPeel.PortHall
variable {n : ℕ}

/-- A coloring outside Z loses at most one unit in the doubled cover bound for
each active deleted vertex. Isolated inputs can be discarded from Z. -/
theorem double_cover_after_set (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (Z : Finset (Fin n))
    (c : Fin n → Bool) (proper : ∀ u v, G.Adj u v → u∉Z → v∉Z → c u ≠ c v) :
    2*Loc.tau G ≤ (CoverThreeCore.active G).card + Z.card := by
  classical
  let A := CoverThreeCore.active G
  let B := A \ Z
  let W := A ∩ Z
  have cov (b : Bool) : IsVertexCover G (W ∪ B.filter (fun v => c v=b)) := by
    intro u v uv
    have hu := CoverThreeCore.active_of_adj G uv
    have hv := CoverThreeCore.active_of_adj G uv.symm
    by_cases uz : u∈Z
    · exact Or.inl (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hu,uz⟩))
    by_cases vz : v∈Z
    · exact Or.inr (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hv,vz⟩))
    have cover (i : Fin n) (hi : i∈A) (iz : i∉Z) (col : c i=b) : i∈W ∪ B.filter (fun v => c v=b) :=
      Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hi,iz⟩,col⟩)
    have diff := proper _ _ uv uz vz
    cases q : c u <;> cases r : c v <;> cases b <;> first | exact Or.inl (cover u hu uz q) | exact Or.inr (cover v hv vz r) | simp_all
  have one (b : Bool) := (Loc.tau_le G _ (cov b)).trans (Finset.card_union_le _ _)
  have t := one true; have f := one false
  have cc := Finset.card_filter_add_card_filter_not (s:=B) (p:=fun v => c v=true)
  simp only [Bool.not_eq_true] at cc
  have wt : W.card ≤ Z.card := Finset.card_le_card Finset.inter_subset_right
  have total : B.card+W.card=A.card := Finset.card_sdiff_add_card_inter _ _
  change 2*Loc.tau G ≤ A.card+Z.card
  omega

/-- Subcubic square-free graphs with an odd-cycle transversal Z and a six-cycle
transversal T can miss at most floor((|Z|+|T|)/2) ANDs from the cover number. -/
theorem subcubic_two_transversals (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Z T : Finset (Fin n)) (c : Fin n → Bool) (proper : ∀ u v, G.Adj u v → u∉Z → v∉Z → c u≠c v)
    (deg : ∀ v, G.degree v≤3) (sq : NoFourCycle G)
    (hit : ∀ z (w : G.Walk z z), w.IsCycle → w.length=6 → ∃ v∈T, v∈w.support)
    (C : Circuit) (ao : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅) :
    Loc.tau G ≤ (physical C).card + (Z.card + T.card)/2 := by
  classical
  apply paid_induction_offset G ((Z.card+T.card)/2) _ C ao ok
  intro H inst sub D dao correct deficit
  have sqH := square_mono sub sq
  have count := double_cover_after_set H Z c (fun u v uv => proper u v (sub uv))
  apply paid_of_label_deficit D H dao correct sqH
    (fun v => (H.degree_le_of_le sub).trans (deg v)) T.card _ (by omega)
  intro A capacity blocked
  have clean : ¬SixCrownIn H (A \ T) := by
    rintro ⟨X,Y,hx,hy,dis,e,inside⟩
    have lifted : SixCrownIn G (A \ T) :=
      ⟨X,Y,hx,hy,dis,fun i j ij => sub (e i j ij),inside⟩
    obtain ⟨z,w,cycle,six,wmem⟩ := six_cycle_in lifted
    obtain ⟨v,inT,on⟩ := hit z w cycle six
    exact (Finset.mem_sdiff.mp (wmem v on)).2 inT
  have bound := hit_bound H sqH A T (ports D) capacity blocked clean
  exact bound.trans (Nat.add_le_add_left (Finset.card_le_card Finset.inter_subset_right) _)

/-- One deletion to bipartiteness costs no AND gates when six-cycles are absent. -/
theorem subcubic_one_odd_transversal (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : Fin n)
    (c : Fin n → Bool) (proper : ∀ u v, (G.deleteIncidenceSet p).Adj u v → c u≠c v)
    (deg : ∀ v, G.degree v≤3) (sq : NoFourCycle G) (six : ∀ z (w : G.Walk z z), w.IsCycle → w.length≠6)
    (C : Circuit) (ao : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅) : Loc.tau G ≤ (physical C).card := by
  have bound := subcubic_two_transversals G {p} ∅ c (fun u v uv up vp => proper _ _
    (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨uv,by simpa using up,by simpa using vp⟩)) deg sq
    (fun z w cy len => (six z w cy len).elim) C ao ok
  simpa using bound

/-- The joint transversal estimate for general monotone fan-in-two circuits. -/
theorem subcubic_two_transversals_mono (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Z T : Finset (Fin n)) (c : Fin n → Bool) (proper : ∀ u v, G.Adj u v → u∉Z → v∉Z → c u≠c v)
    (deg : ∀ v, G.degree v≤3) (sq : NoFourCycle G)
    (hit : ∀ z (w : G.Walk z z), w.IsCycle → w.length=6 → ∃ v∈T, v∈w.support)
    (C : Circuit) (mono : Monotone2 C) (ok : circuitFun n C = graphFun G ∅) :
    Loc.tau G ≤ (physical C).card + (Z.card+T.card)/2 := by
  have zero : circuitFun n C (fun _ => false)=false := (congrFun ok _).trans (by simp [graphFun])
  obtain ⟨D,ao,same,budget⟩ := NormalizeCount.normalize C mono zero
  exact (subcubic_two_transversals G Z T c proper deg sq hit D ao (same.trans ok)).trans
    (Nat.add_le_add_right budget _)

#print axioms subcubic_two_transversals_mono
#print axioms double_cover_after_set
#print axioms subcubic_two_transversals
#print axioms subcubic_one_odd_transversal
end VertexPeel.PivotAND
