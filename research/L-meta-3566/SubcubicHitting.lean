import CubicPorts
import PortHallGirth

namespace VertexPeel.NeighborPorts

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm
open VertexPeel.PortHall

variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- A six-cycle hitting set T permits at most floor(|T|/2) missing AND gates.
The same set T is used throughout the recursion on arbitrary edge subgraphs. -/
theorem subcubic_and_hitting (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u≠c v)
    (deg : ∀ v, G.degree v≤3) (sq : NoFourCycle G) (T : Finset (Fin n))
    (hit : ∀ z (w : G.Walk z z), w.IsCycle → w.length=6 → ∃ v∈T, v∈w.support)
    (C : Circuit) (ao : IsAO2 n C) (ok : circuitFun n C=graphFun G ∅) :
    Loc.tau G ≤ (PivotAND.physical C).card + T.card/2 := by
  classical
  apply PivotAND.paid_induction_offset G (T.card/2) _ C ao ok
  intro H inst sub D dao correct deficit
  obtain ⟨c,proper⟩ := bip
  have sqH := PivotAND.square_mono sub sq
  have count := PivotAND.double_cover_le_active H ⟨c,fun u v e => proper u v (sub e)⟩
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

/-- Arbitrarily many six-cycles may be present if one vertex meets every one. -/
theorem subcubic_and_one_hit (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u≠c v)
    (deg : ∀ v, G.degree v≤3) (sq : NoFourCycle G) (t : Fin n)
    (hit : ∀ z (w : G.Walk z z), w.IsCycle → w.length=6 → t∈w.support)
    (C : Circuit) (ao : IsAO2 n C) (ok : circuitFun n C=graphFun G ∅) :
    Loc.tau G ≤ (PivotAND.physical C).card := by
  have bound := subcubic_and_hitting G bip deg sq {t}
    (fun z w cy sz => ⟨t,Finset.mem_singleton_self _,hit z w cy sz⟩) C ao ok
  simpa using bound

#print axioms subcubic_and_hitting
#print axioms subcubic_and_one_hit
end VertexPeel.NeighborPorts
