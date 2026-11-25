import CubicPorts
import PortHallGirth

namespace VertexPeel.NeighborPorts
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadTwo
open VertexPeel.PortHall
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- Every binary monotone circuit for a bipartite subcubic graph without
four- or six-cycles needs at least the minimum vertex cover number of AND gates. -/
theorem subcubic_and_lower (bip : ∃ c : Fin n → Bool, ∀ u v,G.Adj u v → c u≠c v)
    (deg : ∀ v,G.degree v ≤ 3) (sq : NoFourCycle G)
    (six : ∀ v (w : G.Walk v v), w.IsCycle → w.length≠6)
    (C : Circuit) (ao : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅) :
    Loc.tau G ≤ (PivotAND.physical C).card := by
  apply PivotAND.paid_induction G _ C ao ok
  intro H _ sub D dao correct short
  obtain ⟨c,proper⟩ := bip
  have sqH := PivotAND.square_mono sub sq
  apply paid_of_label_bound D H dao correct sqH ⟨c,fun u v e => proper u v (sub e)⟩
    (fun v => (H.degree_le_of_le sub).trans (deg v)) _ short
  intro A capacity blocked
  apply PortHall.card_le H sqH _ _ _ capacity blocked
  intro embedded
  obtain ⟨v,w,cycle,len⟩ := PortHall.six_cycle embedded
  exact six v (w.mapLe sub) (cycle.mapLe sub) (by simpa using len)

theorem subcubic_girth (bip : ∃ c : Fin n → Bool, ∀ u v,G.Adj u v → c u≠c v)
    (deg : ∀ v,G.degree v ≤ 3) (girth : 6 < G.egirth)
    (C : Circuit) (ao : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅) :
    Loc.tau G ≤ (PivotAND.physical C).card := by
  apply subcubic_and_lower G bip deg (PortHall.no_four_of_girth (lt_trans (by decide) girth)) _ C ao ok
  intro v w cyc len
  have bound := cyc.egirth_le_length
  rw [len] at bound
  exact (not_le_of_gt girth) bound
#print axioms subcubic_girth
#print axioms subcubic_and_lower
end VertexPeel.NeighborPorts
