import PortTransversal
import PseudoforestAND

namespace VertexPeel.NeighborPorts
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.Core
open VertexPeel.ZeroFold VertexPeel.RowGraph VertexPeel.RowCharge VertexPeel.AndSeparation

variable {n : ℕ} (C : Circuit)

/-- The gate position and which operand the singleton selects. -/
def label (x : Fin n) (j : ℕ) : ℕ × Bool := (j,wval C (single x) (in0 C j))

noncomputable def ports (x : Fin n) : Finset (ℕ × Bool) := (lit C x).image (label C x)

private theorem size_ports (x : Fin n) : (ports C x).card = (lit C x).card :=
  Finset.card_image_of_injective _ (fun _ _ eq => congrArg Prod.fst eq)

private theorem read_at {x y : Fin n} {j : ℕ} (mem : label C x j ∈ ports C y) :
    wval C (single y) (port C x j)=true := by
  classical
  obtain ⟨k,hk,eq⟩ := Finset.mem_image.mp mem
  have e : k=j := congrArg Prod.fst eq
  subst k
  have side : wval C (single y) (in0 C j)=wval C (single x) (in0 C j) := congrArg Prod.snd eq
  have hit := (Finset.mem_filter.mp (show j∈lit C y from hk)).2.2
  simpa only [port,side] using hit

private theorem lit_pivot {x : Fin n} {j : ℕ} (hit : j∈lit C x) : PivotAND.lit C x j := by
  classical
  obtain ⟨_,andJ,on⟩ := Finset.mem_filter.mp (show j∈lit C x from hit)
  refine ⟨andJ,?_⟩
  by_cases left : wval C (single x) (in0 C j)=true
  · exact Or.inl left
  · right
    change wval C (single x) (in1 C j)=true
    simpa only [port,ite_eq_right left] using on

private theorem used_ports (U : Finset (Fin n)) :
    (U.biUnion (ports C)).card ≤ 2*(PivotAND.physical C).card := by
  classical
  calc
    _ ≤ ((PivotAND.physical C) ×ˢ (Finset.univ : Finset Bool)).card := by
      apply Finset.card_le_card
      intro p hp
      obtain ⟨x,_,mem⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp mem
      obtain ⟨range,andJ,_⟩ := Finset.mem_filter.mp (show j∈lit C x from hj)
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨range,andJ⟩,Finset.mem_univ _⟩
    _ = _ := by simp [Nat.mul_comm]

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- Distinct labels designate physical ports, so a replacement at every label
is also a replacement at every gate in the transversal theorem. -/
theorem labeled_transversal (ao : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅)
    (sq : NoFourCycle G) (x : Fin n) (few : (lit C x).card < G.degree x)
    (f : ℕ × Bool → Fin n) (other : ∀ p ∈ ports C x, f p ≠ x ∧ p ∈ ports C (f p)) :
    ∃ p ∈ ports C x, ∃ q ∈ ports C x, G.Adj (f p) (f q) := by
  let Y (j : ℕ) := f (label C x j)
  have mem (j) (hj : j∈lit C x) : label C x j ∈ ports C x := Finset.mem_image_of_mem _ hj
  obtain ⟨i,hi,j,hj,adj⟩ := transversal_edge G C ao ok sq x few Y
    (fun i hi => (other _ (mem i hi)).1)
    (fun i hi => read_at C (other _ (mem i hi)).2)
  exact ⟨_,mem i hi,_,mem j hj,adj⟩

/-- A purely combinatorial bound on these label families yields a paid pivot in the original circuit. -/
theorem paid_of_label_bound (ao : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅) (sq : NoFourCycle G)
    (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u≠c v) (deg : ∀ x,G.degree x ≤ 3)
    (hull : let A := CoverThreeCore.active G
      (∀ x∈A, (ports C x).card ≤ 2) →
      (∀ x∈A, ∀ f : ℕ × Bool → Fin n,
        (∀ p∈ports C x, f p∈A ∧ f p≠x ∧ p∈ports C (f p)) →
        ∃ p∈ports C x, ∃ q∈ports C x, G.Adj (f p) (f q)) →
      A.card ≤ (A.biUnion (ports C)).card)
    (few : (PivotAND.physical C).card < Loc.tau G) :
    ∃ x, 0 < G.degree x ∧ ∃ L : Finset ℕ, G.degree x ≤ L.card ∧ ∀ j∈L, PivotAND.lit C x j := by
  classical
  let A := CoverThreeCore.active G
  by_contra! no
  have small (x) (hx : x∈A) : (lit C x).card < G.degree x := by
    by_contra! enough
    obtain ⟨j,hj,off⟩ := no x (Finset.mem_filter.mp hx).2 (lit C x) enough
    exact off (lit_pivot C hj)
  have number := hull (fun x hx => by rw [size_ports]; have := small x hx; have := deg x; omega)
    (fun x hx f h => labeled_transversal C G ao ok sq x (small x hx) f (fun p hp => (h p hp).2))
  have cover := PivotAND.double_cover_le_active G bip
  have cap := used_ports C A
  change (CoverThreeCore.active G).card ≤ (A.biUnion (ports C)).card at number
  omega

#print axioms labeled_transversal
#print axioms paid_of_label_bound
end VertexPeel.NeighborPorts
