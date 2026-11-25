import RowGraph

namespace VertexPeel.RowOverlap

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.Core
open VertexPeel.ZeroFold VertexPeel.RowCharge VertexPeel.RowGraph

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (R : Finset (Fin n)) (C : Circuit)

noncomputable def orGates (C : Circuit) := by
  classical
  exact (Finset.range C.size).filter (isOr C)

noncomputable def rows (L : Finset (Fin n)) (j : ℕ) := by
  classical
  exact L.filter (fun u => j ∈ rowGates G R C u)

/-- Repeated charges on a gate, retaining only gates with at most one right singleton. -/
noncomputable def extra (L : Finset (Fin n)) (j : ℕ) : ℕ :=
  if (singles R C (n+j)).card ≤ 1 then (rows G R C L j).card - 1 else 0

/-- Sum the row bounds on the physical DAG. Every repeat is charged to a gate accepting at
most one right singleton, even if its cone contains many right inputs. -/
theorem overlap_bound (hc : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅)
    (indep : ∀ a ∈ R, ∀ b ∈ R, ¬ G.Adj a b) (four : NoFourCycle G) (L : Finset (Fin n)) :
    ∑ u ∈ L, G.degree u ≤ L.card + (orGates C).card + ∑ j ∈ orGates C, extra G R C L j := by
  classical
  let O := orGates C
  have sub (u : Fin n) : rowGates G R C u ⊆ O := by
    intro j hj
    obtain ⟨hr,sp⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨hr,sp.1⟩
  have sums : ∑ u ∈ L, (rowGates G R C u).card = ∑ j ∈ O, (rows G R C L j).card := by
    calc
      _ = ∑ u ∈ L, ∑ j ∈ O, if j ∈ rowGates G R C u then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro u _
        simp [Finset.inter_eq_right.mpr (sub u)]
      _ = ∑ j ∈ O, ∑ u ∈ L, if j ∈ rowGates G R C u then 1 else 0 := Finset.sum_comm
      _ = _ := by simp [rows]
  have each (j : ℕ) : (rows G R C L j).card ≤ 1 + extra G R C L j := by
    by_cases small : (singles R C (n+j)).card ≤ 1
    · simp [extra,small]
      omega
    · have h : (rows G R C L j).card ≤ 1 := Finset.card_le_one.mpr (fun u hu v hv =>
        rich_unique G R C hc four (j := j) (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2 (by omega))
      simpa [extra,small] using h
  have a := Finset.sum_le_sum (s := L) (fun u _ => degree_bound G R indep C hc ok u)
  have b := Finset.sum_le_sum (s := O) (fun j _ => each j)
  simp only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,mul_one] at a b
  rw [sums] at a
  change _ ≤ L.card + O.card + ∑ j ∈ O, extra G R C L j
  omega

/-- If local row counts exceed the OR budget, an actual physical gate must split at least two
rows. Its right-singleton support has size at most one. -/
theorem shared_gate_of_deficit (hc : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅)
    (indep : ∀ a ∈ R, ∀ b ∈ R, ¬ G.Adj a b) (four : NoFourCycle G) (L : Finset (Fin n))
    (short : L.card + (orGates C).card < ∑ u ∈ L, G.degree u) :
    ∃ j ∈ orGates C, 2 ≤ (rows G R C L j).card ∧ (singles R C (n+j)).card ≤ 1 := by
  classical
  by_contra! fail
  have zero : ∑ j ∈ orGates C, extra G R C L j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    by_cases small : (singles R C (n+j)).card ≤ 1
    · have := fail j hj
      simp [extra,small]
      omega
    · simp [extra,small]
  have := overlap_bound G R C hc ok indep four L
  omega

end VertexPeel.RowOverlap
