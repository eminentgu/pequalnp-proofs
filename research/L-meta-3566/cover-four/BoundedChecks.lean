import EdgeBudget
import PEqualNP.Outside.L_meta_1527

namespace VertexPeel.BoundedChecks
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.MetaComplexity.CoverPromise PEqualNP.TopForm PEqualNP.Outside.L_meta_1774
open VertexPeel.CoverThreeCore VertexPeel.CoverCircuit

/-- At fixed cover number the vertex, edge, gate, input-reference, and output ranges
are all bounded. The only allowed gate operations are binary AND and OR. -/
def At (t : ℕ) : Prop := ∀ m, m ≤ t + t.choose 2 → ∀ (H : SimpleGraph (Fin m)) [DecidableRel H.Adj],
  NoTriangles H → NoFourCycle H → Loc.tau H = t → CriticalSupport.AllLeavesCritical H →
  (∀ a, 0 < H.degree a) → H.edgeFinset.card ≤ t*(t-1) →
  ∀ C : Circuit, IsAO2 m C → circuitFun m C = graphFun H ∅ → C.output < m+C.size →
    C.size+2 ≤ t*t → H.edgeFinset.card + t ≤ C.size+1

theorem lift_at {n t : ℕ} (G : SimpleGraph (Fin n)) [base : DecidableRel G.Adj]
    (tri : NoTriangles G) (sq : NoFourCycle G) (size : Loc.tau G = t) (large : 3 ≤ t)
    (tests : At t) : StableExtension.Numerical G t := by
  intro inst C mono ok
  have eq : inst = base := Subsingleton.elim _ _
  subst inst
  apply FiniteCritical.of_small_order G tri sq size large _ C mono ok
  intro m bound H decH triH sqH sz crit active inst D dm dc
  have eq : inst = decH := Subsingleton.elim _ _
  subst inst
  obtain ⟨T,cover,card⟩ := Loc.tau_attained H
  have ct : T.card = t := card.trans sz
  have edges : H.edgeFinset.card ≤ t*(t-1) := by
    simpa only [ct] using EdgeBudget.core_edges H T triH sqH cover active (ct.symm ▸ bound)
  obtain ⟨A,ao,correct,le⟩ : ∃ A : Circuit, IsAO2 m A ∧ circuitFun m A = graphFun H ∅ ∧ A.size ≤ D.size := by
    apply PEqualNP.Outside.L_meta_1527 m H decH D dm
    intro x
    change circuitFun m D x = true ↔ _
    rw [dc]
    simp [graphFun]
  by_contra! small
  have eqt : t*(t-1)+t = t*t := by
    rw [← Nat.mul_succ, show (t-1).succ = t by omega]
  have gateBound : A.size+2 ≤ t*t := by omega
  have e : ∃ i j, H.Adj i j := by
    by_contra! empty
    have tau := Loc.tau_le H ∅ (fun a b h => (empty a b h).elim)
    simp at tau
    omega
  obtain ⟨i,j,adj⟩ := e
  have output : A.output < m+A.size := by
    by_contra! no
    let x : Fin m → Bool := fun _ => true
    have off := ZeroFold.wval_past A x A.output no
    change circuitFun m A x = false at off
    rw [correct] at off
    have on : graphFun H ∅ x = true := by simp [graphFun,x,show ∃ a b, H.Adj a b from ⟨i,j,adj⟩]
    rw [on] at off
    contradiction
  have result := tests m bound H triH sqH sz crit active edges A ao correct output gateBound
  omega

/-- The two unrestricted desk statements follow from the stated finite test at each
cover number starting with five. -/
theorem both_of_tests (tests : ∀ t, 5 ≤ t → At t) : Exact1774 ∧ VertexPeel.ExactPeel := by
  constructor
  · intro n G dec tri sq
    change StepAt G
    by_cases easy : Loc.tau G ≤ 4
    · exact CoverFour.ownership_at_most_four G tri sq easy
    intro C least correct _ positive
    obtain ⟨T,c,ct⟩ := Loc.tau_attained G
    have lo := lift_at G tri sq rfl (by omega) (tests _ (by omega)) C least.1 correct
    apply coveredDescent G C T c _ positive
    rw [Set.ncard_eq_toFinset_card']
    change G.edgeFinset.card + T.card - 1 ≤ C.size
    omega
  · intro n G dec bip sq edges
    by_cases easy : Loc.tau G ≤ 4
    · exact CoverFour.bipartite_vertex_at_most_four G bip sq easy edges
    obtain ⟨color,proper⟩ := bip
    have tri : NoTriangles G := fun a b c ab bc ca =>
      (by decide : ∀ x y z : Bool, x ≠ y → y ≠ z → z ≠ x → False)
        (color a) (color b) (color c) (proper a b ab) (proper b c bc) (proper c a ca)
    obtain ⟨z,pos,remaining⟩ := nonemptyCut G edges
    refine ⟨z,pos,?_⟩
    intro C ao correct
    obtain ⟨T,c,ct⟩ := Loc.tau_attained G
    have mono : Monotone2 C := fun g hg =>
      ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ao.1 g hg,(ao.2.2 g hg).le⟩
    have lo := lift_at G tri sq rfl (by omega) (tests _ (by omega)) C mono correct
    exact atVertexOfCoverBound G z remaining C ⟨T,c,by omega⟩

#print axioms lift_at
#print axioms both_of_tests
end VertexPeel.BoundedChecks
