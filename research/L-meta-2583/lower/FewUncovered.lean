import UncoveredEdges
import PEqualNP.Outside.L_meta_1490
import PEqualNP.Outside.L_meta_1505
import PEqualNP.Outside.L_meta_1501

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open scoped Sym2

namespace PlaneReadOne

/-- A mixing OR has an operand with no raw input reached by OR gates. Both
operands of a lambda gate must reach a raw input. -/
private theorem mixingOutside {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) {m : ℕ} (hm : m ∈ mixing G C) : m ∈ orN G C \ lam G C := by
  obtain ⟨outside,diff⟩ := Finset.mem_filter.mp hm
  refine Finset.mem_sdiff.mpr ⟨outside,?_⟩
  intro hl
  obtain ⟨_,left,right,_⟩ := Finset.mem_filter.mp hl
  exact diff (propext ⟨fun h => (left.ne_empty h).elim,fun h => (right.ne_empty h).elim⟩)

/-- An uncovered edge costs at least two units in the L1491 accounting.
With one dirty AND, either its top has an empty side or the path contains a
mixing OR. -/
theorem costOfUncovered {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (squareFree : NoFourCycle G) (hasEdge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (normal : TopForm G C) (missing : (Ustar G C).Nonempty) :
    2 ≤ 2*(centreless G C).card+(junk G C).card+(orN G C \ lam G C).card := by
  classical
  obtain ⟨e,he⟩ := missing
  induction e using Sym2.inductionOn with
  | _ u v =>
    obtain ⟨a,ha,b,h,hh,_,path,_⟩ :=
      (PEqualNP.Outside.L_meta_1490 n G C squareFree hasEdge least normal).2 u v he
    have junkPos : 0 < (junk G C).card := Finset.card_pos.mpr ⟨h,hh⟩
    by_cases many : 2 ≤ (junk G C).card
    · omega
    have only : (junk G C).card = 1 := by omega
    obtain ⟨g,sg⟩ := Finset.card_eq_one.mp only
    have same : h = g := by simpa [sg] using hh
    subst h
    by_cases sideEmpty : side (n:=n) C a b = ∅
    · have hasCenterless : a ∈ centreless G C := by
        apply Finset.mem_filter.mpr
        exact ⟨ha,by fin_cases b <;> first | exact Or.inl sideEmpty | exact Or.inr sideEmpty⟩
      have cnt : 0 < (centreless G C).card := Finset.card_pos.mpr ⟨a,hasCenterless⟩
      omega
    · obtain ⟨m,hm,_,_⟩ := PEqualNP.Outside.L_meta_1505 n G C squareFree hasEdge least normal
          g sg a ha b path (Finset.nonempty_iff_ne_empty.mpr sideEmpty)
      have cnt := Finset.card_pos.mpr ⟨m,mixingOutside G C hm⟩
      omega

variable {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (q : ℕ) (C : Circuit)
    (hq : 2 ≤ q) (order : N = q^2+q+1)
    (lines : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)

include order lines in
private theorem planeHasEdge : (graph I).edgeFinset.Nonempty := by
  have enough := edges I q lines
  have positive : 0 < N := by omega
  exact Finset.card_pos.mp ((Nat.mul_pos positive (Nat.zero_lt_succ q)).trans_le enough)

include hq order lines unique in
/-- Two or fewer uncovered incidences suffice for the sharp threshold at every
order q ≥ 2. -/
theorem twoUncovered (least : IsLeastAO (graph I) C) (normal : TopForm (graph I) C)
    (few : (Ustar (graph I) C).card ≤ 2) : N*(q+2) ≤ C.size+1 := by
  let G := graph I
  have bound := uncoveredCharge I q C hq order lines unique least normal
  change N*(q+2)+2*(centreless G C).card+(junk G C).card+(orN G C \ lam G C).card ≤
    C.size+1+(Ustar G C).card+(Ustar G C).card/(q+1) at bound
  change (Ustar G C).card ≤ 2 at few
  have divZero : (Ustar G C).card/(q+1) = 0 := Nat.div_eq_of_lt (by omega)
  by_cases nonempty : (Ustar G C).Nonempty
  · have pay := costOfUncovered G C (noFour I unique)
      (planeHasEdge I q order lines) least normal nonempty
    omega
  · have noEdges : (Ustar G C).card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp nonempty)
    omega

private theorem leastCircuit {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (ao : IsAO2 n C) (ev : circuitFun n C = graphFun G ∅) :
    ∃ D, IsLeastAO G D ∧ D.size ≤ C.size := by
  classical
  let realizable (k : ℕ) := ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size = k
  have bounded : ∃ k, realizable k := ⟨C.size,C,ao,ev,rfl⟩
  obtain ⟨D,dAO,dEval,cost⟩ := Nat.find_spec bounded
  have least : IsLeastAO G D := ⟨dAO,dEval,fun A aAO aEval => by
    rw [cost]; exact Nat.find_min' bounded ⟨A,aAO,aEval,rfl⟩⟩
  exact ⟨D,least,least.2.2 C ao ev⟩

include hq order lines unique in
/-- Any unrestricted counterexample can be chosen in top form with at least
three distinct incidences outside all of its top stars. -/
theorem threeMissing (ao : IsAO2 (N+N) C)
    (evaluates : ∀ z : Fin (N+N) → Bool, circuitFun (N+N) C z =
      decide (∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (small : C.size+1 < N*(q+2)) :
    ∃ D : Circuit, IsLeastAO (graph I) D ∧ TopForm (graph I) D ∧ D.size ≤ C.size ∧
        3 ≤ (Ustar (graph I) D).card := by
  have func : circuitFun (N+N) C = graphFun (graph I) ∅ := by
    funext z
    rw [evaluates]
    simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or]
    exact decide_eq_decide.mpr (graph_eval I z).symm
  obtain ⟨A,amin,alen⟩ := leastCircuit (graph I) C ao func
  obtain ⟨D,least,len,_,normal⟩ := PEqualNP.Outside.L_meta_1501 (N+N) (graph I) A
    (planeHasEdge I q order lines) amin
  refine ⟨D,least,normal,len.le.trans alen,?_⟩
  by_contra! few
  have bound := twoUncovered I q D hq order lines unique least normal (by omega)
  omega

end PlaneReadOne

#print axioms PlaneReadOne.twoUncovered
#print axioms PlaneReadOne.threeMissing
