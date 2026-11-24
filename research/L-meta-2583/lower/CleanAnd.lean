import PlaneReadOne
import PEqualNP.Outside.L_meta_1892

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

namespace PlaneReadOne

variable {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]

def Computes (C : Circuit) : Prop :=
  ∀ z : Fin (N+N) → Bool, circuitFun (N+N) C z =
    decide (∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)

omit [DecidableRel I] in
theorem cycleFree
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l) :
    ∀ a b c d, a ≠ c → b ≠ d →
      ¬ ((graph I).Adj a b ∧ (graph I).Adj b c ∧ (graph I).Adj c d ∧ (graph I).Adj d a) := by
  rintro a b c d ac bd ⟨ab,bc,cd,da⟩
  have common := Finset.card_le_one.mp (noFour I unique a c ac)
  apply bd (common b _ d _)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ab,bc.symm⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,da.symm,cd⟩

private theorem output_nonedge (C : Circuit) (eval : Computes I C)
    (u v : Fin (N+N)) (nonedge : ¬(graph I).Adj u v) :
    circuitFun (N+N) C (pairInput u v) = false := by
  rw [eval]
  apply decide_eq_false
  intro h
  obtain ⟨a,b,edge,ha,hb⟩ := (graph_eval I _).mpr h
  simp only [pairInput,decide_eq_true_eq] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (graph I).loopless.irrefl _ edge
  · exact nonedge edge
  · exact nonedge edge.symm
  · exact (graph I).loopless.irrefl _ edge

/-- A clean AND at a rejected two-position input produces false. Repeated
    positions are allowed, so the test includes singleton inputs. -/
def AndsRejectNonedges (C : Circuit) : Prop :=
  ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.and →
    ∀ u v : Fin (N+N), ¬(graph I).Adj u v → gateVal (N+N) C k (pairInput u v) = false

/-- Nested AND gates are permitted. Only their values on graph nonedges are tested. -/
theorem pairClean (q : ℕ) (C : Circuit) (hq : 2 ≤ q) (order : N = q^2+q+1)
    (lines : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
    (ao : IsAO2 (N+N) C) (eval : Computes I C) (clean : AndsRejectNonedges I C) :
    N*(q+2) ≤ C.size+1 := by
  classical
  apply ofCoverBound I q C hq order lines unique
  apply PEqualNP.Outside.L_meta_1892_aux.Clean.cleanBound (N+N) (graph I)
    (cycleFree I unique) C _ _ clean
  · intro g hg
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ao.1 g hg,
      (ao.2.2 g hg).le⟩
  · funext z
    rw [eval]
    simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or]
    exact decide_eq_decide.mpr (graph_eval I z).symm

/-- If truth of each AND implies truth of the output on every assignment,
    the circuit meets the star threshold even with nested ANDs. -/
theorem dominated (q : ℕ) (C : Circuit) (hq : 2 ≤ q) (order : N = q^2+q+1)
    (lines : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
    (ao : IsAO2 (N+N) C) (eval : Computes I C)
    (dom : ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.and →
      ∀ z, gateVal (N+N) C k z = true → circuitFun (N+N) C z = true) :
    N*(q+2) ≤ C.size+1 := by
  apply pairClean I q C hq order lines unique ao eval
  intro k hk hop u v nonedge
  cases h : gateVal (N+N) C k (pairInput u v) with
  | false => rfl
  | true =>
    have yes := dom k hk hop _ h
    rw [output_nonedge I C eval u v nonedge] at yes
    contradiction

/-- Any circuit below the threshold has an explicit AND and a rejected input
    supported on at most two positions which the AND accepts. -/
theorem dirtyWitness (q : ℕ) (C : Circuit) (hq : 2 ≤ q) (order : N = q^2+q+1)
    (lines : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
    (ao : IsAO2 (N+N) C) (eval : Computes I C) (small : C.size+1 < N*(q+2)) :
    ∃ k, k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ∃ u v : Fin (N+N), ¬(graph I).Adj u v ∧ gateVal (N+N) C k (pairInput u v) = true ∧
        circuitFun (N+N) C (pairInput u v) = false := by
  by_contra missing
  apply (Nat.not_le.mpr small) (pairClean I q C hq order lines unique ao eval ?_)
  intro k hk hop u v nonedge
  cases h : gateVal (N+N) C k (pairInput u v) with
  | false => rfl
  | true => exact (missing ⟨k,hk,hop,u,v,nonedge,h,output_nonedge I C eval u v nonedge⟩).elim

end PlaneReadOne

#print axioms PlaneReadOne.pairClean
#print axioms PlaneReadOne.dominated
#print axioms PlaneReadOne.dirtyWitness
