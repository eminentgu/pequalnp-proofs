import SupportPacking

namespace VertexPeel.BatchExchange

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.MetaComplexity.CoverPromise PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2668 (val bypass bypass_length bypass_mono mono_ops bypass_eval_rel
  opMono_imp opMono_reverse graph_true circuit_monotone)

/-- Inputs are represented as vertex sets when recording negative assignments. -/
def indicator {n} (I : Finset (Fin n)) (v : Fin n) : Bool := decide (v ∈ I)

def MaxIndependent {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (I : Finset (Fin n)) : Prop :=
  graphFun G ∅ (indicator I)=false ∧ ∀ J, I ⊆ J → graphFun G ∅ (indicator J)=false → J=I

theorem extend_negative {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) (neg : graphFun G ∅ x=false) :
    ∃ I, MaxIndependent G I ∧ ∀ v, x v=true → v ∈ I := by
  classical
  let S := Finset.univ.filter fun v => x v=true
  have ind : indicator S = x := by
    funext i
    simp [S,indicator]
  let F := Finset.univ.filter (fun J : Finset (Fin n) => S ⊆ J ∧ graphFun G ∅ (indicator J)=false)
  have init : S ∈ F := by simp [F,ind,neg]
  obtain ⟨I,hI,largest⟩ := F.exists_max_image Finset.card ⟨S,init⟩
  obtain ⟨cont,indep⟩ := (Finset.mem_filter.mp hI).2
  refine ⟨I,⟨indep,?_⟩,fun v hv => cont (by simp [S,hv])⟩
  intro J sup good
  have member : J ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,cont.trans sup,good⟩
  exact (Finset.eq_of_subset_of_card_le sup (largest J member)).symm

/-- A non-equivalent monotone circuit either loses an actual edge, or accepts a
maximal independent set. A maximal negative input is allowed to have arbitrary size. -/
theorem boundary_error {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit)
    (mono : Monotone2 D) (wrong : circuitFun n D ≠ graphFun G ∅) :
    (∃ a b, G.Adj a b ∧ circuitFun n D (pairInput a b)=false) ∨
    ∃ I, MaxIndependent G I ∧ circuitFun n D (indicator I)=true := by
  classical
  by_cases loss : ∃ a b, G.Adj a b ∧ circuitFun n D (pairInput a b)=false
  · exact Or.inl loss
  right
  by_contra no
  apply wrong
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro yes
    by_contra falseG
    obtain ⟨I,hI,extendsX⟩ := extend_negative G x (Bool.eq_false_iff.mpr falseG)
    apply no ⟨I,hI,?_⟩
    apply circuit_monotone n D mono x (indicator I) _ yes
    simpa [indicator] using extendsX
  · intro yes
    obtain ⟨a,b,ab,ha,hb⟩ := (graph_true G x).mp yes
    apply circuit_monotone n D mono (pairInput a b) x
    · intro i hi
      rcases (show i=a ∨ i=b by simpa [pairInput] using hi) with rfl|rfl <;> assumption
    · cases h : circuitFun n D (pairInput a b) with
      | true => exact h
      | false => exact (loss ⟨a,b,ab,h⟩).elim

/-- Substituting an earlier wire for a gate in a minimum circuit has a signed
pivotal witness. Both the gate and wire values, and the wrong *output*, are specified. -/
theorem signed_pivot {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (least : IsMinimalMonoCircuit n C) (correct : circuitFun n C = graphFun G ∅)
    (j : Fin C.size) (w : Nat) (earlier : w<n+j.val ∨ n+C.size ≤ w) :
    (∃ a b, G.Adj a b ∧ gateVal n C j.val (pairInput a b)=true ∧
      val C (List.ofFn (pairInput a b)) w=false ∧ circuitFun n (bypass n C j.val w) (pairInput a b)=false) ∨
    ∃ I, MaxIndependent G I ∧ gateVal n C j.val (indicator I)=false ∧
      val C (List.ofFn (indicator I)) w=true ∧ circuitFun n (bypass n C j.val w) (indicator I)=true := by
  let D := bypass n C j.val w
  have dm : Monotone2 D := bypass_mono least.1
  have wrong : circuitFun n D ≠ graphFun G ∅ := by
    intro good
    have le := least.2 D dm (good.trans correct.symm)
    have sz : D.size=C.size-1 := bypass_length ..
    have pos := j.isLt
    omega
  rcases boundary_error G D dm wrong with ⟨a,b,ab,no⟩|⟨I,hI,yes⟩
  · left
    have orig : circuitFun n C (pairInput a b)=true := by
      rw [correct]
      exact (graph_true G _).mpr ⟨a,b,ab,by simp [pairInput],by simp [pairInput]⟩
    have strict : ¬ (gateVal n C j.val (pairInput a b)=true →
        val C (List.ofFn (pairInput a b)) w=true) := by
      intro inc
      have changed := bypass_eval_rel (R:=fun a b => a=true → b=true) (fun _ => id)
        opMono_imp (n:=n) (C:=C) (by simp) (mono_ops least.1) j.isLt earlier inc orig
      exact Bool.noConfusion (no.symm.trans changed)
    exact ⟨a,b,ab,by by_contra ng; exact strict (fun x => (ng x).elim),
      Bool.eq_false_iff.mpr (fun x => strict (fun _ => x)),no⟩
  · right
    have orig : circuitFun n C (indicator I)=false := by rw [correct]; exact hI.1
    have strict : ¬ (val C (List.ofFn (indicator I)) w=true →
        gateVal n C j.val (indicator I)=true) := by
      intro dec
      have changed := bypass_eval_rel (R:=fun a b => b=true → a=true) (fun _ => id)
        opMono_reverse (n:=n) (C:=C) (by simp) (mono_ops least.1) j.isLt earlier dec yes
      exact Bool.noConfusion (orig.symm.trans changed)
    exact ⟨I,hI,Bool.eq_false_iff.mpr (fun x => strict (fun _ => x)),
      by by_contra nw; exact strict (fun x => (nw x).elim),yes⟩

#print axioms boundary_error
#print axioms signed_pivot
end VertexPeel.BatchExchange
