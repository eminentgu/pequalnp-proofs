import SignedPivots

namespace VertexPeel.BatchExchange

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.MetaComplexity.CoverPromise PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2668 (graph_true circuit_monotone)
open VertexPeel.CoverCircuit (bld_anyFinset)

/-- Maximal independent inputs where an arbitrary proposed circuit makes a false positive. -/
noncomputable def falsePositives {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit) :
    Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter fun I => MaxIndependent G I ∧ circuitFun n D (indicator I)=true

private theorem compile_clauses {n} (D : Circuit) (dm : Monotone2 D) (F : Finset (Finset (Fin n)))
    (proper : ∀ I ∈ F, Iᶜ.Nonempty) : ∃ B : Circuit, Monotone2 B ∧ B.size ≤ D.size + ∑ I ∈ F, Iᶜ.card ∧
      ∀ x, circuitFun n B x=true ↔ circuitFun n D x=true ∧ ∀ I ∈ F, ∃ v ∉ I, x v=true := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨D,dm,by simp,by simp⟩
  | @insert I F fresh ih =>
    obtain ⟨A,am,asize,act⟩ := ih (fun J hJ => proper J (Finset.mem_insert_of_mem hJ))
    have present := proper I (Finset.mem_insert_self _ _)
    obtain ⟨B,bm,bsize,run⟩ := finishWith A am _ _ .and (Or.inl rfl)
      (bld_anyFinset (P:=fun _ => True) Iᶜ present)
    refine ⟨B,bm,?_,?_⟩
    · rw [Finset.sum_insert fresh]
      have pos := Finset.card_pos.mpr present
      omega
    · intro x
      rw [run]
      simp only [GateOp.eval,List.all_cons,id_eq,List.all_nil,Bool.and_true,Bool.and_eq_true,
        decide_eq_true_eq,Finset.mem_compl,act,Finset.forall_mem_insert]
      tauto

private theorem positive_outside {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (I : Finset (Fin n))
    (ind : MaxIndependent G I) (x : Fin n → Bool) (pos : graphFun G ∅ x=true) :
    ∃ v ∉ I, x v=true := by
  classical
  obtain ⟨a,b,ab,ha,hb⟩ := (graph_true G x).mp pos
  by_cases aI : a ∈ I
  · refine ⟨b,?_,hb⟩
    intro bI
    have yes := (graph_true G (indicator I)).mpr ⟨a,b,ab,by simp [indicator,aI],by simp [indicator,bI]⟩
    exact Bool.noConfusion (ind.1.symm.trans yes)
  · exact ⟨a,aI,ha⟩

/-- Conjoining failed maximal-independent clauses removes all false positives;
the resulting circuit agrees with D on every graph-positive input, including all edge rows. -/
theorem negative_patch {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (edge : ∃ a b, G.Adj a b)
    (D : Circuit) (dm : Monotone2 D) : ∃ B : Circuit, Monotone2 B ∧
    B.size ≤ D.size + ∑ I ∈ falsePositives G D, Iᶜ.card ∧
    (∀ x, circuitFun n B x=true → graphFun G ∅ x=true) ∧
    ∀ x, graphFun G ∅ x=true → circuitFun n B x=circuitFun n D x := by
  classical
  let F := falsePositives G D
  have mem (I) : I ∈ F ↔ MaxIndependent G I ∧ circuitFun n D (indicator I)=true := by simp [F,falsePositives]
  have proper (I) (hI : I ∈ F) : Iᶜ.Nonempty := by
    obtain ⟨a,b,ab⟩ := edge
    have yes := (graph_true G (pairInput a b)).mpr ⟨a,b,ab,by simp [pairInput],by simp [pairInput]⟩
    obtain ⟨v,hv,_⟩ := positive_outside G I ((mem I).mp hI).1 _ yes
    exact ⟨v,Finset.mem_compl.mpr hv⟩
  obtain ⟨B,bm,size,act⟩ := compile_clauses D dm F proper
  refine ⟨B,bm,size,?_,?_⟩
  · intro x yes
    by_contra bad
    obtain ⟨I,maximal,extension⟩ := extend_negative G x (Bool.eq_false_iff.mpr bad)
    obtain ⟨dyes,clauses⟩ := (act x).mp yes
    have larger : circuitFun n D (indicator I)=true := by
      apply circuit_monotone n D dm x (indicator I) _ dyes
      simpa [indicator] using extension
    obtain ⟨v,outside,on⟩ := clauses I ((mem I).mpr ⟨maximal,larger⟩)
    exact outside (extension v on)
  · intro x yes
    apply Bool.eq_iff_iff.mpr
    rw [act]
    exact ⟨And.left,fun dx => ⟨dx,fun I hI => positive_outside G I ((mem I).mp hI).1 x yes⟩⟩

/-- A physical two-sided repair of *any* monotone candidate, charged to the
missed edges and the falsely accepted maximal independent sets in the original graph. -/
theorem signed_exchange {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (edge : ∃ a b, G.Adj a b)
    (D : Circuit) (dm : Monotone2 D) : ∃ B : Circuit, Monotone2 B ∧ circuitFun n B = graphFun G ∅ ∧
    B.size ≤ D.size + (loss G D).edgeFinset.card + Loc.tau (loss G D) +
      ∑ I ∈ falsePositives G D, Iᶜ.card := by
  classical
  obtain ⟨A,am,sz,below,agree⟩ := negative_patch G edge D dm
  have same : loss G A = loss G D := by
    ext a b
    change (G.Adj a b ∧ _) ↔ (G.Adj a b ∧ _)
    by_cases ab : G.Adj a b
    · have yes := (graph_true G (pairInput a b)).mpr ⟨a,b,ab,by simp [pairInput],by simp [pairInput]⟩
      simp [ab,agree _ yes]
    · simp [ab]
  obtain ⟨T,cover,card⟩ := Loc.tau_attained (loss G A)
  obtain ⟨B,bm,correct,bound⟩ := patch G A am below T cover
  have equalEdges : (loss G A).edgeFinset = (loss G D).edgeFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    rw [same]
  rw [card,equalEdges,congrArg Loc.tau same] at bound
  refine ⟨B,bm,correct,?_⟩
  omega

#print axioms negative_patch
#print axioms signed_exchange
end VertexPeel.BatchExchange
