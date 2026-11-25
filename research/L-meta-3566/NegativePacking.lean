import SignedExchange

namespace VertexPeel.BatchExchange

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.MetaComplexity.CoverPromise PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2668 (val bypass bypass_length bypass_mono mono_ops bypass_eval_rel
  opMono_imp opMono_reverse graph_true circuit_monotone OpMono bypass_val_lt)

private def reroute {n : Nat} (wire : Nat → Nat) (C : Circuit) : List Nat → Circuit
  | [] => C
  | k::tail => reroute (n:=n) wire (bypass n C k (wire k)) tail

private theorem reroute_size {n} (wire : Nat → Nat) (C : Circuit) (mono : Monotone2 C)
    (ks : List Nat) (ok : valid C.size ks) :
    Monotone2 (reroute (n:=n) wire C ks) ∧ (reroute (n:=n) wire C ks).size+ks.length=C.size := by
  induction ks generalizing C with
  | nil => exact ⟨mono,by simp [reroute]⟩
  | cons k ks ih =>
    let D := bypass n C k (wire k)
    have len : D.size=C.size-1 := bypass_length ..
    obtain ⟨hk,rest⟩ := ok
    obtain ⟨dm,sz⟩ := ih D (bypass_mono mono) (len.symm ▸ rest)
    refine ⟨dm,?_⟩
    change (reroute (n:=n) wire D ks).size+(k::ks).length=C.size
    rw [List.length_cons]
    omega

private theorem reroute_on {n} {R : Bool → Bool → Prop} (reflexive : ∀ b, R b b)
    (trans : ∀ {a b c}, R a b → R b c → R a c) (ops : OpMono R) (wire : Nat → Nat) (C : Circuit)
    (mono : Monotone2 C) (ks : List Nat) (order : ks.Pairwise (· > ·))
    (inside : ∀ j ∈ ks, j<C.size) (earlier : ∀ j ∈ ks, wire j<n+j) (x : Fin n → Bool)
    (sign : ∀ j ∈ ks, R (val C (List.ofFn x) (n+j)) (val C (List.ofFn x) (wire j))) :
    R (circuitFun n C x) (circuitFun n (reroute (n:=n) wire C ks) x) := by
  induction ks generalizing C with
  | nil => exact reflexive _
  | cons j ks ih =>
    let D := bypass n C j (wire j)
    have len : D.size=C.size-1 := bypass_length ..
    obtain ⟨before,sort⟩ := List.pairwise_cons.mp order
    have hj := inside j (List.mem_cons_self ..)
    have hi := earlier j (List.mem_cons_self ..)
    apply trans (bypass_eval_rel reflexive ops (n:=n) (C:=C) (by simp) (mono_ops mono)
      hj (Or.inl hi) (sign j (List.mem_cons_self ..)))
    apply ih D (bypass_mono mono) sort
    · intro k h
      have := before k h
      omega
    · exact fun k h => earlier k (List.mem_cons_of_mem _ h)
    · intro k h
      have lt := before k h
      have wh := earlier k (List.mem_cons_of_mem _ h)
      have old (w : Nat) (hw : w<n+j) : val D (List.ofFn x) w = val C (List.ofFn x) w :=
        bypass_val_lt (n:=n) (by simp) hj w hw
      rw [old _ (by omega),old _ (by omega)]
      exact sign k (List.mem_cons_of_mem _ h)

/-- On a maximal independent input, the proposed earlier wire turns a false original
gate into a true one. Such a replacement can allow a false positive at the output. -/
noncomputable def gains {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (wire : Nat → Nat) (j : Fin C.size) : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter fun I => MaxIndependent G I ∧
    gateVal n C j.val (indicator I)=false ∧ val C (List.ofFn (indicator I)) (wire j.val)=true

/-- If the replacement wire dominates its gate on every genuine edge, any savings
from simultaneous replacement must be paid for by the union of the negative witnesses. -/
theorem negative_union {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (edge : ∃ a b, G.Adj a b)
    (C : Circuit) (least : IsMinimalMonoCircuit n C) (correct : circuitFun n C = graphFun G ∅)
    (wire : Nat → Nat) (S : Finset (Fin C.size)) (earlier : ∀ j ∈ S, wire j.val<n+j.val)
    (dominates : ∀ j ∈ S, ∀ a b, G.Adj a b → gateVal n C j.val (pairInput a b)=true →
      val C (List.ofFn (pairInput a b)) (wire j.val)=true) :
    S.card ≤ ∑ I ∈ S.biUnion (gains G C wire), Iᶜ.card := by
  classical
  let U := S.image Fin.val
  let ks := U.sort (· ≥ ·)
  have order : ks.Pairwise (· > ·) := U.sortedGT_sort.pairwise
  have member (j) : j ∈ ks ↔ ∃ i ∈ S, Fin.val i = j := by simp [ks,U]
  have inside (j) (hj : j ∈ ks) : j < C.size := by
    obtain ⟨i,_,rfl⟩ := (member j).mp hj
    exact i.isLt
  have past (j) (hj : j ∈ ks) : wire j < n+j := by
    obtain ⟨i,hi,rfl⟩ := (member j).mp hj
    exact earlier i hi
  have ksize : ks.length=S.card := by simp [ks,U,Finset.card_image_of_injective _ Fin.val_injective]
  let D := reroute (n:=n) wire C ks
  obtain ⟨dm,len⟩ := reroute_size (n:=n) wire C least.1 ks (sorted_valid order inside)
  change Monotone2 D at dm
  change D.size+ks.length=C.size at len
  rw [ksize] at len
  have positive (a b) (ab : G.Adj a b) : circuitFun n D (pairInput a b)=true := by
    have orig : circuitFun n C (pairInput a b)=true := by
      rw [correct]
      exact (graph_true G _).mpr ⟨a,b,ab,by simp [pairInput],by simp [pairInput]⟩
    apply reroute_on (R:=fun a b => a=true → b=true) (fun _ => id) (fun a b => b ∘ a)
      opMono_imp wire C least.1 ks order inside past (pairInput a b) _ orig
    intro j hj
    obtain ⟨i,hi,rfl⟩ := (member j).mp hj
    exact dominates i hi a b ab
  have inc : falsePositives G D ⊆ S.biUnion (gains G C wire) := by
    intro I hI
    obtain ⟨maximal,yes⟩ := (Finset.mem_filter.mp hI).2
    by_contra absent
    have wrong : circuitFun n C (indicator I)=true := by
      apply reroute_on (R:=fun a b => b=true → a=true) (fun _ => id) (fun a b => a ∘ b)
        opMono_reverse wire C least.1 ks order inside past (indicator I) _ yes
      intro j hj
      obtain ⟨i,hi,rfl⟩ := (member j).mp hj
      intro on
      by_contra off
      apply absent (Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,maximal,Bool.eq_false_iff.mpr off,on⟩⟩)
    rw [correct,maximal.1] at wrong
    contradiction
  obtain ⟨B,bm,sz,below,agree⟩ := negative_patch G edge D dm
  have bc : circuitFun n B=graphFun G ∅ := by
    by_contra wrong
    rcases boundary_error G B bm wrong with ⟨a,b,ab,off⟩|⟨I,maximal,on⟩
    · have orig := (graph_true G (pairInput a b)).mpr ⟨a,b,ab,by simp [pairInput],by simp [pairInput]⟩
      rw [agree _ orig,positive a b ab] at off
      contradiction
    · exact Bool.noConfusion (maximal.1.symm.trans (below _ on))
  have minimal := least.2 B bm (bc.trans correct.symm)
  have sum : (∑ I ∈ falsePositives G D, Iᶜ.card) ≤ ∑ I ∈ S.biUnion (gains G C wire), Iᶜ.card :=
    Finset.sum_le_sum_of_subset_of_nonneg inc (by simp)
  omega

/-- The negative witnesses can be assigned simultaneously. Each selected gate gets its
own pair of a separating maximal independent input and a vertex outside that input. -/
theorem negative_assignment {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (edge : ∃ a b, G.Adj a b)
    (C : Circuit) (least : IsMinimalMonoCircuit n C) (correct : circuitFun n C = graphFun G ∅)
    (wire : Nat → Nat) (S : Finset (Fin C.size)) (earlier : ∀ j ∈ S, wire j.val<n+j.val)
    (dominates : ∀ j ∈ S, ∀ a b, G.Adj a b → gateVal n C j.val (pairInput a b)=true →
      val C (List.ofFn (pairInput a b)) (wire j.val)=true) :
    ∃ f : S → Σ _ : Finset (Fin n), Fin n, Function.Injective f ∧
      ∀ j, (f j).1 ∈ gains G C wire j.val ∧ (f j).2 ∉ (f j).1 := by
  classical
  let options (j : S) := (gains G C wire j.val).sigma (fun I => Iᶜ)
  have hall (T : Finset S) : T.card ≤ (T.biUnion options).card := by
    let Q := T.image Subtype.val
    have inclusion : Q ⊆ S := by
      intro j hj
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hj
      exact i.property
    have bound := negative_union G edge C least correct wire Q
      (fun j h => earlier j (inclusion h)) (fun j h => dominates j (inclusion h))
    have card : Q.card=T.card := Finset.card_image_of_injective _ Subtype.val_injective
    let F := Q.biUnion (gains G C wire)
    have allSlots : F.sigma (fun I => Iᶜ) ⊆ T.biUnion options := by
      rintro ⟨I,v⟩ member
      obtain ⟨gain,outside⟩ := Finset.mem_sigma.mp member
      obtain ⟨j,hj,win⟩ := Finset.mem_biUnion.mp gain
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_sigma.mpr ⟨win,outside⟩⟩
    rw [card] at bound
    exact bound.trans ((Finset.card_sigma ..) ▸ Finset.card_le_card allSlots)
  obtain ⟨f,inj,mem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' options).mp hall
  refine ⟨f,inj,?_⟩
  intro j
  obtain ⟨inG,outside⟩ := Finset.mem_sigma.mp (mem j)
  exact ⟨inG,Finset.mem_compl.mp outside⟩

/-- In particular this applies to every AND gate at once, with either one of its
actual parents chosen independently at each gate. No edge-domination assumption is needed. -/
theorem and_parent_assignment {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (edge : ∃ a b, G.Adj a b) (C : Circuit) (least : IsMinimalMonoCircuit n C)
    (correct : circuitFun n C = graphFun G ∅) (back : ReadsBack n C) (wire : Nat → Nat)
    (S : Finset (Fin C.size)) (ands : ∀ j ∈ S, (gateAt C j.val).op=GateOp.and)
    (parents : ∀ j ∈ S, wire j.val ∈ (gateAt C j.val).inputs) :
    ∃ f : S → Σ _ : Finset (Fin n), Fin n, Function.Injective f ∧
      ∀ j, MaxIndependent G (f j).1 ∧ gateVal n C j.val.val (indicator (f j).1)=false ∧
        val C (List.ofFn (indicator (f j).1)) (wire j.val.val)=true ∧ (f j).2 ∉ (f j).1 := by
  classical
  have old (j) (h : j ∈ S) := back j.val j.isLt (wire j.val) (parents j h)
  obtain ⟨f,inj,props⟩ := negative_assignment G edge C least correct wire S old (by
    intro j hj a b _ on
    exact ((PEqualNP.Outside.L_meta_2668.val_and (n:=n) (C:=C) (x:=List.ofFn (pairInput a b))
      (by simp) j.isLt (ands j hj)).mp on (wire j.val) (parents j hj)).2)
  refine ⟨f,inj,?_⟩
  intro j
  obtain ⟨hit,out⟩ := props j
  obtain ⟨I,off,on⟩ := (Finset.mem_filter.mp hit).2
  exact ⟨I,off,on,out⟩

#print axioms and_parent_assignment
#print axioms negative_assignment
#print axioms negative_union
end VertexPeel.BatchExchange
