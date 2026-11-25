import MixedFoldAnd
import PEqualNP.Outside.L_meta_1527

namespace VertexPeel.NormalizeCount

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.Outside.L_meta_1527

attribute [local instance] gateOpDecEq

private noncomputable def count (gs : List Gate) :=
  (gs.filter (fun g => @decide (g.op=GateOp.and) (Classical.propDecidable _))).length

private theorem snoc (gs : List Gate) (g : Gate) :
    count (gs++[g]) = count gs + (if g.op=GateOp.and then 1 else 0) := by
  classical
  by_cases h : g.op=GateOp.and <;> simp [count,h]

private theorem or_wire {n : Nat} (gs : List Gate) (f g : (Fin n → Bool) → Bool)
    (left : Rep gs f) (right : Rep gs g) :
    ∃ ns, Ext n gs ns ∧ count ns=count gs ∧ Rep ns (fun x => f x || g x) := by
  rcases left with ⟨c,h⟩|⟨a,ha,fa⟩
  · cases c
    · exact ⟨gs,Or.inl rfl,rfl,rep_congr (fun x => by simp [h x]) right⟩
    · exact ⟨gs,Or.inl rfl,rfl,Or.inl ⟨true,fun x => by simp [h x]⟩⟩
  rcases right with ⟨c,h⟩|⟨b,hb,fb⟩
  · cases c
    · refine ⟨gs,Or.inl rfl,rfl,Or.inr ⟨a,ha,?_⟩⟩
      intro x
      change _ = (f x || g x)
      rw [h x,Bool.or_false,fa x]
    · exact ⟨gs,Or.inl rfl,rfl,Or.inl ⟨true,fun x => by simp [h x]⟩⟩
  let q : Gate := ⟨.or,[a,b]⟩
  refine ⟨gs++[q],Or.inr ⟨q,rfl,⟨Or.inr rfl,rfl⟩,?_⟩,by simp [snoc,q],
    Or.inr ⟨n+gs.length,by simp,?_⟩⟩
  · intro i hi
    rcases (show i=a ∨ i=b by simpa [q] using hi) with rfl|rfl <;> assumption
  · intro x
    rw [W_val,ite_eq_left rfl]
    change GateOp.or.eval [(W gs x).getD a false,(W gs x).getD b false] = _
    rw [fa x,fb x]
    simp [GateOp.eval]

private theorem one_step {n : Nat} (old new : List Gate) (q : Gate) (op : q.op=.and ∨ q.op=.or)
    (ar : q.inputs.length≤2) (known : ∀ t, Rep new (fun x : Fin n → Bool => (W old x).getD t false)) :
    ∃ ns, Ext n new ns ∧ count ns ≤ count new + (if q.op=.and then 1 else 0) ∧
      Rep ns (fun x : Fin n → Bool => q.op.eval (q.inputs.map fun i => (W old x).getD i false)) := by
  classical
  cases q with
  | mk o inputs =>
    change o=.and ∨ o=.or at op
    rcases op with rfl|rfl
    · obtain ⟨ns,ext,rep⟩ := gate_rep (n:=n) id old new .and inputs (Or.inl rfl) ar known
      refine ⟨ns,ext,?_,rep⟩
      rcases ext with rfl|⟨g,rfl,_,_⟩
      · simp
      · simp only [snoc]
        split <;> simp
    · change inputs.length≤2 at ar
      rcases inputs with _|⟨a,_|⟨b,_|⟨c,rest⟩⟩⟩
      · exact ⟨new,Or.inl rfl,by simp,Or.inl ⟨false,by simp [GateOp.eval]⟩⟩
      · exact ⟨new,Or.inl rfl,by simp,rep_congr (fun x => by simp [GateOp.eval]) (known a)⟩
      · obtain ⟨ns,ext,cnt,rep⟩ := or_wire new _ _ (known a) (known b)
        exact ⟨ns,ext,by simp [cnt],rep_congr (fun x => by simp [GateOp.eval]) rep⟩
      · simp at ar

private def Represents (n : Nat) (old : List Gate) : Prop :=
  ∃ new : List Gate, (∀ g∈new, Fan g) ∧ RB n new ∧ count new≤count old ∧
    ∀ t, Rep new (fun x : Fin n → Bool => (W old x).getD t false)

private theorem push {n} {old : List Gate} (q : Gate) (op : q.op=.and ∨ q.op=.or)
    (ar : q.inputs.length≤2) (prev : Represents n old) : Represents n (old++[q]) := by
  obtain ⟨new,fan,rb,cnt,rep⟩ := prev
  obtain ⟨ns,ext,bound,added⟩ := one_step old new q op ar rep
  refine ⟨ns,?_,?_,bound.trans (by rw [snoc]; omega),?_⟩
  · rcases ext with rfl|⟨g,rfl,fg,_⟩
    · exact fan
    · intro h inside
      rcases List.mem_append.mp inside with own|last
      · exact fan h own
      · exact List.mem_singleton.mp last ▸ fg
  · rcases ext with rfl|⟨g,rfl,_,ok⟩
    · exact rb
    · exact rb_snoc rb ok
  · intro i
    by_cases top : i=n+old.length
    · apply rep_congr _ added
      intro x
      rw [W_val,ite_eq_left top]
    · apply rep_congr _ (rep_mono ext _ (rep i))
      intro x; rw [W_val,ite_eq_right top]

/-- Public Monotone2 circuits normalize without increasing the AND count whenever
their function takes value false on the all-false input. -/
theorem normalize {n} (C : Circuit) (mono : Monotone2 C) (zero : circuitFun n C (fun _ => false)=false) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D=circuitFun n C ∧
      (PivotAND.physical D).card≤(PivotAND.physical C).card := by
  classical
  have build (gs : List Gate) (valid : ∀ g∈gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) :
      Represents n gs := by
    induction gs using List.reverseRecOn with
    | nil => exact ⟨[],by simp,by intro i hi; simp at hi,le_rfl,rep_input id (fun _ => Or.inr (fun _ => rfl))⟩
    | append_singleton old q ih =>
      have vq := valid q (by simp)
      exact push q vq.1 vq.2 (ih (fun g hg => valid g (List.mem_append_left _ hg)))
  obtain ⟨new,fan,rb,cost,known⟩ := build C.gates mono
  rcases known C.output with ⟨b,fixed⟩|⟨i,_,val⟩
  · have off : ∀ x, circuitFun n C x=false := fun x => (fixed x).trans ((fixed _).symm.trans zero)
    refine ⟨⟨[],n⟩,⟨by simp [PEqualNP.EdgeOwnership.AndOrOnly],by intro i hi; simp at hi,by simp⟩,
      funext (fun x => ?_),?_⟩
    · rw [off]
      change (List.ofFn x).getD n false=false
      exact List.getD_eq_default _ _ (by simp)
    · simp [PivotAND.physical,Circuit.size]
  · refine ⟨⟨new,i⟩,⟨fun g h => (fan g h).1,rb,fun g h => (fan g h).2⟩,funext val,?_⟩
    simpa only [PivotAND.physical_count,count] using cost

#print axioms normalize
end VertexPeel.NormalizeCount
