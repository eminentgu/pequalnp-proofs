import ZeroFold

namespace VertexPeel.MixedFold
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadTwo
open ZeroFold (two wval_gate wval_in wval_past run sB run_length)

abbrev Restr (n : ℕ) := (Fin n → Bool) → Fin n → Bool
def Const {α : Type} (f : α → Bool) : Prop := ∃ v, f = fun _ => v
def val (C : Circuit) (r : Restr n) (w : ℕ) (x : Fin n → Bool) : Bool := wval C (r x) w
def New (C : Circuit) (r : Restr n) (j : ℕ) : Prop :=
  j < C.gates.length ∧ (∀ a < n+j, val C r (n+j) ≠ val C r a) ∧ ¬Const (val C r (n+j))

theorem node (C : Circuit) (r : Restr n) {j a b : ℕ} (hj : j < C.gates.length)
    (ports : C.gates[j].inputs = [a,b]) (ha : a < n+j) (hb : b < n+j) (x : Fin n → Bool) :
    val C r (n+j) x = C.gates[j].op.eval [val C r a x,val C r b x] :=
  wval_gate C _ _ _ _ hj ports ha hb

theorem kill (C : Circuit) (ao : IsAO2 n C) (r : Restr n) {j w : ℕ} (hj : j < C.gates.length)
    (read : w ∈ C.gates[j].inputs) (wc : Const (val C r w)) : ¬New C r j := by
  obtain ⟨v,e⟩ := wc
  obtain ⟨a,b,ports,ha,hb,op⟩ := two n C ao j hj
  have hw : w=a ∨ w=b := by simpa [ports] using read
  rintro ⟨_,distinct,nonconst⟩
  rcases op with op | op <;> rcases hw with rfl | rfl <;> cases v
  · exact nonconst ⟨false,funext fun x => by simp [node C r hj ports ha hb,op,GateOp.eval,e]⟩
  · exact distinct _ hb (funext fun x => by simp [node C r hj ports ha hb,op,GateOp.eval,e])
  · exact nonconst ⟨false,funext fun x => by simp [node C r hj ports ha hb,op,GateOp.eval,e]⟩
  · exact distinct _ ha (funext fun x => by simp [node C r hj ports ha hb,op,GateOp.eval,e])
  · exact distinct _ hb (funext fun x => by simp [node C r hj ports ha hb,op,GateOp.eval,e])
  · exact nonconst ⟨true,funext fun x => by simp [node C r hj ports ha hb,op,GateOp.eval,e]⟩
  · exact distinct _ ha (funext fun x => by simp [node C r hj ports ha hb,op,GateOp.eval,e])
  · exact nonconst ⟨true,funext fun x => by simp [node C r hj ports ha hb,op,GateOp.eval,e]⟩

theorem both (C : Circuit) (ao : IsAO2 n C) (r : Restr n) {j u v : ℕ} (hj : j < C.gates.length)
    (ne : u ≠ v) (hu : u ∈ C.gates[j].inputs) (hv : v ∈ C.gates[j].inputs)
    (cu : Const (val C r u)) (cv : Const (val C r v)) : Const (val C r (n+j)) := by
  obtain ⟨s,es⟩ := cu
  obtain ⟨t,et⟩ := cv
  obtain ⟨a,b,ports,ha,hb,_⟩ := two n C ao j hj
  have uab : u=a ∨ u=b := by simpa [ports] using hu
  have vab : v=a ∨ v=b := by simpa [ports] using hv
  rcases uab with rfl | rfl <;> rcases vab with rfl | rfl
  · contradiction
  · exact ⟨_,funext fun x => by rw [node C r hj ports ha hb,es,et]⟩
  · exact ⟨_,funext fun x => by rw [node C r hj ports ha hb,es,et]⟩
  · contradiction

open Classical in
theorem canal (C : Circuit) (ao : IsAO2 n C) (r : Restr n) {j w : ℕ} (hj : j < C.gates.length)
    (read : w ∈ C.gates[j].inputs) (raw : val C r w = fun _ => decide (C.gates[j].op = .or)) :
    Const (val C r (n+j)) := by
  classical
  obtain ⟨a,b,ports,ha,hb,op⟩ := two n C ao j hj
  have hw : w=a ∨ w=b := by simpa [ports] using read
  refine ⟨decide (C.gates[j].op = .or),funext fun x => ?_⟩
  rw [node C r hj ports ha hb]
  rcases hw with rfl | rfl <;> rcases op with op | op <;> simp [raw,op,GateOp.eval]

def Rep (gs : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  Const f ∨ ∃ w < n + gs.length, f = fun x => wval (⟨gs,0⟩ : Circuit) x w
private theorem old_val (gs : List Gate) (g : Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : w < n + gs.length) :
    wval (⟨gs ++ [g],0⟩ : Circuit) x w = wval (⟨gs,0⟩ : Circuit) x w := by
  change ((gs ++ [g]).foldl (fun R h => R ++ [sB R h]) (List.ofFn x)).getD w false = _
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  apply List.getD_append
  change w < (run sB (List.ofFn x) gs).length
  simpa [run_length] using hw

private theorem Rep.snoc {gs : List Gate} {f : (Fin n → Bool) → Bool} (r : Rep gs f) (g : Gate) :
    Rep (gs ++ [g]) f := by
  rcases r with r | ⟨w,hw,r⟩
  · exact Or.inl r
  · exact Or.inr ⟨w,by simp; omega, r.trans (funext fun x => (old_val gs g x w hw).symm)⟩

private theorem appendAO {gs : List Gate} (old : IsAO2 n ⟨gs,0⟩) (a b : ℕ)
    (ha : a < n+gs.length) (hb : b < n+gs.length) (op : GateOp) (ho : op = .and ∨ op = .or) :
    IsAO2 n ⟨gs ++ [⟨op,[a,b]⟩],0⟩ := by
  let g : Gate := ⟨op,[a,b]⟩
  change IsAO2 n ⟨gs ++ [g],0⟩
  refine ⟨?_,?_,?_⟩
  · intro q hq
    rcases List.mem_append.mp hq with e | e
    · exact old.1 _ e
    · simpa using (List.mem_singleton.mp e ▸ ho : q.op = .and ∨ q.op = .or)
  · intro j hj i hi
    change i ∈ ((gs ++ [g]).getD j _).inputs at hi
    by_cases e : j < gs.length
    · rw [List.getD_append _ _ _ _ e] at hi
      exact old.2.1 j e i hi
    · have hlen : j < (gs ++ [g]).length := hj
      have ej : j = gs.length := by simp at hlen; omega
      subst j
      rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
      have hit : i = a ∨ i = b := by simpa [g] using hi
      rcases hit with rfl | rfl <;> assumption
  · intro q hq
    rcases List.mem_append.mp hq with e | e
    · exact old.2.2 _ e
    · rw [List.mem_singleton.mp e]; rfl

open Classical in
theorem compile_prefix (C : Circuit) (hC : IsAO2 n C) (r : Restr n) (raw : ∀ i : Fin n, Const (val C r i.val) ∨ val C r i.val = fun x => x i) (k : ℕ)
    (hk : k ≤ C.size) :
    ∃ gs : List Gate, IsAO2 n ⟨gs,0⟩ ∧ gs.length ≤ ((Finset.range k).filter (New C r)).card ∧
      ∀ w < n+k, Rep gs (val C r w) := by
  classical
  induction k with
  | zero =>
    have empty : IsAO2 n ⟨[],0⟩ := by
      refine ⟨?_,?_,?_⟩
      · intro g hg
        exact (List.not_mem_nil hg).elim
      · intro j hj
        exact (Nat.not_lt_zero _ hj).elim
      · intro g hg
        exact (List.not_mem_nil hg).elim
    refine ⟨[],empty,by simp,?_⟩
    intro w hw
    let i : Fin n := ⟨w,by omega⟩
    rcases raw i with e | e
    · exact Or.inl e
    · refine Or.inr ⟨w,by simp; omega,e.trans ?_⟩
      exact funext fun x => (wval_in (⟨[],0⟩ : Circuit) x i).symm
  | succ k ih =>
    obtain ⟨gs,hgs,hs,rep⟩ := ih (by omega)
    have hk' : k < C.gates.length := by exact Nat.lt_of_succ_le hk
    by_cases hm : New C r k
    · obtain ⟨a,b,hab,ha,hb,ho⟩ := two n C hC k hk'
      have dep (w : ℕ) (hit : w ∈ C.gates[k].inputs) : ¬Const (val C r w) :=
        fun e => (kill C hC r hk' hit e) hm
      obtain ⟨u,hu,eu⟩ := (rep a ha).resolve_left (dep a (by simp [hab]))
      obtain ⟨v,hv,ev⟩ := (rep b hb).resolve_left (dep b (by simp [hab]))
      let g : Gate := ⟨C.gates[k].op,[u,v]⟩
      refine ⟨gs ++ [g],appendAO hgs u v hu hv _ ho,?_,?_⟩
      · simpa [Finset.range_add_one, Finset.filter_insert, hm] using hs
      · intro w hw
        by_cases e : w < n+k
        · exact (rep w e).snoc g
        · have we : w = n+k := by omega
          subst w
          refine Or.inr ⟨n+gs.length,by simp,funext fun x => ?_⟩
          change wval C (r x) (n+k) = _
          rw [wval_gate C (r x) k a b hk' hab ha hb]
          have newGate := wval_gate (n := n) (⟨gs++[g],0⟩ : Circuit) x gs.length u v
            (by simp) (by simp [g]) hu hv
          rw [newGate]
          simp only [List.getElem_append_right (by omega : gs.length ≤ gs.length), Nat.sub_self,
            List.getElem_cons_zero]
          change C.gates[k].op.eval [val C r a x,val C r b x] = C.gates[k].op.eval [_,_]
          rw [eu,ev,old_val gs g x u hu,old_val gs g x v hv]
    · refine ⟨gs,hgs,?_,?_⟩
      · simpa [Finset.range_add_one,Finset.filter_insert,hm] using hs
      · intro w hw
        by_cases e : w < n+k
        · exact rep w e
        · have we : w = n+k := by omega
          subst w
          by_cases z : Const (val C r (n+k))
          · exact Or.inl z
          · have dup : ∃ a < n+k, val C r (n+k) = val C r a := by
              by_contra! bad
              exact hm ⟨hk',bad,z⟩
            obtain ⟨a,ha,ea⟩ := dup
            rw [ea]
            exact rep _ ha

open Classical in
theorem compile (C : Circuit) (hC : IsAO2 n C) (r : Restr n)
    (raw : ∀ i : Fin n, Const (val C r i.val) ∨ val C r i.val = fun x => x i)
    (nonconst : ¬Const (val C r C.output)) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = val C r C.output ∧
      D.size ≤ ((Finset.range C.size).filter (New C r)).card := by
  classical
  obtain ⟨gs,hg,hlen,rep⟩ := compile_prefix C hC r raw C.size le_rfl
  have valid : C.output < n+C.size := by
    by_contra! far
    exact nonconst ⟨false,funext fun x => wval_past C _ _ far⟩
  obtain ⟨w,_,ew⟩ := (rep _ valid).resolve_left nonconst
  exact ⟨⟨gs,w⟩,hg,ew.symm,hlen⟩

end VertexPeel.MixedFold
