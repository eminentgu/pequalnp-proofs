import ZeroFold

namespace VertexPeel.RowFold

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK PEqualNP.ReadTwo PEqualNP.Core
open VertexPeel.ZeroFold hiding Mg Rep fv compile compile_prefix kill

variable {n : ℕ} {ι : Type} (s : ι → Fin n → Bool)

/-- Wire semantics on an arbitrary indexed family of assignments. -/
def sig (C : Circuit) (w : ℕ) : ι → Bool := fun r => wval C (s r) w

def Fresh (C : Circuit) (j : ℕ) : Prop :=
  j < C.gates.length ∧ (∀ w < n+j, sig s C (n+j) ≠ sig s C w) ∧ sig s C (n+j) ≠ fun _ => false

theorem kill (C : Circuit) (hC : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) (w : ℕ)
    (hc : w ∈ C.gates[j].inputs) (zero : sig s C w = fun _ => false) : ¬ Fresh s C j := by
  rintro ⟨_,diff,nz⟩
  obtain ⟨a,b,hab,ha,hb,op⟩ := two n C hC j hj
  have hit : w=a ∨ w=b := by simpa [hab] using hc
  rcases op with h|h
  · apply nz
    funext r
    unfold sig
    rw [wval_and C (s r) j a b hj hab ha hb h]
    have z := congrFun zero r
    change wval C (s r) w = false at z
    rcases hit with rfl|rfl <;> simp [z]
  · rcases hit with rfl|rfl
    · apply diff b hb
      funext r
      unfold sig
      rw [wval_or C (s r) j w b hj hab ha hb h]
      have z : wval C (s r) w = false := congrFun zero r
      simp [z]
    · apply diff a ha
      funext r
      unfold sig
      rw [wval_or C (s r) j a w hj hab ha hb h]
      have z : wval C (s r) w = false := congrFun zero r
      simp [z]

def Rep (gs : List Gate) (f : ι → Bool) : Prop :=
  f = (fun _ => false) ∨ ∃ w < n + gs.length, f = sig s ⟨gs,0⟩ w

private theorem old_val (gs : List Gate) (g : Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : w < n + gs.length) :
    wval (⟨gs ++ [g],0⟩ : Circuit) x w = wval (⟨gs,0⟩ : Circuit) x w := by
  change ((gs ++ [g]).foldl (fun R h => R ++ [sB R h]) (List.ofFn x)).getD w false = _
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  apply List.getD_append
  change w < (run sB (List.ofFn x) gs).length
  simpa [run_length] using hw

private theorem Rep.snoc {gs : List Gate} {f : ι → Bool} (r : Rep s gs f) (g : Gate) :
    Rep s (gs ++ [g]) f := by
  rcases r with r | ⟨w,hw,r⟩
  · exact Or.inl r
  · exact Or.inr ⟨w,by simp; omega, r.trans (funext fun x => (old_val gs g (s x) w hw).symm)⟩

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
theorem compile_prefix (C : Circuit) (hC : IsAO2 n C) (k : ℕ)
    (hk : k ≤ C.size) :
    ∃ gs : List Gate, IsAO2 n ⟨gs,0⟩ ∧ gs.length ≤ ((Finset.range k).filter (Fresh s C)).card ∧
      ∀ w < n+k, Rep s gs (sig s C w) := by
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
    exact Or.inr ⟨w,by simp; omega, funext fun r =>
      (wval_in C (s r) i).trans (wval_in (⟨[],0⟩ : Circuit) (s r) i).symm⟩
  | succ k ih =>
    obtain ⟨gs,hgs,hs,rep⟩ := ih (by omega)
    have hk' : k < C.gates.length := by exact Nat.lt_of_succ_le hk
    by_cases hm : Fresh s C k
    · obtain ⟨a,b,hab,ha,hb,ho⟩ := two n C hC k hk'
      have dep (w : ℕ) (hit : w ∈ C.gates[k].inputs) : sig s C w ≠ fun _ => false :=
        fun e => (kill s C hC k hk' w hit e) hm
      obtain ⟨u,hu,eu⟩ := (rep a ha).resolve_left (dep a (by simp [hab]))
      obtain ⟨v,hv,ev⟩ := (rep b hb).resolve_left (dep b (by simp [hab]))
      let g : Gate := ⟨C.gates[k].op,[u,v]⟩
      refine ⟨gs ++ [g],appendAO hgs u v hu hv _ ho,?_,?_⟩
      · simpa [Finset.range_add_one, Finset.filter_insert, hm] using hs
      · intro w hw
        by_cases e : w < n+k
        · exact (rep w e).snoc s g
        · have we : w = n+k := by omega
          subst w
          refine Or.inr ⟨n+gs.length,by simp,funext fun x => ?_⟩
          change wval C (s x) (n+k) = wval (⟨gs++[g],0⟩ : Circuit) (s x) (n+gs.length)
          rw [wval_gate C (s x) k a b hk' hab ha hb]
          have newGate := wval_gate (n := n) (⟨gs++[g],0⟩ : Circuit) (s x) gs.length u v
            (by simp) (by simp [g]) hu hv
          rw [newGate]
          simp only [List.getElem_append_right (by omega : gs.length ≤ gs.length), Nat.sub_self,
            List.getElem_cons_zero]
          change C.gates[k].op.eval [sig s C a x,sig s C b x] = C.gates[k].op.eval [_,_]
          rw [eu,ev]
          simp only [sig,old_val gs g (s x) u hu,old_val gs g (s x) v hv]
    · refine ⟨gs,hgs,?_,?_⟩
      · simpa [Finset.range_add_one,Finset.filter_insert,hm] using hs
      · intro w hw
        by_cases e : w < n+k
        · exact rep w e
        · have we : w = n+k := by omega
          subst w
          by_cases z : sig s C (n+k) = fun _ => false
          · exact Or.inl z
          · have dup : ∃ a < n+k, sig s C (n+k) = sig s C a := by
              by_contra! bad
              exact hm ⟨hk',bad,z⟩
            obtain ⟨a,ha,ea⟩ := dup
            rw [ea]
            exact rep _ ha

open Classical in
theorem compile (C : Circuit) (hC : IsAO2 n C) :
    ∃ D : Circuit, IsAO2 n D ∧ (∀ r, circuitFun n D (s r) = circuitFun n C (s r)) ∧
      D.size ≤ ((Finset.range C.size).filter (Fresh s C)).card := by
  classical
  obtain ⟨gs,hg,hlen,r⟩ := compile_prefix s C hC C.size le_rfl
  have rep : Rep s gs (sig s C C.output) := by
    by_cases e : C.output < n+C.size
    · exact r _ e
    · exact Or.inl (funext fun r => wval_past C (s r) _ (Nat.le_of_not_gt e))
  rcases rep with z | ⟨w,hw,ew⟩
  · refine ⟨⟨gs,n+gs.length⟩,hg,?_,hlen⟩
    intro r
    exact (wval_past (⟨gs,n+gs.length⟩ : Circuit) (s r) _ (le_refl _)).trans (congrFun z r).symm
  · exact ⟨⟨gs,w⟩,hg,(fun r => (congrFun ew r).symm),hlen⟩

/-- A zero intermediate result and a reader of its wire can both be removed,
even if the intermediate has other readers. The result agrees on every designated row. -/
theorem erase_zero_and_reader (C : Circuit) (ao : IsAO2 n C) {j k : ℕ}
    (hj : j < C.gates.length) (hk : k < C.gates.length) (ne : j ≠ k)
    (zero : ∀ r, wval C (s r) (n+j) = false) (reads : n+j ∈ C.gates[k].inputs) :
    ∃ D : Circuit, IsAO2 n D ∧ (∀ r, circuitFun n D (s r) = circuitFun n C (s r)) ∧
      D.size + 2 ≤ C.size := by
  classical
  have ez : sig s C (n+j) = fun _ => false := funext zero
  have jn : ¬ Fresh s C j := fun h => h.2.2 ez
  have kn := kill s C ao k hk _ reads ez
  obtain ⟨D,dao,same,sz⟩ := compile s C ao
  refine ⟨D,dao,same,?_⟩
  let R := Finset.range C.size
  have inc : ({j,k} : Finset ℕ) ⊆ R.filter (fun w => ¬Fresh s C w) := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | h
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,jn⟩
    · obtain rfl := Finset.mem_singleton.mp h
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,kn⟩
  have two := Finset.card_le_card inc
  simp [ne] at two
  have part := Finset.card_filter_add_card_filter_not (s := R) (p := Fresh s C)
  simp only [R,Finset.card_range] at part two
  omega

#print axioms erase_zero_and_reader
end VertexPeel.RowFold
