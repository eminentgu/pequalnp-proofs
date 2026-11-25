import CriticalOr

namespace PEqualNP.Research.GatePinning

open CircuitLowerBounds EdgeOwnership MetaComplexity MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_5465 (val val_gate val_ofFn opMono_eq opMono_imp)

private theorem path_origin {n : Nat} {C : Circuit} {k : Nat} {g : Gate}
    {i j : Nat} (path : InCone n (replace C k g) i j) :
    InCone n C i j ∨ (InCone n (replace C k g) i k ∧ (j=k ∨ InCone n C k j)) := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    by_cases target : j=k
    · subst j; exact Or.inr ⟨path,Or.inl rfl⟩
    have boundD := Outside.L_meta_4846.cone_lt n (replace C k g).gates i j path
    have bound : j < C.gates.length := replace_length C k g ▸ boundD
    obtain ⟨w,read,ge,lt,h⟩ := (cone_step boundD).1 path
    rw [replace_elsewhere target] at read
    rcases h with direct|deep
    · exact Or.inl ((cone_step bound).2 ⟨w,read,ge,lt,Or.inl direct⟩)
    rcases ih (w-n) (by omega) deep with old|⟨path,reach⟩
    · exact Or.inl ((cone_step bound).2 ⟨w,read,ge,lt,Or.inr old⟩)
    · exact Or.inr ⟨path,Or.inr ((cone_step bound).2 ⟨w,read,ge,lt,reach.imp Eq.symm id⟩)⟩

/-- New AND ancestors may be introduced when they only activate on rows on which
the replaced AND already activated. A later gate cannot previously own such a row
if its cone contains the replaced AND. -/
theorem masked_owners_survive {n} {C : Circuit} {k : Nat} {g : Gate}
    (legal : Monotone2 C) (oldAnd : (gateAt C k).op = .and)
    (shadow : ∀ a b : Fin n, ∀ j, InCone n (replace C k g) j k →
      (gateAt (replace C k g) j).op = .and →
      gateVal n (replace C k g) j (pairInput a b) = true → gateVal n C k (pairInput a b) = true)
    (narrow : ∀ x : Fin n → Bool, gateVal n (replace C k g) k x = true → gateVal n C k x = true)
    {i u v} (ne : i ≠ k) (own : Owns n C i u v) : Owns n (replace C k g) i u v := by
  let D := replace C k g
  let x := pairInput u v
  have len : D.gates.length = C.gates.length := replace_length ..
  have same (j) (jk : j ≠ k) : gateAt D j = gateAt C j := replace_elsewhere jk
  have less (t) : gateVal n D t x = true → gateVal n C t x = true :=
    propagate k x (fun a b => a = true → b = true) (fun _ => id) opMono_imp legal len same (n+t)
      (fun _ => narrow x)
  have offK (path : InCone n C k i) : gateVal n C k x = false :=
    own.2.2.2 k (Outside.L_meta_4846.cone_idx n C.gates i k path) path oldAnd
  refine ⟨len ▸ own.1,(congrArg Gate.op (same i ne)).trans own.2.1,?_,?_⟩
  · have eq : gateVal n D i x = gateVal n C i x := by
      apply propagate k x Eq (fun _ => rfl) opMono_eq legal len same (n+i)
      rintro ⟨_,h | path⟩
      · exact False.elim (ne (by omega))
      · rw [Nat.add_sub_cancel_left] at path
        cases h : gateVal n D k x with
        | false => exact (offK path).symm
        | true => exact False.elim (Bool.noConfusion ((less k h).symm.trans (offK path)))
    exact eq.trans own.2.2.1
  · intro j ji path hand
    cases h : gateVal n D j x with
    | false => rfl
    | true =>
      rcases path_origin path with oldPath|⟨newPath,origin⟩
      · have oldOp : (gateAt C j).op = .and := by
          by_cases jk : j = k
          · simpa [jk] using oldAnd
          · rw [replace_elsewhere jk] at hand
            exact hand
        exact False.elim (Bool.noConfusion ((less j h).symm.trans (own.2.2.2 j ji oldPath oldOp)))
      · exact False.elim (Bool.noConfusion ((shadow u v j newPath hand h).symm.trans (offK (origin.resolve_left ne))))

/-- Replace any bad AND by an OR of two earlier wires subject to row conditions. -/
theorem repair_of_masked_or {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hC : Eligible G C) {k s t : Nat} (inside : k < C.size)
    (hand : (gateAt C k).op = .and)
    (shadow : ∀ a b : Fin n, ∀ j, InCone n (replace C k ⟨.or,[s,t]⟩) j k →
      (gateAt (replace C k ⟨.or,[s,t]⟩) j).op = .and →
      gateVal n (replace C k ⟨.or,[s,t]⟩) j (pairInput a b) = true → gateVal n C k (pairInput a b) = true)
    (below : ∀ x : Fin n → Bool, gateVal n (replace C k ⟨.or,[s,t]⟩) k x = true → gateVal n C k x = true)
    (keep : ∀ a b, needed G C k a b → gateVal n (replace C k ⟨.or,[s,t]⟩) k (pairInput a b) = true) :
    RepairsAt G C k := by
  let D := replace C k ⟨.or,[s,t]⟩
  have legal : Monotone2 D := replace_mono hC.1.1 (by simp) (by simp)
  have size : D.size = C.size := replace_length ..
  have site : gateAt D k = ⟨.or,[s,t]⟩ := replace_at inside
  have eq := subgate_correct G inside hC.1.1 hC.2.1 _ legal below keep
  have minimal : IsMinimalMonoCircuit n D :=
    ⟨legal,fun E m f => size ▸ hC.1.2 E m (f.trans (eq.trans hC.2.1.symm))⟩
  have useful : Productive G D := by
    intro j hj op
    by_cases atK : j=k
    · subst j; rw [site] at op; cases op
    · have op0 := (congrArg Gate.op (show gateAt D j = gateAt C j from replace_elsewhere atK)).symm.trans op
      obtain ⟨a,b,e,own⟩ := hC.2.2 j (size ▸ hj) op0
      exact ⟨a,b,e,masked_owners_survive hC.1.1 hand shadow below atK own⟩
  refine ⟨D,⟨minimal,eq,useful⟩,size,?_,?_⟩
  · rintro j hj ⟨a,b,c,d,ab,cd,i,j,more⟩
    exact ⟨a,b,c,d,ab,cd,before_new_to_old hC.1.1 hj i,before_new_to_old hC.1.1 hj j,more⟩
  · rintro ⟨a,b,c,d,_,_,owned,_⟩
    have op := owned.2.1
    rw [site] at op
    cases op

/-- If the two critical edges have already been computed as primary ANDs,
their disjunction repairs the gate. The edges can be disjoint and both wires can
be outside the old gate's fan-in cone. -/
theorem repair_of_precomputed_pairs {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hC : Eligible G C) {k p q : Nat} (inside : k < C.size)
    (hand : (gateAt C k).op = .and) (hp : p<k) (hq : q<k) (a b c d : Fin n)
    (pg : gateAt C p = ⟨.and,[a.val,b.val]⟩) (qg : gateAt C q = ⟨.and,[c.val,d.val]⟩)
    (first : needed G C k a b) (second : needed G C k c d)
    (covers : ∀ u v, needed G C k u v →
      (u=a ∧ v=b) ∨ (u=b ∧ v=a) ∨ (u=c ∧ v=d) ∨ (u=d ∧ v=c)) : RepairsAt G C k := by
  let D := replace C k ⟨.or,[n+p,n+q]⟩
  have boundD : k < D.gates.length := by simpa [D,Circuit.size] using inside
  have site : gateAt D k = ⟨.or,[n+p,n+q]⟩ := replace_at inside
  have left : gateAt D p = ⟨.and,[a.val,b.val]⟩ := (replace_elsewhere hp.ne).trans pg
  have right : gateAt D q = ⟨.and,[c.val,d.val]⟩ := (replace_elsewhere hq.ne).trans qg
  have value (r : Nat) (u v : Fin n) (hr : r<k) (g : gateAt D r = ⟨.and,[u.val,v.val]⟩)
      (x : Fin n → Bool) : gateVal n D r x = (x u && x v) := by
    change val D (List.ofFn x) (n+r) = _
    rw [val_gate (n:=n) (by simp) (hr.trans boundD),g]
    simp [GateOp.eval,val_ofFn,show u.val < n+r by omega,show v.val < n+r by omega]
  have eval (x : Fin n → Bool) : gateVal n D k x = (gateVal n D p x || gateVal n D q x) := by
    change val D (List.ofFn x) (n+k) = (val D _ (n+p) || val D _ (n+q))
    rw [val_gate (n:=n) (by simp) boundD,site]
    simp [GateOp.eval,show n+p<n+k by omega,show n+q<n+k by omega]
  have force (u v : Fin n) (need : needed G C k u v) (x : Fin n → Bool)
      (both : (x u && x v) = true) : gateVal n C k x = true := by
    obtain ⟨onU,onV⟩ := Bool.and_eq_true_iff.mp both
    apply Outside.L_meta_2573.wires_mono C (Outside.L_meta_2573.mono2_ops C hC.1.1) (pairInput u v) x _
      (n+k) (needed_turns_on G hC.1.1 inside hC.2.1 need)
    intro i hi
    simp only [pairInput,decide_eq_true_eq] at hi
    rcases hi with rfl|rfl
    · exact onU
    · exact onV
  have below (x : Fin n → Bool) (on : gateVal n D k x = true) : gateVal n C k x = true := by
    rw [eval,Bool.or_eq_true,value p a b hp left,value q c d hq right] at on
    exact on.elim (force a b first x) (force c d second x)
  have pure (r : Nat) (u v : Fin n) (hr : r<k) (g : gateAt D r = ⟨.and,[u.val,v.val]⟩)
      (i : Nat) (path : InCone n D i r) : False := by
    obtain ⟨w,read,gate,_,_⟩ := (cone_step (hr.trans boundD)).1 path
    simp only [g,List.mem_cons,List.not_mem_nil,or_false] at read
    have hu := u.isLt; have hv := v.isLt
    rcases read with e|e <;> omega
  apply repair_of_masked_or G hC inside (s:=n+p) (t:=n+q) hand _ below
  · intro u v need
    rw [eval,Bool.or_eq_true,value p a b hp left,value q c d hq right]
    rcases covers u v need with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [pairInput]
  · intro u v i path _ on
    obtain ⟨w,read,gate,_,h⟩ := (cone_step boundD).1 path
    simp only [site,List.mem_cons,List.not_mem_nil,or_false] at read
    apply below (pairInput u v)
    rw [eval,Bool.or_eq_true]
    rcases read with eq|eq <;> subst w <;> rw [Nat.add_sub_cancel_left] at h
    · rcases h with same|ancestor
      · exact Or.inl (same ▸ on)
      · exact (pure p a b hp left i ancestor).elim
    · rcases h with same|ancestor
      · exact Or.inr (same ▸ on)
      · exact (pure q c d hq right i ancestor).elim

end PEqualNP.Research.GatePinning
