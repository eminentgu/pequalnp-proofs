import GroupedStar

namespace PEqualNP.Research.GatePinning

open CircuitLowerBounds EdgeOwnership MetaComplexity MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_5465 (val val_gate val_input val_ge val_ofFn opMono_eq opMono_imp gateAt_mem)

def PrivateInputs {n : Nat} (C : Circuit) (p q k : Nat) : Prop :=
  C.output ≠ n+p ∧ C.output ≠ n+q ∧
  ∀ j < C.size, j ≠ k → ∀ w ∈ (gateAt C j).inputs, w ≠ n+p ∧ w ≠ n+q

/-- Propagation through a circuit that changes an output gate and its two private
parents. Earlier parent values can differ. All external reads bypass the two parents. -/
private theorem outer_propagate {n} {C D : Circuit} {p q k} (x : Fin n → Bool)
    (R : Bool → Bool → Prop) (reflR : ∀ b, R b b) (lift : Outside.L_meta_5465.OpMono R)
    (legal : Monotone2 C) (len : D.gates.length = C.gates.length)
    (privateIn : PrivateInputs (n:=n) C p q k)
    (same : ∀ j, j≠p → j≠q → j≠k → gateAt D j = gateAt C j)
    (w : Nat) (wp : w≠n+p) (wq : w≠n+q)
    (localR : feeds (n:=n) C k w → R (gateVal n D k x) (gateVal n C k x)) :
    R (val D (List.ofFn x) w) (val C (List.ofFn x) w) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w<n
    · rw [val_input (n:=n) (by simp) raw,val_input (n:=n) (by simp) raw]; exact reflR _
    by_cases out : n+C.gates.length ≤ w
    · rw [val_ge (n:=n) (by simp) (by omega : n+D.gates.length≤w),val_ge (n:=n) (by simp) out]
      exact reflR _
    obtain ⟨j,rfl⟩ : ∃ j, w=n+j := ⟨w-n,by omega⟩
    by_cases target : j=k
    · subst j; exact localR ⟨by omega,Or.inl rfl⟩
    have inside : j<C.gates.length := by omega
    rw [val_gate (n:=n) (by simp) (by omega : j<D.gates.length),val_gate (n:=n) (by simp) inside,
      same j (by omega) (by omega) target]
    apply lift _ (legal _ (gateAt_mem inside)).1
    intro u read
    by_cases earlier : u<n+j
    · have priv := privateIn.2.2 j inside target u read
      simp only [earlier,ite_true]
      apply ih u earlier priv.1 priv.2
      intro feed
      apply localR
      refine ⟨by omega,Or.inr ?_⟩
      rw [Nat.add_sub_cancel_left]
      exact (cone_step inside).2 ⟨u,read,feed.1,earlier,feed.2.imp (fun e => by omega) id⟩
    · simp [earlier,reflR]

private theorem private_path {n} {C : Circuit} {k p q i j : Nat}
    (priv : PrivateInputs (n:=n) C p q k) (source : i=p ∨ i=q) (path : InCone n C i j) :
    j=k ∨ InCone n C k j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    by_cases eq : j=k
    · exact Or.inl eq
    have bound := Outside.L_meta_4846.cone_lt n C.gates i j path
    obtain ⟨w,read,ge,lt,h⟩ := (cone_step bound).1 path
    have blocked := priv.2.2 j bound eq w read
    rcases h with edge|deep
    · exact False.elim (by rcases source with a|a <;> omega)
    exact Or.inr ((cone_step bound).2 ⟨w,read,ge,lt,(ih (w-n) (by omega) deep).imp Eq.symm id⟩)

private theorem prefix_path {n} {C D : Circuit} {k p q : Nat}
    (priv : PrivateInputs (n:=n) C p q k) (len : D.gates.length=C.gates.length)
    (same : ∀ j, j≠p → j≠q → j≠k → gateAt D j = gateAt C j)
    {i j} (early : j<k) (jp : j≠p) (jq : j≠q) (path : InCone n C i j) : InCone n D i j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    have bound := Outside.L_meta_4846.cone_lt n C.gates i j path
    obtain ⟨w,h,ge,lt,reach⟩ := (cone_step bound).1 path
    have pr := priv.2.2 j bound early.ne w h
    apply (cone_step (len ▸ bound)).2
    rw [same j jp jq early.ne]
    exact ⟨w,h,ge,lt,reach.imp id (fun path => ih (w-n) (by omega) (by omega) (by omega) (by omega) path)⟩

/-- Two private gate positions before the defective AND suffice to rebuild any two
critical edges. Neither old operand needs to compute the corresponding pair. -/
theorem repair_of_private_parents {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hC : Eligible G C) {k p q : Nat} (inside : k < C.size)
    (hp : p<k) (hq : q<k) (distinct : p≠q) (site : gateAt C k = ⟨.and,[n+p,n+q]⟩)
    (priv : PrivateInputs (n:=n) C p q k) (a b c d : Fin n)
    (first : needed G C k a b) (second : needed G C k c d)
    (cover : ∀ u v, needed G C k u v →
      (u=a ∧ v=b) ∨ (u=b ∧ v=a) ∨ (u=c ∧ v=d) ∨ (u=d ∧ v=c)) : RepairsAt G C k := by
  let A := replace C p ⟨.and,[a.val,b.val]⟩
  let B := replace A q ⟨.and,[c.val,d.val]⟩
  let D := replace B k ⟨.or,[n+p,n+q]⟩
  have len : D.gates.length = C.gates.length := by simp [D,B,A]
  have size : D.size = C.size := len
  have inB : k < B.gates.length := by simpa [B,A,Circuit.size] using inside
  have inD : k < D.gates.length := len ▸ inside
  have inA : q < A.gates.length := by simpa [A,Circuit.size] using hq.trans inside
  have dm : Monotone2 D := replace_mono (replace_mono (replace_mono hC.1.1 (by simp) (by simp))
    (by simp) (by simp)) (by simp) (by simp)
  have dk : gateAt D k = ⟨.or,[n+p,n+q]⟩ := replace_at inB
  have dp : gateAt D p = ⟨.and,[a.val,b.val]⟩ :=
    (replace_elsewhere hp.ne).trans ((replace_elsewhere distinct).trans (replace_at (hp.trans inside)))
  have dq : gateAt D q = ⟨.and,[c.val,d.val]⟩ :=
    (replace_elsewhere hq.ne).trans (replace_at inA)
  have same (j) (jp : j≠p) (jq : j≠q) (jk : j≠k) : gateAt D j = gateAt C j :=
    (replace_elsewhere jk).trans ((replace_elsewhere jq).trans (replace_elsewhere jp))
  have coneOld {i j} (h : InCone n D i j) : InCone n C i j := by
    have bSite : gateAt B k = ⟨.and,[n+p,n+q]⟩ :=
      (replace_elsewhere hq.ne').trans ((replace_elsewhere hp.ne').trans site)
    have bPath : InCone n B i j := cone_subread B k _ (by intro w hw; exact Or.inr (by simpa [bSite] using hw)) h
    have aPath : InCone n A i j := cone_subread A q _ (by
      intro w hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl
      · exact Or.inl c.isLt
      · exact Or.inl d.isLt) bPath
    apply cone_subread C p _ _ aPath
    intro w hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl
    · exact Or.inl a.isLt
    · exact Or.inl b.isLt
  have row (r : Nat) (u v : Fin n) (bound : r < D.gates.length)
      (g : gateAt D r = ⟨.and,[u.val,v.val]⟩) (x : Fin n → Bool) :
      gateVal n D r x = (x u && x v) := by
    change val D (List.ofFn x) (n+r) = _
    rw [val_gate (n:=n) (by simp) bound,g]
    simp [GateOp.eval,val_ofFn,show u.val<n+r by omega,show v.val<n+r by omega]
  have eval (x : Fin n → Bool) : gateVal n D k x = (gateVal n D p x || gateVal n D q x) := by
    change val D (List.ofFn x) (n+k) = (val D _ (n+p) || val D _ (n+q))
    rw [val_gate (n:=n) (by simp) inD,dk]
    simp [GateOp.eval,show n+p<n+k by omega,show n+q<n+k by omega]
  have firstRow := row p a b (hp.trans inD) dp
  have secondRow := row q c d (hq.trans inD) dq
  have force (u v : Fin n) (need : needed G C k u v) (x : Fin n → Bool)
      (both : (x u && x v) = true) : gateVal n C k x = true := by
    obtain ⟨hu,hv⟩ := Bool.and_eq_true_iff.mp both
    apply Outside.L_meta_2573.wires_mono C (Outside.L_meta_2573.mono2_ops C hC.1.1) (pairInput u v) x _
      (n+k) (needed_turns_on G hC.1.1 inside hC.2.1 need)
    intro i hi
    simp only [pairInput,decide_eq_true_eq] at hi
    rcases hi with rfl|rfl
    · exact hu
    · exact hv
  have narrow (x : Fin n → Bool) : gateVal n D k x = true → gateVal n C k x = true := by
    rw [eval,Bool.or_eq_true,firstRow,secondRow]
    exact fun h => h.elim (force a b first x) (force c d second x)
  have keep (u v : Fin n) (need : needed G C k u v) : gateVal n D k (pairInput u v) = true := by
    rw [eval,Bool.or_eq_true,firstRow,secondRow]
    rcases cover u v need with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [pairInput]
  have correct : circuitFun n D = graphFun G ∅ := by
    apply (GuardedReaders.graph_rows_iff G D dm).2
    constructor
    · intro u v edge
      let x := pairInput u v
      by_cases on : gateVal n D k x = true
      · have eq : circuitFun n D x = circuitFun n C x :=
          outer_propagate x Eq (fun _ => rfl) opMono_eq hC.1.1 len priv same C.output
            priv.1 priv.2.1 (fun _ => on.trans (narrow x on).symm)
        exact eq.trans (((GuardedReaders.graph_rows_iff G C hC.1.1).1 hC.2.1).1 u v edge)
      · let Z := zero C k
        have zm : Monotone2 Z := replace_mono hC.1.1 (by simp) (by simp)
        have length : Z.gates.length=C.gates.length := replace_length ..
        have zpr : PrivateInputs (n:=n) Z p q k := by
          refine ⟨priv.1,priv.2.1,?_⟩
          intro j bound jk w h
          rw [show gateAt Z j = gateAt C j from replace_elsewhere jk] at h
          exact priv.2.2 j (show j<C.gates.length from length ▸ (show j<Z.gates.length from bound)) jk w h
        have eq : circuitFun n D x = circuitFun n Z x :=
          outer_propagate x Eq (fun _ => rfl) opMono_eq zm (len.trans length.symm) zpr
            (fun j jp jq jk => (same j jp jq jk).trans (replace_elsewhere jk).symm)
            C.output priv.1 priv.2.1 (fun _ => (Bool.eq_false_iff.mpr on).trans (zero_value inside x).symm)
        rw [eq]
        cases hz : circuitFun n Z x with
        | false => exact (on (keep u v ⟨edge,hz⟩)).elim
        | true => rfl
    · intro x off
      have cmp := outer_propagate x (fun a b => a=true → b=true) (fun _ => id) opMono_imp
        hC.1.1 len priv same C.output priv.1 priv.2.1 (fun _ => narrow x)
      cases v : circuitFun n D x with
      | false => rfl
      | true => exact False.elim (Bool.noConfusion ((cmp v).symm.trans ((congrFun hC.2.1 x).trans off)))
  have minD : IsMinimalMonoCircuit n D :=
    ⟨dm,fun E m f => size ▸ hC.1.2 E m (f.trans (correct.trans hC.2.1.symm))⟩
  have lesser (i : Nat) (ip : i≠p) (iq : i≠q) (x : Fin n → Bool) :
      gateVal n D i x = true → gateVal n C i x = true :=
    outer_propagate x (fun a b => a=true → b=true) (fun _ => id) opMono_imp hC.1.1 len priv same (n+i)
      (by omega) (by omega) (fun _ => narrow x)
  have shadow (j : Nat) (loc : j=p ∨ j=q) (x : Fin n → Bool) (on : gateVal n D j x = true) :
      gateVal n C k x = true := by
    apply narrow x
    rw [eval,Bool.or_eq_true]
    rcases loc with rfl|rfl
    · exact Or.inl on
    · exact Or.inr on
  have oldAnd : (gateAt C k).op = .and := congrArg Gate.op site
  have transfer {i : Nat} (ip : i≠p) (iq : i≠q) (ik : i≠k) {u v : Fin n}
      (own : Owns n C i u v) : Owns n D i u v := by
    let x := pairInput u v
    have oldOff (path : InCone n C k i) : gateVal n C k x = false :=
      own.2.2.2 k (Outside.L_meta_4846.cone_idx n C.gates i k path) path oldAnd
    refine ⟨len ▸ own.1,(congrArg Gate.op (same i ip iq ik)).trans own.2.1,?_,?_⟩
    · have eq : gateVal n D i x = gateVal n C i x := by
        apply outer_propagate x Eq (fun _ => rfl) opMono_eq hC.1.1 len priv same (n+i)
          (by omega) (by omega)
        rintro ⟨_,e|path⟩
        · exact (ik (by omega)).elim
        · rw [Nat.add_sub_cancel_left] at path
          cases h : gateVal n D k x with
          | false => exact (oldOff path).symm
          | true => exact False.elim (Bool.noConfusion ((narrow x h).symm.trans (oldOff path)))
      exact eq.trans own.2.2.1
    · intro j ji newPath newAnd
      have oldPath := coneOld newPath
      cases h : gateVal n D j x with
      | false => rfl
      | true =>
        by_cases sp : j=p ∨ j=q
        · have kPath := (private_path priv sp oldPath).resolve_left ik
          exact False.elim (Bool.noConfusion ((shadow j sp x h).symm.trans (oldOff kPath)))
        · have jp := fun e : j=p => sp (Or.inl e)
          have jq := fun e : j=q => sp (Or.inr e)
          have jk : j≠k := by rintro rfl; rw [dk] at newAnd; cases newAnd
          have oldOp := (congrArg Gate.op (same j jp jq jk)).symm.trans newAnd
          exact False.elim (Bool.noConfusion ((lesser j jp jq x h).symm.trans (own.2.2.2 j ji oldPath oldOp)))
  have noParent (r : Nat) (u v : Fin n) (rb : r<D.gates.length)
      (g : gateAt D r = ⟨.and,[u.val,v.val]⟩) (j : Nat) (path : InCone n D j r) : False := by
    obtain ⟨w,read,ge,_,_⟩ := (cone_step rb).1 path
    simp only [g,List.mem_cons,List.not_mem_nil,or_false] at read
    have hu := u.isLt; have hv := v.isLt
    rcases read with t|t <;> omega
  have ownsSelf (r : Nat) (u v : Fin n) (rb : r<D.gates.length)
      (g : gateAt D r = ⟨.and,[u.val,v.val]⟩) : Owns n D r u v := by
    refine ⟨rb,congrArg Gate.op g,?_,fun j _ path _ => (noParent r u v rb g j path).elim⟩
    rw [row r u v rb g]; simp [pairInput]
  have ready : Productive G D := by
    intro i ib op
    by_cases ip : i=p
    · subst i; exact ⟨a,b,first.1,ownsSelf p a b (hp.trans inD) dp⟩
    by_cases iq : i=q
    · subst i; exact ⟨c,d,second.1,ownsSelf q c d (hq.trans inD) dq⟩
    have ik : i≠k := by rintro rfl; rw [dk] at op; cases op
    have oldOp := (congrArg Gate.op (same i ip iq ik)).symm.trans op
    obtain ⟨u,v,e,own⟩ := hC.2.2 i (size ▸ ib) oldOp
    exact ⟨u,v,e,transfer ip iq ik own⟩
  have earlyVal (i : Nat) (e : i<k) (ip : i≠p) (iq : i≠q) (x : Fin n → Bool) :
      gateVal n D i x = gateVal n C i x := by
    apply outer_propagate x Eq (fun _ => rfl) opMono_eq hC.1.1 len priv same (n+i) (by omega) (by omega)
    rintro ⟨_,eq|h⟩
    · omega
    · rw [Nat.add_sub_cancel_left] at h
      have := Outside.L_meta_4846.cone_idx n C.gates i k h
      omega
  have earlyOwn {i : Nat} (e : i<k) (ip : i≠p) (iq : i≠q) {u v : Fin n}
      (own : Owns n D i u v) : Owns n C i u v := by
    refine ⟨len ▸ own.1,(congrArg Gate.op (same i ip iq e.ne)).symm.trans own.2.1,
      (earlyVal i e ip iq _).symm.trans own.2.2.1,?_⟩
    intro j ji oldPath oldOp
    have away : ¬(j=p ∨ j=q) := by
      intro claimed
      have h := (private_path priv claimed oldPath).resolve_left e.ne
      have := Outside.L_meta_4846.cone_idx n C.gates i k h
      omega
    have jp := fun t : j=p => away (Or.inl t)
    have jq := fun t : j=q => away (Or.inr t)
    have newPath := prefix_path priv len same e ip iq oldPath
    have newOp := (congrArg Gate.op (same j jp jq (ji.trans e).ne)).trans oldOp
    exact (earlyVal j (ji.trans e) jp jq _).symm.trans (own.2.2.2 j ji newPath newOp)
  have singleParent (r : Nat) (u v : Fin n) (rb : r<D.gates.length)
      (g : gateAt D r = ⟨.and,[u.val,v.val]⟩) : ¬BadAt G D r := by
    have center {x y : Fin n} (own : Owns n D r x y) : u=x ∨ u=y := by
      have on := own.2.2.1
      rw [row r u v rb g,Bool.and_eq_true] at on
      simpa [pairInput] using on.1
    rintro ⟨x,y,m,l,_,_,u1,u2,h1,h2,h3,h4⟩
    rcases center u1 with t|t <;> rcases center u2 with h|h <;> grind
  refine ⟨D,⟨minD,correct,ready⟩,size,?_,?_⟩
  · intro i e bad
    by_cases ip : i=p
    · subst i; exact (singleParent p a b (hp.trans inD) dp bad).elim
    by_cases iq : i=q
    · subst i; exact (singleParent q c d (hq.trans inD) dq bad).elim
    obtain ⟨u,v,x,y,m,l,own,other,dis⟩ := bad
    exact ⟨u,v,x,y,m,l,earlyOwn e ip iq own,earlyOwn e ip iq other,dis⟩
  · rintro ⟨_,_,_,_,_,_,own,_⟩
    have op := own.2.1
    rw [dk] at op; cases op

def CriticalPairSplice {n} (G : SimpleGraph (Fin n)) (C : Circuit) (k : Nat) :=
  ∃ (p q : Nat) (a b c d : Fin n), p<k ∧ q<k ∧ needed G C k a b ∧ needed G C k c d ∧
    (∀ u v, needed G C k u v →
      (u=a ∧ v=b) ∨ (u=b ∧ v=a) ∨ (u=c ∧ v=d) ∨ (u=d ∧ v=c)) ∧
    ((gateAt C p = ⟨.and,[a.val,b.val]⟩ ∧ gateAt C q = ⟨.and,[c.val,d.val]⟩) ∨
      (p≠q ∧ gateAt C k = ⟨.and,[n+p,n+q]⟩ ∧ PrivateInputs (n:=n) C p q k))

def GroupedCriticalStar {n} (G : SimpleGraph (Fin n)) (C : Circuit) (k : Nat) :=
  ∃ (r : Nat) (z : Fin n), r<k ∧ (gateAt C r).op = .or ∧
    (∀ i, InCone n C i r → (gateAt C i).op ≠ .and) ∧
    (∀ x : Fin n → Bool, x z = true → gateVal n C r x = true → gateVal n C k x = true) ∧
    ∀ a b, needed G C k a b → (a=z ∨ b=z) ∧ gateVal n C r (pairInput a b) = true

/-- The unresolved descent premise excludes vertex covers by forcing inputs, owned
two-spoke stars, reusable OR groups, precomputed pairs, and private-parent rebuilds. -/
theorem exact_of_remaining_shared_cases
    (hard : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) → TopForm.NoFourCycle G →
      ∀ C : Circuit, Eligible G C → ∀ k < C.size, (∀ j < k, ¬BadAt G C j) → BadAt G C k →
      MultipleCritical G C k → ¬AdmitsStarPin G C k →
      ¬TwoOwnedSpokes G C k → ¬TwoForcingVertices G C k → ¬CriticalPairSplice G C k →
      ¬GroupedCriticalStar G C k → RepairsAt G C k) : Exact1774 := by
  apply exact_of_remaining_beyond_two_spokes
  intro n G _ tri four C hC k inside early bad multi nstar nspokes nforcing
  have hand : (gateAt C k).op = .and := by
    obtain ⟨_,_,_,_,_,_,own,_⟩ := bad
    exact own.2.1
  by_cases pairs : CriticalPairSplice G C k
  · obtain ⟨p,q,a,b,c,d,hp,hq,first,second,cover,old|fresh⟩ := pairs
    · exact repair_of_precomputed_pairs G hC inside hand hp hq a b c d old.1 old.2 first second cover
    · exact repair_of_private_parents G hC inside hp hq fresh.1 fresh.2.1 fresh.2.2 a b c d first second cover
  by_cases grouped : GroupedCriticalStar G C k
  · obtain ⟨r,z,hr,ra,pure,safe,cover⟩ := grouped
    exact repair_of_grouped_star G hC inside hand hr z ra pure safe cover
  exact hard n G tri four C hC k inside early bad multi nstar nspokes nforcing pairs grouped

end PEqualNP.Research.GatePinning
