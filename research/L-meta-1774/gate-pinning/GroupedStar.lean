import CriticalPairOr

namespace PEqualNP.Research.GatePinning

open CircuitLowerBounds EdgeOwnership MetaComplexity MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_5465 (val val_gate val_input val_ofFn opMono_eq opMono_imp)

private theorem old_path_before {n : Nat} {C : Circuit} {k : Nat} {g : Gate}
    {i j : Nat} (early : j < k) (path : InCone n (replace C k g) i j) :
    InCone n C i j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    have boundD := Outside.L_meta_4846.cone_lt n (replace C k g).gates i j path
    have bound : j < C.gates.length := replace_length C k g ▸ boundD
    obtain ⟨w,read,gate,before,h⟩ := (cone_step boundD).1 path
    rw [replace_elsewhere early.ne] at read
    exact (cone_step bound).2 ⟨w,read,gate,before,h.imp id (fun t => ih (w-n) (by omega) (by omega) t)⟩

/-- Reuse a previously computed OR-only wire whose support, restricted by the
centre, activates the old gate and covers its critical edges. The wire can be outside
the old fan-in cone. The old gate need not own any of its critical edges. -/
theorem repair_of_grouped_star {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hC : Eligible G C) {k r : Nat} (inside : k < C.size)
    (oldAnd : (gateAt C k).op = .and) (early : r < k) (z : Fin n)
    (groupOp : (gateAt C r).op = .or)
    (pure : ∀ i, InCone n C i r → (gateAt C i).op ≠ .and)
    (safe : ∀ x : Fin n → Bool, x z = true → gateVal n C r x = true → gateVal n C k x = true)
    (cover : ∀ a b, needed G C k a b →
      (a=z ∨ b=z) ∧ gateVal n C r (pairInput a b) = true) : RepairsAt G C k := by
  let D := pinSide C k z (n+r)
  have size : D.size = C.size := replace_length ..
  have boundD : k < D.gates.length := by simpa [D,pinSide,Circuit.size] using inside
  have legal : Monotone2 D := replace_mono hC.1.1 (by simp) (by simp)
  have site : gateAt D k = ⟨.and,[z.val,n+r]⟩ := replace_at inside
  have gr : gateAt D r = gateAt C r := replace_elsewhere early.ne
  have eval (x : Fin n → Bool) : gateVal n D k x = (x z && gateVal n C r x) := by
    have pr : val D (List.ofFn x) (n+r) = gateVal n C r x := val_before hC.1.1 early x
    change val D (List.ofFn x) (n+k) = _
    rw [val_gate (n := n) (by simp) boundD,site]
    simp [GateOp.eval,val_ofFn,show z.val<n+k by omega,show n+r<n+k by omega,pr]
  have clear (i : Nat) (path : InCone n D i k) (andOp : (gateAt D i).op = .and) : False := by
    obtain ⟨w,read,gate,_,h⟩ := (cone_step boundD).1 path
    simp only [site,List.mem_cons,List.not_mem_nil,or_false] at read
    rcases read with e|e
    · have := z.isLt; omega
    subst w
    rw [Nat.add_sub_cancel_left] at h
    rcases h with e|h
    · subst i; rw [gr,groupOp] at andOp; cases andOp
    · have oldPath : InCone n C i r := old_path_before early h
      have ik : i < k := (Outside.L_meta_4846.cone_idx n C.gates r i oldPath).trans early
      have old : gateAt D i = gateAt C i := replace_elsewhere ik.ne
      exact pure i oldPath ((congrArg Gate.op old).symm.trans andOp)
  have below (x : Fin n → Bool) : gateVal n D k x = true → gateVal n C k x = true := by
    rw [eval,Bool.and_eq_true]
    exact fun h => safe x h.1 h.2
  have keep (a b : Fin n) (need : needed G C k a b) : gateVal n D k (pairInput a b) = true := by
    obtain ⟨hz,hit⟩ := cover a b need
    rw [eval,Bool.and_eq_true]
    exact ⟨by rcases hz with rfl | rfl <;> simp [pairInput],hit⟩
  obtain ⟨a,b,neededEdge⟩ := critical_exists G hC.1 hC.2.1 inside
  have eq : circuitFun n D = graphFun G ∅ :=
    subgate_correct G inside hC.1.1 hC.2.1 _ legal below keep
  have minimal : IsMinimalMonoCircuit n D :=
    ⟨legal,fun E m f => size ▸ hC.1.2 E m (f.trans (eq.trans hC.2.1.symm))⟩
  have useful : Productive G D := by
    intro i bound op
    by_cases same : i=k
    · subst i
      exact ⟨a,b,neededEdge.1,boundD,by rw [site],keep a b neededEdge,fun j _ path hop => (clear j path hop).elim⟩
    · have op0 : (gateAt C i).op = .and := (congrArg Gate.op
          (show gateAt D i = gateAt C i from replace_elsewhere same)).symm.trans op
      obtain ⟨a,b,e,own⟩ := hC.2.2 i (size ▸ bound) op0
      exact ⟨a,b,e,masked_owners_survive hC.1.1 oldAnd
        (fun _ _ j path op _ => (clear j path op).elim) below same own⟩
  refine ⟨D,⟨minimal,eq,useful⟩,size,?_,?_⟩
  · rintro j hj ⟨a,b,c,d,ab,cd,i,j,more⟩
    exact ⟨a,b,c,d,ab,cd,before_new_to_old hC.1.1 hj i,before_new_to_old hC.1.1 hj j,more⟩
  · have centered {a b : Fin n} (h : Owns n D k a b) : z=a ∨ z=b := by
      have yes := h.2.2.1
      rw [eval,Bool.and_eq_true] at yes
      simpa [pairInput] using yes.1
    rintro ⟨a,b,c,d,_,_,h,j,ac,ad,bc,bd⟩
    rcases centered h with ha|hb <;> rcases centered j with hc|hd <;> grind

/-- A location before the bad gate already computes the disjunction of the two leaves.
It may sit outside the original fan-in cone, and neither spoke need be owned by that gate. -/
theorem repair_of_precomputed_spokes {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hC : Eligible G C) {k r : Nat} (inside : k < C.size)
    (oldAnd : (gateAt C k).op = .and) (early : r < k) (z u v : Fin n)
    (group : gateAt C r = ⟨.or,[u.val,v.val]⟩)
    (needU : needed G C k z u) (needV : needed G C k z v)
    (cover : ∀ a b, needed G C k a b → (a=z ∨ b=z) ∧ (a=u ∨ b=u ∨ a=v ∨ b=v)) :
    RepairsAt G C k := by
  have groupEval (x : Fin n → Bool) : gateVal n C r x = (x u || x v) := by
    change val C (List.ofFn x) (n+r) = _
    rw [val_gate (n:=n) (by simp) (early.trans inside),group]
    simp [GateOp.eval,val_ofFn,show u.val < n+r by omega,show v.val < n+r by omega]
  have leaf (q : Fin n) (need : needed G C k z q) (x : Fin n → Bool) (hz : x z = true)
      (hq : x q = true) : gateVal n C k x = true := by
    apply Outside.L_meta_2573.wires_mono C (Outside.L_meta_2573.mono2_ops C hC.1.1) (pairInput z q) x _
      (n+k) (needed_turns_on G hC.1.1 inside hC.2.1 need)
    intro a h
    simp only [pairInput,decide_eq_true_eq] at h
    rcases h with rfl|rfl
    · exact hz
    · exact hq
  apply repair_of_grouped_star G hC inside oldAnd early z (by simp [group])
  · intro i path _
    obtain ⟨w,read,gate,_,_⟩ := (cone_step (early.trans inside)).1 path
    simp only [group,List.mem_cons,List.not_mem_nil,or_false] at read
    have hu := u.isLt; have hv := v.isLt
    rcases read with e|e <;> omega
  · intro x hz on
    rw [groupEval,Bool.or_eq_true] at on
    exact on.elim (leaf u needU x hz) (leaf v needV x hz)
  · intro a b need
    obtain ⟨hz,spokes⟩ := cover a b need
    refine ⟨hz,?_⟩
    rw [groupEval,Bool.or_eq_true]
    rcases spokes with rfl | rfl | rfl | rfl <;> simp [pairInput]

end PEqualNP.Research.GatePinning
