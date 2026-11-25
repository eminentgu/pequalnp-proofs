import CriticalCases

namespace PEqualNP.Research.GatePinning

open CircuitLowerBounds EdgeOwnership MetaComplexity MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_5465 (val val_gate opMono_eq opMono_imp)

def one (C : Circuit) (k : Nat) := replace C k ⟨.and,[]⟩

theorem one_value {n} {C : Circuit} {k : Nat} (inside : k < C.gates.length) (x : Fin n → Bool) :
    gateVal n (one C k) k x = true := by
  change val (one C k) (List.ofFn x) (n+k) = _
  rw [val_gate (n := n) (by simp) (by simpa [one] using inside),
    show gateAt (one C k) k = _ from replace_at inside]
  rfl

/-- Independent inputs which become false positives when the site is clamped high. -/
def forbidden {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : Nat)
    (x : Fin n → Bool) := graphFun G ∅ x = false ∧ circuitFun n (one C k) x = true

private theorem clamp_read {n} (C : Circuit) {k} (inside : k < C.size) (g : Gate)
    (dm : Monotone2 (replace C k g)) (x : Fin n → Bool) :
    (gateVal n (replace C k g) k x = false →
      circuitFun n (replace C k g) x = circuitFun n (zero C k) x) ∧
    (gateVal n (replace C k g) k x = true →
      circuitFun n (replace C k g) x = circuitFun n (one C k) x) := by
  constructor
  · intro off
    exact (propagate k x Eq (fun _ => rfl) opMono_eq dm
      ((replace_length ..).trans (replace_length ..).symm)
      (fun _ ne => (replace_elsewhere ne).trans (replace_elsewhere ne).symm)
      C.output (fun _ => (zero_value inside x).trans off.symm)).symm
  · intro on
    exact (propagate k x Eq (fun _ => rfl) opMono_eq dm
      ((replace_length ..).trans (replace_length ..).symm)
      (fun _ ne => (replace_elsewhere ne).trans (replace_elsewhere ne).symm)
      C.output (fun _ => (one_value inside x).trans on.symm)).symm

private theorem clamp_bounds {n} (C : Circuit) {k} (inside : k < C.size) (m : Monotone2 C)
    (x : Fin n → Bool) :
    (circuitFun n (zero C k) x = true → circuitFun n C x = true) ∧
    (circuitFun n C x = true → circuitFun n (one C k) x = true) := by
  constructor
  · exact propagate k x (fun a b => a=true → b=true) (fun _ => id) opMono_imp m
      (replace_length ..) (fun _ h => replace_elsewhere h) C.output
      (fun _ hit => False.elim (Bool.noConfusion ((zero_value inside x).symm.trans hit)))
  · have lm : Monotone2 (one C k) := replace_mono m (by simp) (by simp)
    exact propagate k x (fun a b => a=true → b=true) (fun _ => id) opMono_imp lm
      (replace_length ..).symm (fun _ h => (replace_elsewhere h).symm) C.output
      (fun _ _ => one_value inside x)

/-- Exact two-sided test for an arbitrary monotone gate substituted at one site. -/
theorem rewrite_correct_iff {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit} {k}
    (inside : k < C.size) (m : Monotone2 C) (correct : circuitFun n C = graphFun G ∅)
    (g : Gate) (dm : Monotone2 (replace C k g)) :
    circuitFun n (replace C k g) = graphFun G ∅ ↔
      (∀ a b, needed G C k a b → gateVal n (replace C k g) k (pairInput a b) = true) ∧
      (∀ x, forbidden G C k x → gateVal n (replace C k g) k x = false) := by
  let D := replace C k g
  have old := (GuardedReaders.graph_rows_iff G C m).1 correct
  rw [GuardedReaders.graph_rows_iff G _ dm]
  constructor
  · rintro ⟨edges,indep⟩
    constructor
    · intro a b must
      cases h : gateVal n D k (pairInput a b) with
      | true => rfl
      | false =>
        exact False.elim (Bool.noConfusion ((edges a b must.1).symm.trans
          (((clamp_read C inside g dm _).1 h).trans must.2)))
    · intro x block
      cases h : gateVal n D k x with
      | false => rfl
      | true =>
        exact False.elim (Bool.noConfusion ((indep x block.1).symm.trans
          (((clamp_read C inside g dm _).2 h).trans block.2)))
  · rintro ⟨keep,avoid⟩
    constructor
    · intro a b edge
      let x := pairInput a b
      cases h : gateVal n D k x with
      | true => exact ((clamp_read C inside g dm x).2 h).trans ((clamp_bounds C inside m x).2 (old.1 a b edge))
      | false =>
        rw [(clamp_read C inside g dm x).1 h]
        cases hz : circuitFun n (zero C k) x with
        | true => rfl
        | false => exact False.elim (Bool.noConfusion (h.symm.trans (keep a b ⟨edge,hz⟩)))
    · intro x indep
      cases h : gateVal n D k x with
      | false =>
        rw [(clamp_read C inside g dm x).1 h]
        cases hz : circuitFun n (zero C k) x with
        | false => rfl
        | true => exact False.elim (Bool.noConfusion (((clamp_bounds C inside m x).1 hz).symm.trans (old.2 x indep)))
      | true =>
        rw [(clamp_read C inside g dm x).2 h]
        cases hi : circuitFun n (one C k) x with
        | false => rfl
        | true => exact False.elim (Bool.noConfusion (h.symm.trans (avoid x ⟨indep,hi⟩)))


private def copy (C : Circuit) (k t : Nat) := replace C k ⟨.or,[t]⟩

private theorem copy_value {n} {C : Circuit} {k t : Nat} (inside : k < C.size) (early : t < n+k)
    (x : Fin n → Bool) : gateVal n (copy C k t) k x = val (copy C k t) (List.ofFn x) t := by
  change val (copy C k t) (List.ofFn x) (n+k) = _
  rw [val_gate (n := n) (by simp) (by simpa [copy,Circuit.size] using inside),
    show gateAt (copy C k t) k = _ from replace_at inside]
  simp [GateOp.eval,early]

private theorem copy_source {n} {C : Circuit} {k t : Nat} (m : Monotone2 C) (inside : k < C.size)
    (early : t < n+k) (x : Fin n → Bool) : gateVal n (copy C k t) k x = val C (List.ofFn x) t := by
  rw [copy_value inside early]
  by_cases ht : t < n
  · rw [Outside.L_meta_5465.val_input (n := n) (by simp) ht,Outside.L_meta_5465.val_input (n := n) (by simp) ht]
  · obtain ⟨i,rfl⟩ : ∃ i, t=n+i := ⟨t-n,by omega⟩
    exact val_before m (by omega) x

/-- For every earlier wire, some critical graph edge needs more than that wire supplies,
or some independent input would become a false positive if that wire were used here. -/
theorem every_wire_fails {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit} {k t}
    (least : IsMinimalMonoCircuit n C) (correct : circuitFun n C = graphFun G ∅)
    (inside : k < C.size) (early : t < n+k) :
    (∃ a b, needed G C k a b ∧ val C (List.ofFn (pairInput a b)) t = false) ∨
    ∃ x, forbidden G C k x ∧ val C (List.ofFn x) t = true := by
  classical
  by_contra! tests
  let D := copy C k t
  have mono : Monotone2 D := replace_mono least.1 (by simp) (by simp)
  have exactCopy : circuitFun n D = graphFun G ∅ := by
    apply (rewrite_correct_iff G inside least.1 correct _ mono).2
    constructor
    · intro a b needed
      change gateVal n D k (pairInput a b) = true
      rw [show gateVal n D k (pairInput a b) = _ from copy_source least.1 inside early _]
      have stay := tests.1 a b needed
      cases h : val C (List.ofFn (pairInput a b)) t <;> simp_all
    · intro x block
      change gateVal n D k x = false
      rw [show gateVal n D k x = _ from copy_source least.1 inside early _]
      have stay := tests.2 x block
      cases h : val C (List.ofFn x) t <;> simp_all
  let E := Outside.L_meta_2668.bypass n D k t
  have eq : circuitFun n E = circuitFun n D := by
    funext x
    apply Outside.L_meta_2668.bypass_eval_eq (n := n) (by simp)
      (fun j hj => (mono _ (Outside.L_meta_5465.gateAt_mem hj)).1)
      (by simpa [D,copy,Circuit.size] using inside) (Or.inl early)
    exact copy_value inside early x
  have le := least.2 E (Outside.L_meta_2668.bypass_mono mono) (eq.trans (exactCopy.trans correct.symm))
  have sz : E.size = D.gates.length - 1 := Outside.L_meta_2668.bypass_length ..
  have len : D.gates.length = C.size := replace_length ..
  omega

private theorem forbidden_turns_off {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} {k} (inside : k < C.size) (m : Monotone2 C) (eq : circuitFun n C = graphFun G ∅)
    {x : Fin n → Bool} (block : forbidden G C k x) : gateVal n C k x = false := by
  cases h : gateVal n C k x with
  | false => rfl
  | true =>
    have same : circuitFun n (one C k) x = circuitFun n C x :=
      propagate k x Eq (fun _ => rfl) opMono_eq m (replace_length ..) (fun _ ne => replace_elsewhere ne)
        C.output (fun _ => (one_value inside x).trans h.symm)
    exact False.elim (Bool.noConfusion (block.2.symm.trans (same.trans ((congrFun eq x).trans block.1))))

/-- Each parent of a two-input AND in a minimum circuit fires alone on an independent
input where clamping the gate high causes a false positive. The two witnesses can differ. -/
theorem and_parent_witness {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit} {k s t}
    (least : IsMinimalMonoCircuit n C) (exactC : circuitFun n C = graphFun G ∅)
    (inside : k < C.size) (hs : s<n+k) (ht : t<n+k)
    (site : gateAt C k = ⟨.and,[s,t]⟩ ∨ gateAt C k = ⟨.and,[t,s]⟩) :
    ∃ x, forbidden G C k x ∧ val C (List.ofFn x) s = true ∧ val C (List.ofFn x) t = false := by
  have form (x : Fin n → Bool) :
      gateVal n C k x = (val C (List.ofFn x) s && val C (List.ofFn x) t) := by
    change val C (List.ofFn x) (n+k) = _
    rw [val_gate (n := n) (by simp) inside]
    rcases site with h|h <;> simp [h,GateOp.eval,hs,ht,Bool.and_comm]
  rcases every_wire_fails G least exactC inside hs with ⟨a,b,need,low⟩ | ⟨x,block,high⟩
  · have old := needed_turns_on G least.1 inside exactC need
    simp [form,low] at old
  · have old := forbidden_turns_off G inside least.1 exactC block
    exact ⟨x,block,high,by simpa [form,high] using old⟩

/-- Each parent of a two-input OR in a minimum circuit alone supplies some
output-critical edge. Swapping the parents supplies a second distinct unordered edge. -/
theorem or_parent_witness {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit} {k s t}
    (least : IsMinimalMonoCircuit n C) (exactC : circuitFun n C = graphFun G ∅)
    (inside : k < C.size) (hs : s<n+k) (ht : t<n+k)
    (site : gateAt C k = ⟨.or,[s,t]⟩ ∨ gateAt C k = ⟨.or,[t,s]⟩) :
    ∃ a b, needed G C k a b ∧ val C (List.ofFn (pairInput a b)) s = true ∧
      val C (List.ofFn (pairInput a b)) t = false := by
  have form (x : Fin n → Bool) :
      gateVal n C k x = (val C (List.ofFn x) s || val C (List.ofFn x) t) := by
    change val C (List.ofFn x) (n+k) = _
    rw [val_gate (n := n) (by simp) inside]
    rcases site with h|h <;> simp [h,GateOp.eval,hs,ht,Bool.or_comm]
  rcases every_wire_fails G least exactC inside ht with ⟨a,b,need,low⟩ | ⟨x,block,high⟩
  · have old := needed_turns_on G least.1 inside exactC need
    exact ⟨a,b,need,by simpa [form,low] using old,low⟩
  · have old := forbidden_turns_off G inside least.1 exactC block
    simp [form,high] at old


theorem or_multiple_critical {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit} {k s t}
    (least : IsMinimalMonoCircuit n C) (exactC : circuitFun n C = graphFun G ∅)
    (inside : k < C.size) (hs : s<n+k) (ht : t<n+k) (site : gateAt C k = ⟨.or,[s,t]⟩) :
    MultipleCritical G C k := by
  obtain ⟨a,b,first,high,_⟩ := or_parent_witness G least exactC inside hs ht (Or.inl site)
  obtain ⟨c,d,second,_,low⟩ := or_parent_witness G least exactC inside ht hs (Or.inr site)
  refine ⟨a,b,c,d,first,second,?_⟩
  rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
  · exact Bool.noConfusion (high.symm.trans low)
  · have flip : pairInput a b = pairInput b a := by funext i; simp [pairInput,or_comm]
    exact Bool.noConfusion (high.symm.trans (flip ▸ low))


/-- No input to a genuine binary AND in a global minimum can imply the output edge function. -/
theorem and_parent_not_sound {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit} {k s t}
    (least : IsMinimalMonoCircuit n C) (f : circuitFun n C = graphFun G ∅)
    (inside : k < C.size) (hs : s<n+k) (ht : t<n+k)
    (site : gateAt C k = ⟨.and,[s,t]⟩ ∨ gateAt C k = ⟨.and,[t,s]⟩) :
    ¬ (∀ x, val C (List.ofFn x) s = true → graphFun G ∅ x = true) := by
  intro sound
  obtain ⟨x,block,on,_⟩ := and_parent_witness G least f inside hs ht site
  exact Bool.noConfusion ((sound x on).symm.trans block.1)

/-- No input to a genuine binary OR in a global minimum is already true on every graph edge. -/
theorem or_parent_not_complete {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit} {k s t}
    (least : IsMinimalMonoCircuit n C) (f : circuitFun n C = graphFun G ∅)
    (inside : k < C.size) (hs : s<n+k) (ht : t<n+k)
    (site : gateAt C k = ⟨.or,[s,t]⟩ ∨ gateAt C k = ⟨.or,[t,s]⟩) :
    ¬ (∀ a b, G.Adj a b → val C (List.ofFn (pairInput a b)) s = true) := by
  intro complete
  obtain ⟨a,b,need,_,off⟩ := or_parent_witness G least f inside ht hs site.symm
  exact Bool.noConfusion ((complete a b need.1).symm.trans off)

end PEqualNP.Research.GatePinning
