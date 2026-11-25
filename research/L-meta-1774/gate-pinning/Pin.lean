import Omit
import PEqualNP.Outside.L_meta_4846
import PEqualNP.Outside.L_meta_5465

namespace PEqualNP.Research.GatePinning

open CircuitLowerBounds EdgeOwnership MetaComplexity MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_5465 (val val_gate val_ge val_input val_ofFn opMono_eq opMono_imp gateAt_mem)

/-- Rewire an existing gate without changing wire names or the output index. -/
def replace (C : Circuit) (k : Nat) (g : Gate) : Circuit := ⟨C.gates.set k g,C.output⟩

@[simp] theorem replace_length (C : Circuit) (k : Nat) (g : Gate) :
    (replace C k g).gates.length = C.gates.length := by simp [replace]

theorem replace_at {C : Circuit} {k : Nat} {g : Gate} (inside : k < C.gates.length) :
    gateAt (replace C k g) k = g := by
  simp [replace,gateAt,List.getD_eq_getElem?_getD,inside]

theorem replace_elsewhere {C : Circuit} {k j : Nat} {g : Gate} (ne : j ≠ k) :
    gateAt (replace C k g) j = gateAt C j := by
  simp [replace,gateAt,List.getD_eq_getElem?_getD,Ne.symm ne]

theorem cone_step {n : Nat} {C : Circuit} {k i : Nat} (inside : i < C.gates.length) :
    InCone n C k i ↔ ∃ w ∈ (gateAt C i).inputs, n ≤ w ∧ w < n+i ∧
      (k = w-n ∨ InCone n C k (w-n)) := by
  rw [Outside.L_meta_4846.gateAt_eq C i inside]
  exact Outside.L_meta_4846.cone_iff n C.gates i inside k

def feeds {n : Nat} (C : Circuit) (k w : Nat) := n ≤ w ∧ (w = n+k ∨ InCone n C k (w-n))

private theorem feeds_step {n} {C : Circuit} {k i u : Nat} (inside : i < C.gates.length)
    (read : u ∈ (gateAt C i).inputs) (earlier : u < n+i) (fromK : feeds (n := n) C k u) :
    feeds (n := n) C k (n+i) := by
  refine ⟨by omega,Or.inr ?_⟩
  rw [Nat.add_sub_cancel_left]
  exact (cone_step inside).2 ⟨u,read,fromK.1,earlier,fromK.2.imp (fun h => by omega) id⟩

/-- A one-site relation propagates through all later monotone gates. Outside the original
fanout cone, the changed gate value is irrelevant. Forward and out-of-range wires read false. -/
theorem propagate {n} {C D : Circuit} (k : Nat) (x : Fin n → Bool) (R : Bool → Bool → Prop)
    (reflR : ∀ b, R b b) (lift : Outside.L_meta_5465.OpMono R)
    (legal : Monotone2 C) (len : D.gates.length = C.gates.length)
    (same : ∀ j, j ≠ k → gateAt D j = gateAt C j) (w : Nat)
    (localR : feeds (n := n) C k w → R (gateVal n D k x) (gateVal n C k x)) :
    R (val D (List.ofFn x) w) (val C (List.ofFn x) w) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases input : w < n
    · rw [val_input (n := n) (by simp) input,val_input (n := n) (by simp) input]
      exact reflR _
    by_cases out : n + C.gates.length ≤ w
    · rw [val_ge (n := n) (by simp) (by omega : n+D.gates.length ≤ w),
        val_ge (n := n) (by simp) out]
      exact reflR _
    obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
    by_cases target : j=k
    · subst j
      exact localR ⟨by omega,Or.inl rfl⟩
    have inside : j < C.gates.length := by omega
    rw [val_gate (n := n) (by simp) (by omega : j < D.gates.length),
      val_gate (n := n) (by simp) inside,same j target]
    apply lift _ (legal _ (gateAt_mem inside)).1
    intro u read
    by_cases early : u < n+j
    · simp only [early,ite_true]
      exact ih u early (fun feedsU => localR (feeds_step inside read early feedsU))
    · simp [early,reflR]

theorem cone_subread {n : Nat} (C : Circuit) (k : Nat) (g : Gate)
    (subread : ∀ w ∈ g.inputs, w < n ∨ w ∈ (gateAt C k).inputs)
    {i j} (path : InCone n (replace C k g) i j) : InCone n C i j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    have insideD := Outside.L_meta_4846.cone_lt n (replace C k g).gates i j path
    have inside : j < C.gates.length := replace_length C k g ▸ insideD
    obtain ⟨w,read,gate,earlier,h⟩ := (cone_step insideD).1 path
    have oldRead : w ∈ (gateAt C j).inputs := by
      by_cases target : j=k
      · subst j
        rw [replace_at inside] at read
        exact (subread w read).resolve_left (Nat.not_lt_of_ge gate)
      · simpa [replace_elsewhere target] using read
    apply (cone_step inside).2
    exact ⟨w,oldRead,gate,earlier,h.imp id (fun path => ih (w-n) (by omega) path)⟩

theorem replace_mono {C : Circuit} {k : Nat} {g : Gate} (m : Monotone2 C)
    (go : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp)) (gl : g.inputs.length ≤ 2) : Monotone2 (replace C k g) := by
  intro a ha
  rcases List.mem_or_eq_of_mem_set ha with ha | rfl
  · exact m a ha
  · exact ⟨go,gl⟩

/-- Narrowing an AND to a gate using only primary inputs or original operands preserves
all previously owned edges of every other AND. The new gate may have arbitrarily many readers. -/
theorem other_owners_survive {n} {C : Circuit} {k : Nat} {g : Gate}
    (legal : Monotone2 C) (oldAnd : (gateAt C k).op = .and)
    (subread : ∀ w ∈ g.inputs, w < n ∨ w ∈ (gateAt C k).inputs)
    (narrow : ∀ x : Fin n → Bool, gateVal n (replace C k g) k x = true → gateVal n C k x = true)
    {i u v} (ne : i ≠ k) (own : Owns n C i u v) : Owns n (replace C k g) i u v := by
  let D := replace C k g
  let x := pairInput u v
  have len : D.gates.length = C.gates.length := replace_length _ _ _
  have same (j) (jk : j ≠ k) : gateAt D j = gateAt C j := replace_elsewhere jk
  have less (t) : gateVal n D t x = true → gateVal n C t x = true :=
    propagate k x (fun a b => a = true → b = true) (fun _ => id) opMono_imp legal len same (n+t)
      (fun _ => narrow x)
  refine ⟨len ▸ own.1,(congrArg Gate.op (same i ne)).trans own.2.1,?_,?_⟩
  · have eq : gateVal n D i x = gateVal n C i x := by
      apply propagate k x Eq (fun _ => rfl) opMono_eq legal len same (n+i)
      rintro ⟨_,h | path⟩
      · exact False.elim (ne (by omega))
      · rw [Nat.add_sub_cancel_left] at path
        have before := Outside.L_meta_4846.cone_idx n C.gates i k path
        have off := own.2.2.2 k before path oldAnd
        cases h : gateVal n D k x with
        | false => exact off.symm
        | true => exact False.elim (Bool.noConfusion ((less k h).symm.trans off))
    exact eq.trans own.2.2.1
  · intro j ji path hand
    have oldPath := cone_subread C k g subread path
    have oldOp : (gateAt C j).op = .and := by
      by_cases jk : j = k
      · simpa [jk] using oldAnd
      · rw [replace_elsewhere jk] at hand
        exact hand
    have off := own.2.2.2 j ji oldPath oldOp
    cases h : gateVal n D j x with
    | false => rfl
    | true => exact False.elim (Bool.noConfusion ((less j h).symm.trans off))

def pin {n} (C : Circuit) (k : Nat) (u v : Fin n) : Circuit := replace C k ⟨.and,[u,v]⟩
def zero (C : Circuit) (k : Nat) := replace C k ⟨.or,[]⟩

private theorem pin_primary {n} (u v : Fin n) : ∀ w ∈ ([u.val,v.val] : List Nat), w < n := by
  intro w hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl
  · exact u.isLt
  · exact v.isLt

theorem pin_value {n} {C : Circuit} {k : Nat} (u v : Fin n) (inside : k < C.gates.length) (x : Fin n → Bool) :
    gateVal n (pin C k u v) k x = (x u && x v) := by
  change val (pin C k u v) (List.ofFn x) (n+k) = _
  rw [val_gate (n := n) (by simp) (by simpa [pin] using inside),show gateAt (pin C k u v) k = _ from replace_at inside]
  simp [GateOp.eval,val_ofFn,show u.val < n+k by omega,show v.val < n+k by omega]

theorem zero_value {n} {C : Circuit} {k : Nat} (inside : k < C.gates.length) (x : Fin n → Bool) :
    gateVal n (zero C k) k x = false := by
  change val (zero C k) (List.ofFn x) (n+k) = _
  rw [val_gate (n := n) (by simp) (by simpa [zero] using inside),show gateAt (zero C k) k = _ from replace_at inside]
  rfl

theorem pin_narrows {n} {C : Circuit} {k : Nat} {u v : Fin n} (legal : Monotone2 C) (own : Owns n C k u v)
    (x : Fin n → Bool) : gateVal n (pin C k u v) k x = true → gateVal n C k x = true := by
  rw [pin_value u v own.1]
  rintro ht
  obtain ⟨hu,hv⟩ := Bool.and_eq_true_iff.mp ht
  apply Outside.L_meta_2573.wires_mono C (Outside.L_meta_2573.mono2_ops C legal) (pairInput u v) x _ (n+k) own.2.2.1
  intro a h
  simp only [pairInput,decide_eq_true_eq] at h
  rcases h with rfl | rfl <;> assumption

theorem pin_owns {n} {C : Circuit} {k : Nat} (u v : Fin n) (inside : k < C.gates.length) :
    Owns n (pin C k u v) k u v := by
  refine ⟨by simpa [pin] using inside,congrArg Gate.op (replace_at inside),?_,?_⟩
  · simp [pin_value u v inside,pairInput]
  · intro i hi cone h
    have atK : gateAt (pin C k u v) k = ⟨.and,[u,v]⟩ := replace_at inside
    obtain ⟨w,read,nw,_,_⟩ := (cone_step (by simpa [pin] using inside)).1 cone
    rw [atK] at read
    have := pin_primary u v w read
    omega

theorem pin_has_center {n} {C : Circuit} {k : Nat} (u v : Fin n) (inside : k < C.gates.length)
    {a b : Fin n} (own : Owns n (pin C k u v) k a b) : a = u ∨ b = u := by
  have h := own.2.2.1
  rw [pin_value u v inside] at h
  have a := (Bool.and_eq_true_iff.mp h).1
  simp only [pairInput,decide_eq_true_eq] at a
  exact a.imp Eq.symm Eq.symm

/-- Edges lost after clamping gate `k` to false. This depends on the full fanout of `k`. -/
def needed {n} (G : SimpleGraph (Fin n)) (C : Circuit) (k : Nat) (a b : Fin n) : Prop :=
  G.Adj a b ∧ circuitFun n (zero C k) (pairInput a b) = false

/-- A replacement whose output only decreases needs to be verified on the edges
that fail when the old gate is clamped. This test applies to arbitrary fanout. -/
theorem subgate_correct {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit} {k : Nat}
    (inside : k < C.gates.length) (legal : Monotone2 C) (correct : circuitFun n C = graphFun G ∅)
    (g : Gate) (dlegal : Monotone2 (replace C k g))
    (narrow : ∀ x : Fin n → Bool, gateVal n (replace C k g) k x = true → gateVal n C k x = true)
    (keep : ∀ a b, needed G C k a b → gateVal n (replace C k g) k (pairInput a b) = true) :
    circuitFun n (replace C k g) = graphFun G ∅ := by
  let D := replace C k g
  let Z := zero C k
  have len : D.gates.length = C.gates.length := replace_length ..
  have same (j) (ne : j ≠ k) : gateAt D j = gateAt C j := replace_elsewhere ne
  apply (GuardedReaders.graph_rows_iff G D dlegal).2
  constructor
  · intro a b edge
    let x := pairInput a b
    cases hz : circuitFun n Z x with
    | true =>
      have sameZD (j) (ne : j ≠ k) : gateAt Z j = gateAt D j := (replace_elsewhere ne).trans (same j ne).symm
      exact propagate k x (fun a b => a=true → b=true) (fun _ => id) opMono_imp dlegal
        ((replace_length ..).trans len.symm) sameZD D.output
        (fun _ h => False.elim (Bool.noConfusion ((zero_value inside x).symm.trans h))) hz
    | false =>
      have yes := keep a b ⟨edge,hz⟩
      have eq : circuitFun n D x = circuitFun n C x :=
        propagate k x Eq (fun _ => rfl) opMono_eq legal len same C.output (fun _ => yes.trans (narrow x yes).symm)
      exact eq.trans (((GuardedReaders.graph_rows_iff G C legal).1 correct).1 a b edge)
  · intro x hx
    have mono := propagate k x (fun a b => a=true → b=true) (fun _ => id) opMono_imp legal len same C.output
      (fun _ => narrow x)
    cases h : circuitFun n D x with
    | false => rfl
    | true => exact False.elim (Bool.noConfusion ((mono h).symm.trans ((congrFun correct x).trans hx)))

/-- If every affected graph edge is the chosen owned edge, pinning the gate to that
pair is a function-preserving, equal-size edit for arbitrary fanout. -/
theorem pin_correct {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    (legal : Monotone2 C) (correct : circuitFun n C = graphFun G ∅) {k : Nat} {u v : Fin n}
    (own : Owns n C k u v) (single : ∀ a b, needed G C k a b → (a=u ∧ b=v) ∨ (a=v ∧ b=u)) :
    circuitFun n (pin C k u v) = graphFun G ∅ := by
  have legalD : Monotone2 (pin C k u v) := replace_mono legal (by simp) (by simp)
  apply subgate_correct G own.1 legal correct _ legalD (pin_narrows legal own)
  intro a b e
  change gateVal n (pin C k u v) k (pairInput a b) = true
  rw [pin_value u v own.1]
  rcases single a b e with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [pairInput]

theorem cone_before {n : Nat} (C : Circuit) (k : Nat) (g : Gate) {i j : Nat} (early : j < k)
    (path : InCone n C i j) : InCone n (replace C k g) i j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    have inside := Outside.L_meta_4846.cone_lt n C.gates i j path
    obtain ⟨w,read,gate,earlier,h⟩ := (cone_step inside).1 path
    apply (cone_step (by simpa using inside)).2
    rw [replace_elsewhere (Nat.ne_of_lt early)]
    exact ⟨w,read,gate,earlier,h.imp id (fun p => ih (w-n) (by omega) (by omega) p)⟩

theorem val_before {n} {C : Circuit} {k : Nat} {g : Gate} (legal : Monotone2 C)
    {i : Nat} (early : i < k) (x : Fin n → Bool) : gateVal n (replace C k g) i x = gateVal n C i x := by
  apply propagate k x Eq (fun _ => rfl) opMono_eq legal (replace_length ..) (fun _ ne => replace_elsewhere ne) (n+i)
  rintro ⟨_,eq | path⟩
  · omega
  · rw [Nat.add_sub_cancel_left] at path
    have := Outside.L_meta_4846.cone_idx n C.gates i k path
    omega

theorem before_new_to_old {n} {C : Circuit} {k : Nat} {g : Gate} {p q : Fin n}
    (legal : Monotone2 C) {i : Nat} (early : i < k) :
    Owns n (replace C k g) i p q → Owns n C i p q := by
  have eq : gateAt (replace C k g) i = gateAt C i := replace_elsewhere early.ne
  rintro ⟨inside,and,yes,first⟩
  refine ⟨by simpa using inside,(congrArg Gate.op eq).symm.trans and,
    (val_before legal early _).symm.trans yes,?_⟩
  intro j ji path op
  have jk : j < k := ji.trans early
  have op' : (gateAt (replace C k g) j).op = .and := (congrArg Gate.op (replace_elsewhere jk.ne)).trans op
  exact (val_before legal jk _).symm.trans (first j ji (cone_before C k _ early path) op')

theorem pin_owns_before {n} {C : Circuit} {k : Nat} {u v p q : Fin n} (legal : Monotone2 C)
    (target : Owns n C k u v) {i : Nat} (early : i < k) :
    Owns n (pin C k u v) i p q ↔ Owns n C i p q := by
  constructor
  · exact before_new_to_old legal early
  · exact other_owners_survive legal target.2.1 (fun w hw => Or.inl (pin_primary u v w hw))
      (pin_narrows legal target) early.ne

end PEqualNP.Research.GatePinning
