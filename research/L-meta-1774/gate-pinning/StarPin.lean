import Pin

namespace PEqualNP.Research.GatePinning

open CircuitLowerBounds EdgeOwnership MetaComplexity MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_5465 (val val_gate val_input val_ofFn opMono_eq opMono_imp)

def pinSide {n} (C : Circuit) (k : Nat) (v : Fin n) (t : Nat) : Circuit := replace C k ⟨.and,[v,t]⟩

private theorem earlier_wire {n} (C : Circuit) (g : Gate) {k t : Nat} (legal : Monotone2 C)
    (early : t < n+k) (x : Fin n → Bool) : val (replace C k g) (List.ofFn x) t = val C (List.ofFn x) t := by
  by_cases ht : t < n
  · rw [val_input (n := n) (by simp) ht,val_input (n := n) (by simp) ht]
  · obtain ⟨i,rfl⟩ : ∃ i, t=n+i := ⟨t-n,by omega⟩
    exact val_before legal (by omega) x

private theorem bin_site {n} (C : Circuit) {k s t : Nat} (inside : k < C.gates.length)
    (gate : gateAt C k = ⟨.and,[s,t]⟩) (hs : s < n+k) (ht : t < n+k) (x : Fin n → Bool) :
    gateVal n C k x = (val C (List.ofFn x) s && val C (List.ofFn x) t) := by
  change val C (List.ofFn x) (n+k) = _
  rw [val_gate (n := n) (by simp) inside,gate]
  simp [GateOp.eval,hs,ht]

private theorem side_value {n} (C : Circuit) (k : Nat) (v : Fin n) (t : Nat) (inside : k < C.gates.length)
    (legal : Monotone2 C) (ht : t < n+k) (x : Fin n → Bool) :
    gateVal n (pinSide C k v t) k x = (x v && val C (List.ofFn x) t) := by
  rw [bin_site (pinSide C k v t) (by simpa [pinSide] using inside) (replace_at inside) (by omega) ht,
    val_ofFn]
  exact congrArg (fun b => x v && b) (earlier_wire C _ legal ht x)

private theorem clamped_output {n} (C : Circuit) (k : Nat) (inside : k < C.gates.length) (legal : Monotone2 C)
    (x : Fin n → Bool) (off : gateVal n C k x = false) : circuitFun n (zero C k) x = circuitFun n C x :=
  propagate k x Eq (fun _ => rfl) opMono_eq legal (replace_length ..) (fun _ h => replace_elsewhere h) C.output
    (fun _ => (zero_value inside x).trans off.symm)

/-- An edge lost by clamping a gate must turn that gate on in the original circuit. -/
theorem needed_turns_on {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit} {k : Nat}
    (legal : Monotone2 C) (inside : k < C.gates.length) (correct : circuitFun n C = graphFun G ∅)
    {a b : Fin n} (need : needed G C k a b) : gateVal n C k (pairInput a b) = true := by
  cases hb : gateVal n C k (pairInput a b) with
  | true => rfl
  | false =>
    have out := clamped_output C k inside legal _ hb
    have yes := ((GuardedReaders.graph_rows_iff G C legal).1 correct).1 a b need.1
    exact False.elim (Bool.noConfusion (need.2.symm.trans (out.trans yes)))

/-- At an arbitrary two-input AND, replace the first operand by a single input `v`.
It suffices that `v` implies that operand and every clamping-critical edge contains `v`.
The remaining operand can be any earlier circuit wire. -/
theorem pin_critical_star {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit} {k s t : Nat}
    (legal : Monotone2 C) (correct : circuitFun n C = graphFun G ∅) (inside : k < C.gates.length)
    (site : gateAt C k = ⟨.and,[s,t]⟩ ∨ gateAt C k = ⟨.and,[t,s]⟩) (hs : s < n+k) (ht : t < n+k) (v : Fin n)
    (forces : ∀ x : Fin n → Bool, x v = true → val C (List.ofFn x) s = true)
    (star : ∀ a b, needed G C k a b → a=v ∨ b=v) :
    let D := pinSide C k v t
    Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size = C.size ∧
    (∀ i, i ≠ k → ∀ a b, Owns n C i a b → Owns n D i a b) ∧
    (∀ a b, Owns n D k a b → a=v ∨ b=v) ∧
    (∀ a b, Owns n C k a b → (a=v ∨ b=v) → Owns n D k a b) := by
  intro D
  have dlegal : Monotone2 D := replace_mono legal (by simp) (by simp)
  have form (x : Fin n → Bool) : gateVal n C k x = (val C (List.ofFn x) s && val C (List.ofFn x) t) := by
    rcases site with direct | reverse
    · exact bin_site C inside direct hs ht x
    · exact (bin_site C inside reverse ht hs x).trans (Bool.and_comm ..)
  have hand : (gateAt C k).op = .and := site.elim (congrArg Gate.op) (congrArg Gate.op)
  have below (x : Fin n → Bool) : gateVal n D k x = true → gateVal n C k x = true := by
    rw [side_value C k v t inside legal ht,form x]
    intro h
    obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp h
    exact Bool.and_eq_true_iff.mpr ⟨forces x a,b⟩
  have keep (a b : Fin n) (w : gateVal n C k (pairInput a b) = true) (hit : a=v ∨ b=v) :
      gateVal n D k (pairInput a b) = true := by
    rw [side_value C k v t inside legal ht]
    rw [form] at w
    apply Bool.and_eq_true_iff.mpr
    refine ⟨?_,(Bool.and_eq_true_iff.mp w).2⟩
    rcases hit with rfl | rfl <;> simp [pairInput]
  have subsetIn (w) (hw : w ∈ ([v.val,t] : List Nat)) : w<n ∨ w∈(gateAt C k).inputs := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl
    · exact Or.inl v.isLt
    · exact Or.inr (by rcases site with h | h <;> simp [h])
  refine ⟨dlegal,subgate_correct G inside legal correct _ dlegal below
    (fun a b need => keep a b (needed_turns_on G legal inside correct need) (star a b need)),
    replace_length ..,?_,?_,?_⟩
  · intro i ne a b own
    exact other_owners_survive legal hand subsetIn below ne own
  · intro a b own
    have h := own.2.2.1
    rw [side_value C k v t inside legal ht] at h
    have g := (Bool.and_eq_true_iff.mp h).1
    simp only [pairInput,decide_eq_true_eq] at g
    exact g.imp Eq.symm Eq.symm
  · intro a b own hit
    refine ⟨by simpa [D,pinSide] using inside,congrArg Gate.op (replace_at inside),keep a b own.2.2.1 hit,?_⟩
    intro i hi path op
    have ok : (gateAt C i).op = .and := by
      exact (congrArg Gate.op (show gateAt D i = gateAt C i from replace_elsewhere hi.ne)).symm.trans op
    have old := own.2.2.2 i hi (cone_subread C k _ subsetIn path) ok
    exact (val_before legal hi _).trans old

end PEqualNP.Research.GatePinning
