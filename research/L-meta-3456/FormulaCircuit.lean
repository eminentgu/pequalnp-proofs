import PEqualNP.Defs

namespace SingletonFiniteFormula

inductive Op where
  | meet | join
  deriving DecidableEq

def Op.apply : Op → Bool → Bool → Bool
  | .meet, a, b => a && b
  | .join, a, b => a || b

inductive Formula (α : Type) where
  | atom (x : α)
  | node (op : Op) (left right : Formula α)

namespace Formula

variable {α : Type}

def eval (z : α → Bool) : Formula α → Bool
  | .atom x => z x
  | .node op l r => op.apply (eval z l) (eval z r)

def leaves : Formula α → Nat
  | .atom _ => 1
  | .node _ l r => leaves l + leaves r

def gates : Formula α → Nat
  | .atom _ => 0
  | .node _ l r => gates l + gates r + 1

theorem leaves_eq (f : Formula α) : f.leaves = f.gates + 1 := by
  induction f with
  | atom => rfl
  | node op l r hl hr => simp [leaves, gates, hl, hr]; omega

variable [DecidableEq α]

def single (x : α) : α → Bool := fun i => decide (i = x)

def evalOpt (z : α → Bool) : Option (Formula α) → Bool
  | none => false
  | some f => eval z f

def leavesOpt : Option (Formula α) → Nat
  | none => 0
  | some f => f.leaves

def combine : Op → Option (Formula α) → Option (Formula α) → Option (Formula α)
  | op, some a, some b => some (.node op a b)
  | .meet, _, _ => none
  | .join, a, b => a.or b

omit [DecidableEq α] in
theorem combine_eval (op : Op) (a b : Option (Formula α)) (z : α → Bool) :
    evalOpt z (combine op a b) = op.apply (evalOpt z a) (evalOpt z b) := by
  cases op <;> cases a <;> cases b <;> simp [combine, evalOpt, eval, Op.apply]

omit [DecidableEq α] in
theorem combine_leaves (op : Op) (a b : Option (Formula α)) :
    leavesOpt (combine op a b) ≤ leavesOpt a + leavesOpt b := by
  cases op <;> cases a <;> cases b <;> simp [combine, leavesOpt, leaves]

def cofactor (x : α) : Formula α → Option (Formula α)
  | .atom i => if i = x then none else some (.atom i)
  | .node op a b => combine op (cofactor x a) (cofactor x b)

theorem cofactor_eval (f : Formula α) (x : α) (z : α → Bool) :
    evalOpt z (cofactor x f) = f.eval (fun i => if i = x then false else z i) := by
  induction f with
  | atom i => by_cases h : i = x <;> simp [cofactor, evalOpt, eval, h]
  | node op a b ha hb => simp [cofactor, combine_eval, eval, ha, hb]

theorem cofactor_leaves (f : Formula α) (x : α) :
    leavesOpt (cofactor x f) ≤ f.leaves := by
  induction f with
  | atom i => by_cases h : i = x <;> simp [cofactor, leavesOpt, leaves, h]
  | node op a b ha hb =>
    exact (combine_leaves _ _ _).trans (Nat.add_le_add ha hb)

theorem cofactor_lt (f : Formula α) (x : α) (h : f.eval (single x) = true) :
    leavesOpt (cofactor x f) < f.leaves := by
  induction f with
  | atom i =>
    have hi : i = x := by simpa [eval, single] using h
    simp [cofactor, leavesOpt, leaves, hi]
  | node op a b ha hb =>
    have hor : a.eval (single x) = true ∨ b.eval (single x) = true := by
      cases op <;> cases h₁ : a.eval (single x) <;> cases h₂ : b.eval (single x) <;>
        simp_all [eval, Op.apply]
    have un := combine_leaves op (cofactor x a) (cofactor x b)
    change leavesOpt (combine op (cofactor x a) (cofactor x b)) < a.leaves + b.leaves
    rcases hor with h | h
    · have := ha h
      have := cofactor_leaves b x
      omega
    · have := hb h
      have := cofactor_leaves a x
      omega

omit [DecidableEq α] in
theorem eval_mono (f : Formula α) (a b : α → Bool)
    (h : ∀ i, a i = true → b i = true) (hf : f.eval a = true) : f.eval b = true := by
  induction f with
  | atom i => exact h i hf
  | node op l r hl hr =>
    cases op with
    | meet =>
      simp only [eval, Op.apply, Bool.and_eq_true] at hf ⊢
      exact ⟨hl hf.1, hr hf.2⟩
    | join =>
      simp only [eval, Op.apply, Bool.or_eq_true] at hf ⊢
      exact hf.elim (fun h => Or.inl (hl h)) (fun h => Or.inr (hr h))

theorem extract_atom (f : Formula α) (x : α) (hf : f.eval (single x) = true) (z : α → Bool) :
    f.eval z = (z x || evalOpt z (cofactor x f)) := by
  cases hx : z x with
  | false =>
    rw [cofactor_eval]
    have hh : (fun i => if i = x then false else z i) = z := by
      funext i
      split <;> simp_all
    rw [hh]
    rfl
  | true =>
    have mono : ∀ i, single x i = true → z i = true := by
      intro i hi
      have e : i = x := by simpa [single] using hi
      simpa [e] using hx
    simpa using eval_mono f _ _ mono hf

def factor (x : α) (a b : Formula α) : Formula α :=
  match cofactor x a, cofactor x b with
  | some a', some b' => .node .join (.atom x) (.node .meet a' b')
  | _, _ => .atom x

theorem factor_eval (x : α) (a b : Formula α)
    (ha : a.eval (single x) = true) (hb : b.eval (single x) = true) (z : α → Bool) :
    (factor x a b).eval z = (Formula.node .meet a b).eval z := by
  change (factor x a b).eval z = (a.eval z && b.eval z)
  rw [extract_atom a x ha z, extract_atom b x hb z]
  cases aa : cofactor x a <;> cases bb : cofactor x b <;> cases hx : z x <;>
    simp [factor, aa, bb, eval, evalOpt, Op.apply, hx]

theorem factor_smaller (x : α) (a b : Formula α)
    (ha : a.eval (single x) = true) (hb : b.eval (single x) = true) :
    (factor x a b).gates < (Formula.node .meet a b).gates := by
  have h₁ := cofactor_lt a x ha
  have h₂ := cofactor_lt b x hb
  cases aa : cofactor x a <;> cases bb : cofactor x b <;>
    simp [factor, aa, bb, gates, leavesOpt, leaves_eq] at *; omega

/-- All AND nodes evaluate to false on every individual input. -/
def Clean : Formula α → Prop
  | .atom _ => True
  | .node op a b => a.Clean ∧ b.Clean ∧
      ¬(op = .meet ∧ ∃ x, a.eval (single x) = true ∧ b.eval (single x) = true)

/-- A dirty formula has an equivalent formula using strictly fewer binary gates. -/
theorem shrink_if_dirty (f : Formula α) (h : ¬ f.Clean) :
    ∃ g : Formula α, g.gates < f.gates ∧ ∀ z, g.eval z = f.eval z := by
  classical
  induction f with
  | atom i => exact (h trivial).elim
  | node op a b ia ib =>
    by_cases ha : a.Clean
    · by_cases hb : b.Clean
      · have bad : op = .meet ∧ ∃ x, a.eval (single x) = true ∧ b.eval (single x) = true := by
          by_contra hn
          exact h ⟨ha, hb, hn⟩
        obtain ⟨rfl, x, hx, hy⟩ := bad
        exact ⟨factor x a b, factor_smaller x a b hx hy, factor_eval x a b hx hy⟩
      · obtain ⟨b', hs, he⟩ := ib hb
        refine ⟨.node op a b', ?_, ?_⟩
        · simp only [gates]; omega
        · intro z; simp only [eval, he]
    · obtain ⟨a', hs, he⟩ := ia ha
      refine ⟨.node op a' b, ?_, ?_⟩
      · simp only [gates]; omega
      · intro z; simp only [eval, he]

/-- Singleton-clean normalization for arbitrary finite binary monotone formulas. -/
theorem normalize (f : Formula α) :
    ∃ g : Formula α, g.Clean ∧ g.gates ≤ f.gates ∧ ∀ z, g.eval z = f.eval z := by
  classical
  by_cases hc : f.Clean
  · exact ⟨f, hc, le_rfl, fun _ => rfl⟩
  · obtain ⟨d, hd, hdf⟩ := shrink_if_dirty f hc
    obtain ⟨g, hg, hgd, he⟩ := normalize d
    exact ⟨g, hg, hgd.trans (Nat.le_of_lt hd), fun z => (he z).trans (hdf z)⟩
termination_by f.gates

end Formula
end SingletonFiniteFormula

namespace SingletonFiniteFormula.Formula
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

variable {n : Nat}

def opcode : Op → GateOp
  | .meet => .and
  | .join => .or

def rootOp : Formula (Fin n) → GateOp
  | .atom _ => .or
  | .node op _ _ => opcode op

def ptr : Formula (Fin n) → Nat → Nat
  | .atom i, _ => i.val
  | .node _ a b, base => base + a.gates + b.gates

def code : Formula (Fin n) → Nat → List Gate
  | .atom _, _ => []
  | .node op a b, base =>
    a.code base ++ b.code (base + a.gates) ++
       [⟨opcode op, [a.ptr base, b.ptr (base + a.gates)]⟩]

def trace : Formula (Fin n) → List (Formula (Fin n))
  | .atom _ => []
  | .node op a b => a.trace ++ b.trace ++ [Formula.node op a b]

theorem code_length (f : Formula (Fin n)) (base : Nat) :
    (f.code base).length = f.gates := by
  induction f generalizing base with
  | atom => rfl
  | node op a b ia ib => simp [code, gates, ia, ib, Nat.add_assoc]

theorem trace_length (f : Formula (Fin n)) : f.trace.length = f.gates := by
  induction f with
  | atom => rfl
  | node op a b ia ib => simp [trace, gates, ia, ib, Nat.add_assoc]

theorem trace_op (f : Formula (Fin n)) (base : Nat) :
    (f.code base).map Gate.op = f.trace.map rootOp := by
  induction f generalizing base with
  | atom => rfl
  | node op a b ia ib => simp [trace, rootOp, code, ia, ib]

theorem ptr_lt (f : Formula (Fin n)) (base : Nat) (h : n ≤ base) :
    f.ptr base < base + f.gates := by
  cases f with
  | atom i => simpa [ptr, gates] using lt_of_lt_of_le i.isLt h
  | node op a b => simp [ptr, gates]; omega

theorem getD_left {α} (a b : List α) (i : Nat) (d : α) (h : i < a.length) :
    (a ++ b).getD i d = a.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_right {α} (a b : List α) (i : Nat) (d : α) :
    (a ++ b).getD (a.length + i) d = b.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem step_pair (op : Op) (w : List Bool) (a b : Nat) :
    step w ⟨opcode op,[a,b]⟩ = w ++ [op.apply (w.getD a false) (w.getD b false)] := by
  cases op <;> simp [step, opcode, Op.apply, GateOp.eval]

theorem code_eval (f : Formula (Fin n)) (z : Fin n → Bool) (w : List Bool)
    (hn : n ≤ w.length) (hw : ∀ i : Fin n, w.getD i false = z i) :
    (f.code w.length).foldl step w = w ++ f.trace.map (eval z) ∧
    (w ++ f.trace.map (eval z)).getD (f.ptr w.length) false = f.eval z := by
  induction f generalizing w with
  | atom i => exact ⟨by simp [code, trace], by simpa [trace, ptr, eval] using hw i⟩
  | node op a b ia ib =>
    let u := w ++ a.trace.map (eval z)
    let v := u ++ b.trace.map (eval z)
    have hu : u.length = w.length + a.gates := by simp [u, trace_length]
    have hv : v.length = w.length + a.gates + b.gates := by simp [v, hu, trace_length]
    obtain ⟨cal, oa⟩ := ia w hn hw
    have huraw (i : Fin n) : u.getD i false = z i :=
      (getD_left _ _ _ _ (lt_of_lt_of_le i.isLt hn)).trans (hw i)
    have hnu : n ≤ u.length := by omega
    obtain ⟨cbr, ob⟩ := ib u hnu huraw
    rw [hu] at cbr ob
    change (v.getD (b.ptr (w.length + a.gates)) false) = _ at ob
    have old : v.getD (a.ptr w.length) false = a.eval z := by
      apply (getD_left u _ _ _ ?_).trans oa
      rw [hu]
      exact ptr_lt a _ hn
    constructor
    · simp only [code, List.foldl_append, List.foldl_cons, List.foldl_nil, cal]
      change step ((b.code (w.length + a.gates)).foldl step u) _ = _
      rw [cbr]
      change step v _ = _
      rw [step_pair, old, ob]
      simp [trace, v, u, eval, List.append_assoc]
    · change (w ++ (a.trace ++ b.trace ++ [Formula.node op a b]).map (eval z)).getD
          (w.length + a.gates + b.gates) false = _
      have lists : w ++ (a.trace ++ b.trace ++ [Formula.node op a b]).map (eval z) =
          v ++ [(Formula.node op a b).eval z] := by simp [v, u, List.append_assoc]
      rw [lists, ← hv]
      simp [List.getD_eq_getElem?_getD]

end SingletonFiniteFormula.Formula

namespace SingletonFiniteFormula.Formula
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

variable {n : Nat}

def Back (base : Nat) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < base + j

theorem back_append {base : Nat} {a b : List Gate} (ha : Back base a)
    (hb : Back (base + a.length) b) : Back base (a ++ b) := by
  intro j hj i hi
  by_cases h : j < a.length
  · rw [List.getElem_append_left h] at hi
    exact ha j h i hi
  · have hj' : j - a.length < b.length := by simp at hj; omega
    rw [List.getElem_append_right (by omega : a.length ≤ j)] at hi
    have := hb (j - a.length) hj' i hi
    omega

theorem code_back (f : Formula (Fin n)) (base : Nat) (hn : n ≤ base) : Back base (f.code base) := by
  induction f generalizing base with
  | atom => intro j hj; simp [code] at hj
  | node op a b ia ib =>
    apply back_append
    · apply back_append (ia _ hn)
      rw [code_length]
      exact ib _ (by omega)
    · intro j hj i hi
      simp only [List.length_cons,List.length_nil] at hj
      have h0 : j = 0 := by omega
      subst j
      simp only [List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
      simp only [List.length_append, code_length, Nat.add_zero]
      rcases hi with rfl | rfl
      · have := ptr_lt a base hn
        omega
      · have := ptr_lt b (base + a.gates) (by omega)
        omega

theorem code_mono (f : Formula (Fin n)) (base : Nat) (g : Gate) (hg : g ∈ f.code base) :
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction f generalizing base with
  | atom => simp [code] at hg
  | node op a b ia ib =>
    simp only [code, List.mem_append, List.mem_singleton] at hg
    rcases hg with (h|h)|rfl
    · exact ia _ h
    · exact ib _ h
    · cases op <;> simp [opcode]

theorem clean_trace (f : Formula (Fin n)) (hc : f.Clean) (t : Formula (Fin n))
    (ht : t ∈ f.trace) (ho : t.rootOp = .and) (i : Fin n) : t.eval (single i) = false := by
  induction f with
  | atom => simp [trace] at ht
  | node op a b ia ib =>
    simp only [trace, List.mem_append, List.mem_singleton] at ht
    rcases ht with (h|h)|rfl
    · exact ia hc.1 h
    · exact ib hc.2.1 h
    · cases op with
      | join => simp [rootOp, opcode] at ho
      | meet =>
        have nod := hc.2.2
        cases ha : a.eval (single i) <;> cases hb : b.eval (single i) <;>
          simp_all [eval, Op.apply]

def circuit (f : Formula (Fin n)) : Circuit := ⟨f.code n, f.ptr n⟩

theorem ofFn_lookup (z : Fin n → Bool) (i : Fin n) : (List.ofFn z).getD i false = z i := by
  simp [List.getD_eq_getElem?_getD]

theorem circuit_wires (f : Formula (Fin n)) (z : Fin n → Bool) :
    f.circuit.wires (List.ofFn z) = List.ofFn z ++ f.trace.map (eval z) := by
  have h := (code_eval f z (List.ofFn z) (by simp) (ofFn_lookup z)).1
  simp only [List.length_ofFn] at h
  exact h

theorem circuit_value (f : Formula (Fin n)) (z : Fin n → Bool) :
    circuitFun n f.circuit z = f.eval z := by
  have h := (code_eval f z (List.ofFn z) (by simp) (ofFn_lookup z)).2
  simp only [List.length_ofFn] at h
  change (f.circuit.wires (List.ofFn z)).getD (f.ptr n) false = _
  rwa [circuit_wires]

theorem circuit_safe (f : Formula (Fin n)) (hc : f.Clean) (j : Nat) (hj : j < f.circuit.gates.length)
    (ho : (gateAt f.circuit j).op = .and) (i : Fin n) :
    (f.circuit.wires (List.ofFn (single i))).getD (n + j) false = false := by
  have hjc : j < (f.code n).length := hj
  have hjt : j < f.trace.length := by simpa [code_length, trace_length] using hjc
  have hop := congrArg (fun (xs : List GateOp) => xs[j]?) (trace_op f n)
  simp only [List.getElem?_map, List.getElem?_eq_getElem hjc, List.getElem?_eq_getElem hjt,
    Option.map_some, Option.some.injEq] at hop
  have gate : (f.code n)[j].op = .and := by
    simpa [gateAt, circuit, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjc] using ho
  have hq := clean_trace f hc f.trace[j] (List.getElem_mem hjt) (hop ▸ gate) i
  rw [circuit_wires]
  have hlist := getD_right (List.ofFn (single i)) (f.trace.map (eval (single i))) j false
  simp only [List.length_ofFn] at hlist
  rw [hlist]
  simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hjt] using hq

/-- A circuit whose function has an equally small monotone formula admits the requested
singleton normalization on the project's actual ordered gates and wires. -/
theorem circuit_normalize_of_formula (C : Circuit) (f : Formula (Fin n))
    (hs : f.gates ≤ C.size) (he : ∀ z, f.eval z = circuitFun n C z) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size ≤ C.size ∧
      (∀ z, circuitFun n D z = circuitFun n C z) ∧
      ∀ j < D.gates.length, (gateAt D j).op = .and →
        ∀ i : Fin n, (D.wires (List.ofFn (single i))).getD (n+j) false = false := by
  obtain ⟨g,hc,hsize,hval⟩ := normalize f
  refine ⟨g.circuit, code_mono g n, ?_, ?_, ?_, circuit_safe g hc⟩
  · intro j hj i hi
    have hj' : j < (g.code n).length := hj
    apply code_back g n le_rfl j hj' i
    simpa [gateAt, circuit, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'] using hi
  · change (g.code n).length ≤ C.size
    rw [code_length]
    exact hsize.trans hs
  · intro z
    exact (circuit_value g z).trans ((hval z).trans (he z))

/-- The incidence problem's full conclusion for a circuit having a no-larger formula.
Neither a girth assumption nor a bound on the number of vertices is needed in this case. -/
theorem incidence_of_formula (N : Nat) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hf : ∃ f : Formula (Fin (N+N)), f.gates ≤ C.size ∧
      ∀ z, f.eval z = circuitFun (N+N) C z)
    (he : ∀ z : Fin (N+N) → Bool, circuitFun (N+N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size ≤ C.size ∧
      (∀ z : Fin (N+N) → Bool, circuitFun (N+N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      ∀ j < D.gates.length, (gateAt D j).op = .and →
        (∀ p : Fin N, (D.wires (List.ofFn (fun i : Fin (N+N) =>
          decide (i = Fin.castAdd N p)))).getD (N+N+j) false = false) ∧
        ∀ l : Fin N, (D.wires (List.ofFn (fun i : Fin (N+N) =>
          decide (i = Fin.natAdd N l)))).getD (N+N+j) false = false := by
  obtain ⟨f,hs,hf⟩ := hf
  obtain ⟨D,hm,hr,hs,hd,ha⟩ := circuit_normalize_of_formula C f hs hf
  refine ⟨D,hm,hr,hs,?_,?_⟩
  · intro z; rw [hd]; exact he z
  · intro j hj hop
    exact ⟨fun p => ha j hj hop (Fin.castAdd N p), fun l => ha j hj hop (Fin.natAdd N l)⟩

end SingletonFiniteFormula.Formula
