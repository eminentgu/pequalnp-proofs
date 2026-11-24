import FormulaCircuit

namespace SingletonFiniteFormula.Formula
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

def rename {α β : Type} (σ : α → β) : Formula α → Formula β
  | .atom x => .atom (σ x)
  | .node op a b => .node op (a.rename σ) (b.rename σ)

theorem rename_gates {α β : Type} (σ : α → β) (f : Formula α) :
    (f.rename σ).gates = f.gates := by
  induction f with
  | atom => rfl
  | node op a b ia ib => simp [rename, gates, ia, ib]

theorem rename_eval {α β : Type} (σ : α → β) (f : Formula α) (z : β → Bool) :
    (f.rename σ).eval z = f.eval (fun x => z (σ x)) := by
  induction f with
  | atom => rfl
  | node op a b ia ib => simp [rename, eval, ia, ib]

theorem eval_zero {α : Type} (f : Formula α) : f.eval (fun _ => false) = false := by
  induction f with
  | atom => rfl
  | node op a b ia ib => cases op <;> simp [eval, Op.apply, ia, ib]

theorem rename_root {k m : Nat} (σ : Fin k → Fin m) (f : Formula (Fin k)) :
    (f.rename σ).rootOp = f.rootOp := by cases f <;> rfl

theorem rename_trace {k m : Nat} (σ : Fin k → Fin m) (f : Formula (Fin k)) :
    (f.rename σ).trace = f.trace.map (rename σ) := by
  induction f with
  | atom => rfl
  | node op a b ia ib => simp [rename, trace, ia, ib]

def AllAndClean (n : Nat) (P : Circuit) : Prop :=
  ∀ j < P.gates.length, (gateAt P j).op = .and →
    ∀ i : Fin n, (P.wires (List.ofFn (single i))).getD (n+j) false = false

def prefixValue {n : Nat} (P : Circuit) (z : Fin n → Bool)
    (w : Fin (n + P.size)) : Bool := (P.wires (List.ofFn z)).getD w false

/-- On every original singleton, at most one of the formula cone's distinct ports is high. -/
def SeparatedPorts {n k : Nat} (P : Circuit) (σ : Fin k → Fin (n + P.size)) : Prop :=
  ∀ i : Fin n, (∀ p, prefixValue P (single i) (σ p) = false) ∨
    ∃ a : Fin k, (fun p => prefixValue P (single i) (σ p)) = single a

/-- A directly checkable equivalent formulation of the boundary hypothesis. -/
theorem separated_iff {n k : Nat} (P : Circuit) (σ : Fin k → Fin (n+P.size)) :
    SeparatedPorts P σ ↔
      ∀ (i : Fin n) (a b : Fin k), prefixValue P (single i) (σ a) = true →
        prefixValue P (single i) (σ b) = true → a = b := by
  classical
  constructor
  · intro h i a b ha hb
    rcases h i with off|⟨c,hc⟩
    · have := off a; simp_all
    · have aa := congrFun hc a
      have bb := congrFun hc b
      simp [ha,hb,single] at aa bb
      exact aa.trans bb.symm
  · intro h i
    by_cases hh : ∃ a, prefixValue P (single i) (σ a) = true
    · obtain ⟨a,ha⟩ := hh
      refine Or.inr ⟨a,?_⟩
      funext b
      by_cases hb : prefixValue P (single i) (σ b) = true
      · have eq := h i b a hb ha
        simp [single,eq,ha]
      · have ne : b ≠ a := by intro eq; exact hb (eq ▸ ha)
        simp [hb,single,ne]
    · exact Or.inl (fun p => by cases hh' : prefixValue P (single i) (σ p) with
                                | false => rfl
                                | true => exact (hh ⟨p,hh'⟩).elim)

def attach {n k : Nat} (P : Circuit) (σ : Fin k → Fin (n + P.size))
    (f : Formula (Fin k)) : Circuit :=
  ⟨P.gates ++ (f.rename σ).code (n+P.size), (f.rename σ).ptr (n+P.size)⟩

theorem run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih, step]; omega

theorem prefix_length {n : Nat} (P : Circuit) (z : Fin n → Bool) :
    (P.wires (List.ofFn z)).length = n + P.size := by
  change (P.gates.foldl step (List.ofFn z)).length = _
  rw [run_length]
  simp [Circuit.size]

theorem attach_wires {n k : Nat} (P : Circuit) (σ : Fin k → Fin (n+P.size))
    (f : Formula (Fin k)) (z : Fin n → Bool) :
    (attach P σ f).wires (List.ofFn z) = P.wires (List.ofFn z) ++
      (f.rename σ).trace.map (eval (prefixValue P z)) := by
  let w := P.wires (List.ofFn z)
  have hl : w.length = n + P.size := prefix_length P z
  have h := (code_eval (f.rename σ) (prefixValue P z) w (by omega) (fun _ => rfl)).1
  rw [hl] at h
  change (P.gates ++ _).foldl step (List.ofFn z) = _
  rw [List.foldl_append]
  exact h

theorem attach_eval {n k : Nat} (P : Circuit) (σ : Fin k → Fin (n+P.size))
    (f : Formula (Fin k)) (z : Fin n → Bool) :
    circuitFun n (attach P σ f) z = f.eval (fun p => prefixValue P z (σ p)) := by
  let w := P.wires (List.ofFn z)
  have hl : w.length = n + P.size := prefix_length P z
  have h := (code_eval (f.rename σ) (prefixValue P z) w (by omega) (fun _ => rfl)).2
  rw [hl] at h
  change ((attach P σ f).wires (List.ofFn z)).getD ((f.rename σ).ptr (n+P.size)) false = _
  rw [attach_wires]
  exact h.trans (rename_eval σ f _)

theorem attach_size {n k : Nat} (P : Circuit) (σ : Fin k → Fin (n+P.size))
    (f : Formula (Fin k)) : (attach P σ f).size = P.size + f.gates := by
  change (P.gates ++ (f.rename σ).code (n+P.size)).length = P.gates.length + f.gates
  rw [List.length_append,code_length,rename_gates]

theorem attach_mono {n k : Nat} (P : Circuit) (σ : Fin k → Fin (n+P.size))
    (f : Formula (Fin k)) (hm : Monotone2 P) : Monotone2 (attach P σ f) := by
  intro g hg
  rcases List.mem_append.mp hg with hg|hg
  · exact hm g hg
  · exact code_mono _ _ _ hg

theorem attach_back {n k : Nat} (P : Circuit) (σ : Fin k → Fin (n+P.size))
    (f : Formula (Fin k)) (hr : ReadsBack n P) : ReadsBack n (attach P σ f) := by
  have left : Back n P.gates := by
    intro j hj i hi
    apply hr j hj i
    simpa [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using hi
  have all := back_append left (code_back (f.rename σ) (n+P.size) le_rfl)
  intro j hj i hi
  apply all j hj i
  change i ∈ (attach P σ f).gates[j].inputs
  simpa [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using hi

theorem attach_clean {n k : Nat} (P : Circuit) (σ : Fin k → Fin (n+P.size))
    (f : Formula (Fin k)) (hf : f.Clean) (hp : AllAndClean n P) (hs : SeparatedPorts P σ) :
    AllAndClean n (attach P σ f) := by
  intro j hj hop i
  let t := f.rename σ
  let z := single i
  let w := P.wires (List.ofFn z)
  have hw : w.length = n + P.size := prefix_length P z
  have hlen : j < P.gates.length + (t.code (n+P.size)).length := by
    simpa [attach, t] using hj
  have hgate : ((P.gates ++ t.code (n+P.size))[j]'(by simpa using hlen)).op = .and := by
    change (attach P σ f).gates[j].op = .and
    simpa [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using hop
  rw [attach_wires]
  by_cases h : j < P.gates.length
  · rw [List.getElem_append_left h] at hgate
    have hor : (gateAt P j).op = .and := by
      simpa [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h] using hgate
    change (w ++ _).getD (n+j) false = _
    rw [getD_left _ _ _ _ (by rw [hw]; exact Nat.add_lt_add_left h n)]
    exact hp j h hor i
  · let q := j-P.gates.length
    have hq : q < (t.code (n+P.size)).length := by dsimp [q]; omega
    have hjq : j = P.size + q := by change j = P.gates.length + (j-P.gates.length); omega
    rw [List.getElem_append_right (by omega : P.gates.length ≤ j)] at hgate
    change (t.code (n+P.size))[q].op = .and at hgate
    have htq : q < t.trace.length := by simpa [code_length,trace_length] using hq
    have hop' := congrArg (fun (xs : List GateOp) => xs[q]?) (trace_op t (n+P.size))
    simp only [List.getElem?_map, List.getElem?_eq_getElem hq, List.getElem?_eq_getElem htq,
      Option.map_some, Option.some.injEq] at hop'
    have hor : t.trace[q].rootOp = .and := hop' ▸ hgate
    have mem : t.trace[q] ∈ f.trace.map (rename σ) := by
      rw [← rename_trace]; exact List.getElem_mem htq
    obtain ⟨a,ha,he⟩ := List.mem_map.mp mem
    have har : a.rootOp = .and := by rw [← he,rename_root] at hor; exact hor
    have val : t.trace[q].eval (prefixValue P z) = false := by
      rw [← he,rename_eval]
      rcases hs i with off|⟨c,one⟩
      · have ez : (fun p => prefixValue P z (σ p)) = fun _ => false := funext off
        rw [ez,eval_zero]
      · change (fun p => prefixValue P z (σ p)) = single c at one
        rw [one]; exact clean_trace f hf a ha har c
    change (w ++ t.trace.map (eval (prefixValue P z))).getD (n+j) false = false
    have hj' : n+j = w.length+q := by omega
    rw [hj',getD_right]
    simpa [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem htq] using val

/-- A shared native-circuit prefix can feed a formula cone at arbitrarily many leaves.
If its exposed ports are separated on raw singleton inputs, the entire composite
has an equivalent singleton-clean native circuit at no greater total size. -/
theorem normalize_shared_cone {n k : Nat} (P : Circuit) (σ : Fin k → Fin (n+P.size))
    (f : Formula (Fin k)) (hm : Monotone2 P) (hr : ReadsBack n P)
    (hp : AllAndClean n P) (hs : SeparatedPorts P σ) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size ≤ P.size + f.gates ∧
      (∀ z, circuitFun n D z = circuitFun n (attach P σ f) z) ∧ AllAndClean n D := by
  obtain ⟨g,hg,hsize,he⟩ := normalize f
  refine ⟨attach P σ g, attach_mono P σ g hm, attach_back P σ g hr, ?_, ?_,
    attach_clean P σ g hg hp hs⟩
  · rw [attach_size]; omega
  · intro z; rw [attach_eval,attach_eval,he]

end SingletonFiniteFormula.Formula
