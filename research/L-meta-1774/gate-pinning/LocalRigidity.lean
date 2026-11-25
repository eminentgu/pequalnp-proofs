import Sensitive
import SharedMask

namespace PEqualNP.Research.GatePinning.LocalRigidity

open CircuitLowerBounds EdgeOwnership MetaComplexity MetaComplexity.NestedCover
open SharedMask (G C)

private def bound (i : Nat) : Fin 9 := ⟨min i 8,by omega⟩

private def inputs (x : Fin 6 → Bool) : List Bool :=
  [x 0,x 1,x 2,x 3,x 4,x 5,x 0 || x 2,x 1 || x 3]

private def eval (x : Fin 6 → Bool) (g : Gate) : Bool :=
  let j := g.op.eval (g.inputs.map fun i => (inputs x).getD i false)
  (x 0 && (j || x 4)) || (x 3 && (j || x 5))

private theorem computes (x : Fin 6 → Bool) (g : Gate) :
    circuitFun 6 (replace C 2 g) x = eval x g := by
  simp [circuitFun,Circuit.eval,Circuit.wires,replace,C,eval,inputs,List.ofFn_succ,GateOp.eval]

private theorem read_bound (i : Nat) (x : Fin 6 → Bool) :
    (inputs x).getD (bound i).val false = (inputs x).getD i false := by
  by_cases hi : i<8
  · simp [bound,Nat.min_eq_left (by omega : i≤8)]
  · have hi' : 8 ≤ i := by omega
    have last : (inputs x)[8]? = none := List.getElem?_eq_none (by simp [inputs])
    have missing : (inputs x)[i]? = none := List.getElem?_eq_none (by simpa [inputs] using hi')
    simp [bound,Nat.min_eq_right hi',List.getD_eq_getElem?_getD,last,missing]

private theorem finite_bins : ∀ (mode : Bool) (a b : Fin 9),
    (∀ x : Fin 6 → Bool, eval x ⟨if mode then .and else .or,[a,b]⟩ = graphFun G ∅ x) →
    mode = true ∧ ((a=6 ∧ b=7) ∨ (a=7 ∧ b=6)) := by
  decide +kernel

private theorem bounded_eq {i : Nat} {q : Fin 9} (qsmall : q.val < 8)
    (h : bound i = q) : i = q.val := by
  have := congrArg Fin.val h
  simp only [bound] at this
  omega

/-- Even with all monotone arities up to two and the default-false reads allowed, the
only gate that can occupy site 2 and preserve the function is the original binary AND
in one of its two input orders. -/
theorem only_gate (g : Gate) (allowed : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp))
    (arity : g.inputs.length ≤ 2) (eq : circuitFun 6 (replace C 2 g) = graphFun G ∅) :
    g = ⟨.and,[6,7]⟩ ∨ g = ⟨.and,[7,6]⟩ := by
  rcases g with ⟨op,ws⟩
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at allowed
  obtain ⟨mode, rfl⟩ : ∃ mode : Bool, op = if mode then GateOp.and else .or := by
    rcases allowed with rfl | rfl
    · exact ⟨true,rfl⟩
    · exact ⟨false,rfl⟩
  have correct (x : Fin 6 → Bool) := (computes x ⟨if mode then .and else .or,ws⟩).symm.trans (congrFun eq x)
  cases ws with
  | nil =>
    obtain ⟨x,bad⟩ := SharedMask.noConstantReplacement (2 : Fin 8) mode
    exact False.elim (bad ((congrFun eq x).trans (congrFun SharedMask.computes.1 x).symm))
  | cons i tail =>
    cases tail with
    | nil =>
      have bad := finite_bins mode (bound i) (bound i) (fun x => by
        cases mode <;>
          simpa [eval,GateOp.eval,-List.getD_eq_getElem?_getD,read_bound] using correct x)
      rcases bad.2 with h|h <;> have := congrArg Fin.val (h.1.symm.trans h.2) <;> contradiction
    | cons j tail =>
      cases tail with
      | nil =>
        have ok := finite_bins mode (bound i) (bound j) (fun x => by
          simpa [eval,-List.getD_eq_getElem?_getD,read_bound] using correct x)
        obtain ⟨rfl,forward | backward⟩ := ok
        · exact Or.inl (by rw [bounded_eq (by decide) forward.1,bounded_eq (by decide) forward.2]; rfl)
        · exact Or.inr (by rw [bounded_eq (by decide) backward.1,bounded_eq (by decide) backward.2]; rfl)
      | cons j' tail => simp at arity


/-- The three critical unordered edges form the path 1--0--3--2. -/
theorem critical_edges (a b : Fin 6) : needed G C 2 a b ↔
    s(a,b) = s((0 : Fin 6),1) ∨ s(a,b) = s((0 : Fin 6),3) ∨ s(a,b) = s((2 : Fin 6),3) := by
  revert a b
  unfold needed
  decide +kernel

/-- The site must stay off on the lone vertices 0 and 3, where opposite operands turn on. -/
theorem forbidden_rows : forbidden G C 2 (pairInput (0 : Fin 6) 0) ∧
    forbidden G C 2 (pairInput (3 : Fin 6) 3) := by
  unfold forbidden
  decide +kernel

end PEqualNP.Research.GatePinning.LocalRigidity
