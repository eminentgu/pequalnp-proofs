import ResidualGraphs
import PendantCross

namespace VertexPeel.CoverFourResidual
open PEqualNP.ReadTwo PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover VertexPeel.ZeroFold VertexPeel.SideReaders

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Before any wire from B has been read, the remaining wires are monotone in the
    complementary input coordinates regardless of the values on B. -/
theorem prefix_mono {n : ℕ} (C : Circuit) (ao : IsAO2 n C)
    (B : Finset ℕ) (r : ℕ) (limit : r ≤ C.gates.length)
    (skip : ∀ i (hi : i < C.gates.length), i < r → ∀ k ∈ C.gates[i].inputs, k ∉ B)
    (x y : Fin n → Bool) (incl : ∀ v : Fin n, v.val ∉ B → x v = true → y v = true) :
    ∀ j < n+r, j ∉ B → wval C x j = true → wval C y j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro jr outside on
    by_cases raw : j < n
    · let v : Fin n := ⟨j,raw⟩
      exact (wval_in C y v).trans (incl v outside ((wval_in C x v).symm.trans on))
    obtain ⟨i,rfl⟩ : ∃ i, j = n+i := ⟨j-n,by omega⟩
    have hi : i < C.gates.length := by omega
    obtain ⟨a,b,ports,ha,hb,op⟩ := two n C ao i hi
    have transfer (t : ℕ) (ht : t ∈ C.gates[i].inputs) (back : t < n+i) :
        wval C x t = true → wval C y t = true :=
      ih t back (by omega) (skip i hi (by omega) t ht)
    have ta := transfer a (by simp [ports]) ha
    have tb := transfer b (by simp [ports]) hb
    rw [wval_gate C x i a b hi ports ha hb] at on
    rw [wval_gate C y i a b hi ports ha hb]
    rcases op with h | h <;> simp [h,GateOp.eval] at on ⊢ <;> tauto

theorem on_of_or {n : ℕ} (C : Circuit) (ao : IsAO2 n C) (r : ℕ)
    (hr : r < C.gates.length) (op : C.gates[r].op = .or)
    (t : ℕ) (read : t ∈ C.gates[r].inputs) (x : Fin n → Bool) (on : wval C x t = true) :
    wval C x (n+r) = true := by
  obtain ⟨a,b,ports,ha,hb,_⟩ := two n C ao r hr
  rw [wval_gate C x r a b hr ports ha hb,op]
  have mem : t=a ∨ t=b := by simpa [ports] using read
  rcases mem with rfl | rfl <;> simp [GateOp.eval,on]

abbrev subdivisionSide : Finset ℕ := {4,5,6,7,8}

private def base (x : Fin 9 → Bool) (v : Fin 9) : Bool :=
  decide (v.val < 4 ∧ v ≠ (if x 0 then 1 else 0))

/-- In row 15, the partner wire of the first private subdivision OR can be true
    only when both endpoints of the unique unsubdivided edge are true. -/
theorem firstPartner {C : Circuit} (ao : IsAO2 9 C)
    (correct : circuitFun 9 C = graphFun (graph 15) ∅)
    (r : ℕ) (hr : r < C.gates.length) (op : C.gates[r].op = .or)
    (b : Fin 9) (inSide : b.val ∈ subdivisionSide)
    (readB : b.val ∈ C.gates[r].inputs)
    (only : ∀ i (hi : i < C.gates.length), b.val ∈ C.gates[i].inputs → i = r)
    (skip : ∀ i (hi : i < C.gates.length), i < r → ∀ t ∈ C.gates[i].inputs, t ∉ subdivisionSide)
    (j : ℕ) (read : j ∈ C.gates[r].inputs) (back : j < 9+r) (outside : j ∉ subdivisionSide)
    (x : Fin 9 → Bool) (missing : ¬ (x 0 = true ∧ x 1 = true)) : wval C x j = false := by
  let y := base x
  let z := Function.update y b true
  have incl : ∀ v : Fin 9, v.val ∉ subdivisionSide → x v = true → y v = true := by
    intro v hv hx
    fin_cases v <;> simp_all [y,base,subdivisionSide] <;> split <;> simp_all
  have neg : graphFun (graph 15) ∅ y = false := by
    have all : ∀ k : Bool, graphFun (graph 15) ∅ (fun v : Fin 9 =>
        decide (v.val < 4 ∧ v ≠ (if k then 1 else 0))) = false := by decide +kernel
    exact all (x 0)
  have pos : graphFun (graph 15) ∅ z = true := by
    have all : ∀ (k : Bool) (b : Fin 9), b.val ∈ subdivisionSide →
        graphFun (graph 15) ∅ (Function.update (fun v : Fin 9 =>
          decide (v.val < 4 ∧ v ≠ (if k then 1 else 0))) b true) = true := by decide +kernel
    exact all (x 0) b inSide
  have different : wval C y C.output ≠ wval C z C.output := by
    change circuitFun 9 C y ≠ circuitFun 9 C z
    rw [correct,neg,pos]; decide
  obtain ⟨i,hi,_,diff,t,ht,reads⟩ := PendantCross.crosses_diff C ao {b.val} y z (by
    intro a ha
    exact (Function.update_of_ne (fun e => ha (by simp [e])) _ _).symm) different
    (by simpa using no_raw_output (graph 15) correct b)
  obtain rfl : t = b.val := Finset.mem_singleton.mp ht
  have same : i = r := only i hi reads
  subst i
  apply Bool.eq_false_iff.mpr
  intro h
  have sy := prefix_mono C ao subdivisionSide r hr.le skip x y incl j back outside h
  have sz : wval C z b.val = true := (wval_in C z b).trans (Function.update_self ..)
  exact diff ((on_of_or C ao r hr op j read y sy).trans (on_of_or C ao r hr op b.val readB z sz).symm)

/-- A partner that vanishes whenever the two distinguished bits are not both on
    cannot be a raw input. Each raw input is true on its singleton assignment. -/
theorem internal_of_vanishes {C : Circuit} {j r : ℕ} (back : j < 9+r)
    (off : ∀ x : Fin 9 → Bool, ¬ (x 0 = true ∧ x 1 = true) → wval C x j = false) :
    ∃ k < r, j = 9+k := by
  by_cases raw : j < 9
  · let v : Fin 9 := ⟨j,raw⟩
    let x : Fin 9 → Bool := fun t => decide (t = v)
    have missing : ¬ (x 0 = true ∧ x 1 = true) := by
      simp [x]
      omega
    have yes : wval C x j = true := (wval_in C x v).trans (by simp [x])
    exact (Bool.false_ne_true ((off x missing).symm.trans yes)).elim
  · exact ⟨j-9,by omega,by omega⟩

end VertexPeel.CoverFourResidual
#print axioms VertexPeel.CoverFourResidual.firstPartner
