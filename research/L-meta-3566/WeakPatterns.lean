import PEqualNP.Outside.L_meta_1527

namespace VertexPeel.WeakPatterns

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1527 (step step_len step_lt step_last)
attribute [local instance] gateOpDecEq

/-- Counts every actual AND, including empty or unary gates. -/
def andCount (C : Circuit) : ℕ := (C.gates.filter fun g => decide (g.op = .and)).length

private def first (g : Gate) (x : List Bool) := x.getD (g.inputs.headD 0) false

private def bits : List Gate → List Bool → List Bool
  | [], _ => []
  | g::gs, x => if g.op = .and then first g x :: bits gs (step x g) else bits gs (step x g)

private theorem bitLength (gs : List Gate) (x : List Bool) :
    (bits gs x).length = (gs.filter fun g => decide (g.op = .and)).length := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih => by_cases h : g.op = .and <;> simp [bits,h,ih]

private abbrev Supported (x y z : List Bool) :=
  ∀ i, z.getD i false = true → x.getD i false = true ∨ y.getD i false = true

private theorem gate_supported (g : Gate) (x y z : List Bool) (support : Supported x y z)
    (ok : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (same : g.op = .and → first g x = first g y) :
    g.op.eval (g.inputs.map fun i => z.getD i false) = true →
      g.op.eval (g.inputs.map fun i => x.getD i false) = true ∨
      g.op.eval (g.inputs.map fun i => y.getD i false) = true := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨hop,size⟩ := ok
  change op = .and ∨ op = .or at hop
  change ins.length ≤ 2 at size
  cases ins with
  | nil => rcases hop with rfl|rfl <;> simp [GateOp.eval]
  | cons a rest =>
    cases rest with
    | nil => rcases hop with rfl|rfl <;> simpa [GateOp.eval] using support a
    | cons b tail =>
      change tail.length + 1 + 1 ≤ 2 at size
      have := List.length_eq_zero_iff.mp (by omega : tail.length = 0)
      subst tail
      rcases hop with rfl|rfl
      · have eq := same rfl
        change x.getD a false = y.getD a false at eq
        simp only [List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,
          Bool.and_true,Bool.and_eq_true, id_eq]
        rintro ⟨za,zb⟩
        have xa : x.getD a false = true := (support a za).elim id (fun h => eq.trans h)
        exact (support b zb).imp (fun xb => ⟨xa,xb⟩) (fun yb => ⟨eq.symm.trans xa,yb⟩)
      · simp only [List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,
          Bool.or_false,Bool.or_eq_true,id_eq]
        intro h
        rcases h with ha|hb
        · exact (support a ha).imp Or.inl Or.inl
        · exact (support b hb).imp Or.inr Or.inr

private theorem step_supported (g : Gate) (x y z : List Bool)
    (lx : x.length = z.length) (ly : y.length = z.length) (support : Supported x y z)
    (ok : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (same : g.op = .and → first g x = first g y) :
    Supported (step x g) (step y g) (step z g) := by
  intro i hot
  by_cases eq : i = z.length
  · rw [step_last _ _ _ eq] at hot
    rw [step_last _ _ _ (eq.trans lx.symm),step_last _ _ _ (eq.trans ly.symm)]
    exact gate_supported g x y z support ok same hot
  by_cases lt : i < z.length
  · rw [step_lt _ _ _ lt] at hot
    rw [step_lt _ _ _ (lx ▸ lt),step_lt _ _ _ (ly ▸ lt)]
    exact support i hot
  · rw [List.getD_eq_default _ _ (by rw [step_len]; omega)] at hot
    contradiction

/-- Prefix semantics ensure that even forward and out-of-range operands receive
their actual default values before the current gate appends its output. -/
private theorem propagate (gs : List Gate)
    (ok : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (x y z : List Bool) (lx : x.length = z.length) (ly : y.length = z.length)
    (support : Supported x y z) (same : bits gs x = bits gs y) :
    Supported (gs.foldl step x) (gs.foldl step y) (gs.foldl step z) := by
  induction gs generalizing x y z with
  | nil => exact support
  | cons g gs ih =>
    have tail : bits gs (step x g) = bits gs (step y g) := by
      by_cases h : g.op = .and
      · exact (List.cons.inj (by simpa [bits,h] using same)).2
      · simpa [bits,h] using same
    have head : g.op = .and → first g x = first g y := by
      intro h
      exact (List.cons.inj (by simpa [bits,h] using same)).1
    exact ih (fun a ha => ok a (by simp [ha])) (step x g) (step y g) (step z g)
      (by simp [step_len,lx]) (by simp [step_len,ly])
      (step_supported g x y z lx ly support (ok g (by simp)) head) tail

private def record {n : ℕ} (C : Circuit) (x : Fin n → Bool) : Fin (andCount C) → Bool :=
  fun i => (bits C.gates (List.ofFn x))[i.val]'(by rw [bitLength]; exact i.isLt)

private theorem separate {n : ℕ} (C : Circuit) (mono : Monotone2 C) {x y z : Fin n → Bool}
    (sub : ∀ i, z i = true → x i = true ∨ y i = true)
    (agree : record C x = record C y) (w : ℕ)
    (on : (C.wires (List.ofFn z)).getD w false = true) :
    (C.wires (List.ofFn x)).getD w false = true ∨ (C.wires (List.ofFn y)).getD w false = true := by
  have same : bits C.gates (List.ofFn x) = bits C.gates (List.ofFn y) := by
    apply List.ext_getElem (by simp [bitLength])
    intro i hx hy
    exact congrFun agree ⟨i,by simpa [bitLength,andCount] using hx⟩
  have raw : Supported (List.ofFn x) (List.ofFn y) (List.ofFn z) := by
    intro i isTrue
    by_cases h : i < n
    · simpa [List.getD,List.getElem?_ofFn,h] using sub ⟨i,h⟩ (by simpa [List.getD,List.getElem?_ofFn,h] using isTrue)
    · simp [List.getD,h] at isTrue
  have ok : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using mono g hg
  exact propagate C.gates ok _ _ _ (by simp) (by simp) raw same w on

/-- Any finite set of pairwise union-separable negative tests has cardinality
at most two to the number of AND gates in an arbitrary fan-in-at-most-two
monotone circuit. The output and gate operands need not be valid references. -/
theorem pattern_bound_set {n : ℕ} {ι : Type*} (C : Circuit) (mono : Monotone2 C)
    (U : Finset ι) (test : ι → Fin n → Bool)
    (off : ∀ i ∈ U, circuitFun n C (test i) = false)
    (sep : ∀ i ∈ U, ∀ j ∈ U, i ≠ j → ∃ z, circuitFun n C z = true ∧
        ∀ v, z v = true → test i v = true ∨ test j v = true) :
    U.card ≤ 2 ^ andCount C := by
  classical
  have h := Finset.card_le_card_of_injOn (s := U) (t := (Finset.univ : Finset (Fin (andCount C) → Bool)))
    (fun i => record C (test i)) (fun _ _ => Finset.mem_univ _) (by
      intro i hi j hj agree
      by_contra ne
      obtain ⟨z,positive,sub⟩ := sep i hi j hj ne
      have h := separate C mono sub agree C.output positive
      change circuitFun n C (test i) = true ∨ circuitFun n C (test j) = true at h
      simp [off i hi,off j hj] at h)
  simpa [Fintype.card_fun] using h

theorem pattern_bound {n k : ℕ} (C : Circuit) (mono : Monotone2 C) (test : Fin k → Fin n → Bool)
    (off : ∀ i, circuitFun n C (test i) = false)
    (sep : ∀ i j, i ≠ j → ∃ z, circuitFun n C z = true ∧
        ∀ v, z v = true → test i v = true ∨ test j v = true) :
    k ≤ 2 ^ andCount C := by
  simpa using pattern_bound_set C mono Finset.univ test (fun i _ => off i) (fun i _ j _ => sep i j)

#print axioms pattern_bound
end VertexPeel.WeakPatterns
