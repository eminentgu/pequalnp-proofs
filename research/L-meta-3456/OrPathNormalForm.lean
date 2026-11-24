import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Local3456

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

/-- A raw input reaches a wire by a path whose internal gates are all OR gates. -/
inductive OrPath {n : ℕ} (C : Circuit) (k : Fin n) : ℕ → Prop where
  | input : OrPath C k k.val
  | gate {j p : ℕ} (valid : j < C.gates.length) (isOr : (gateAt C j).op = .or)
      (pin : p ∈ (gateAt C j).inputs) : OrPath C k p → OrPath C k (n + j)

def singleWire {n : ℕ} (C : Circuit) (k : Fin n) (i : ℕ) : Bool :=
  (C.wires (List.ofFn (fun q : Fin n => decide (q = k)))).getD i false

def SingletonClean (n : ℕ) (C : Circuit) : Prop :=
  ∀ j < C.gates.length, (gateAt C j).op = .and → ∀ k : Fin n, singleWire C k (n+j) = false

/-- At each AND, every raw input fails to reach at least one operand via OR gates alone. -/
def SeparatedOrPaths (n : ℕ) (C : Circuit) : Prop :=
  ∀ j < C.gates.length, (gateAt C j).op = .and → ∀ k : Fin n,
    ∃ p ∈ (gateAt C j).inputs, ¬ OrPath C k p

private def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
private def unusedGate : Gate := ⟨.or, []⟩

private theorem lengthRun (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    change (gs.foldl step (step w g)).length = _
    rw [ih (step w g)]
    simp [step]
    omega

private theorem oldRead (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (gs.foldl step (step w g)).getD i false = _
    rw [ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ h

private theorem gateRule (gs : List Gate) (w : List Bool) (j : ℕ) (valid : j < gs.length)
    (back : ∀ t < gs.length, ∀ i ∈ (gs.getD t unusedGate).inputs, i < w.length + t) :
    (gs.foldl step w).getD (w.length+j) false =
      (gs.getD j unusedGate).op.eval ((gs.getD j unusedGate).inputs.map fun i => (gs.foldl step w).getD i false) := by
  induction gs generalizing w j with
  | nil => simp at valid
  | cons g gs ih =>
    cases j with
    | zero =>
      change (gs.foldl step (step w g)).getD (w.length+0) false =
        g.op.eval (g.inputs.map fun i => ((g::gs).foldl step w).getD i false)
      rw [Nat.add_zero, oldRead gs (step w g) w.length (by simp [step])]
      have lastRead : (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
        unfold step
        rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)]
        simp
      rw [lastRead]
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro i hi
      exact (oldRead (g::gs) w i (by simpa using back 0 (by simp) i hi)).symm
    | succ j =>
      have b : ∀ t < gs.length, ∀ i ∈ (gs.getD t unusedGate).inputs, i < (step w g).length + t := by
        intro t ht i hi
        have hb := back (t+1) (by simp [ht]) i (by simpa using hi)
        simp [step] at ⊢
        omega
      have r := ih (step w g) j (by simpa using valid) b
      have eqidx : w.length + (j+1) = (step w g).length + j := by simp [step]; omega
      simpa only [List.foldl_cons, List.getD_cons_succ, eqidx] using r

private theorem inputRule {n : ℕ} (C : Circuit) (k i : Fin n) :
    singleWire C k i.val = decide (i = k) := by
  let w := List.ofFn (fun q : Fin n => decide (q = k))
  change (C.gates.foldl step w).getD i.val false = _
  rw [oldRead _ _ _ (by simp [w])]
  simp [w,List.getD_eq_getElem?_getD]

private theorem outRule {n : ℕ} (C : Circuit) (back : ReadsBack n C) (k : Fin n) (j : ℕ)
    (hj : j < C.gates.length) :
    singleWire C k (n+j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (singleWire C k)) := by
  let w := List.ofFn (fun q : Fin n => decide (q = k))
  have b : ∀ t < C.gates.length, ∀ i ∈ (C.gates.getD t unusedGate).inputs, i < w.length + t := by
    intro t ht i hi
    simpa [w] using back t ht i hi
  change (C.gates.foldl step w).getD (n+j) false =
    (C.gates.getD j unusedGate).op.eval ((C.gates.getD j unusedGate).inputs.map (fun i => (C.gates.foldl step w).getD i false))
  have len : w.length = n := by simp [w]
  simpa only [len] using gateRule C.gates w j hj b

private theorem andTrue (g : Gate) (f : ℕ → Bool) (op : g.op = .and) :
    g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true := by
  simp [op,GateOp.eval]

private theorem orTrue (g : Gate) (f : ℕ → Bool) (op : g.op = .or) :
    g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true := by
  simp [op,GateOp.eval,List.any_eq_true]

theorem orPath_implies_true {n : ℕ} (C : Circuit) (back : ReadsBack n C) (k : Fin n) {p : ℕ}
    (path : OrPath C k p) : singleWire C k p = true := by
  induction path with
  | input => simp [inputRule]
  | @gate j p hj op pin path prev =>
    rw [outRule C back k j hj]
    exact (orTrue _ _ op).mpr ⟨p,pin,prev⟩

/-- The OR-path test finds every obstruction, including nullary and unary ANDs. -/
theorem singletonClean_iff_separated (n : ℕ) (C : Circuit) (mono : Monotone2 C) (back : ReadsBack n C) :
    SingletonClean n C ↔ SeparatedOrPaths n C := by
  classical
  constructor
  · intro clean j hj op k
    by_contra! all
    have yes := (andTrue _ _ op).mpr (fun p hp => orPath_implies_true C back k (all p hp))
    rw [← outRule C back k j hj,clean j hj op k] at yes
    contradiction
  · intro sep
    have reflected (k : Fin n) (i : ℕ) (hi : singleWire C k i = true) : OrPath C k i := by
      induction i using Nat.strong_induction_on with
      | ind i ih =>
        by_cases raw : i < n
        · let u : Fin n := ⟨i,raw⟩
          have eq : u = k := of_decide_eq_true ((inputRule C k u).symm.trans hi)
          have idx : i = k.val := congrArg Fin.val eq
          rw [idx]
          exact .input
        · let d := i-n
          have idx : i = n+d := by dsimp [d]; omega
          have hd : d < C.gates.length := by
            by_contra! outside
            let w := List.ofFn (fun q : Fin n => decide (q = k))
            change (C.gates.foldl step w).getD i false = true at hi
            have bound : (C.gates.foldl step w).length ≤ i := by rw [lengthRun]; simp [w]; omega
            rw [List.getD_eq_default _ _ bound] at hi
            contradiction
          have gm : gateAt C d ∈ C.gates := by
            unfold gateAt
            rw [List.getD_eq_getElem _ _ hd]
            exact List.getElem_mem hd
          have op : (gateAt C d).op = .and ∨ (gateAt C d).op = .or := by
            simpa using (mono _ gm).1
          rw [idx,outRule C back k d hd] at hi
          rcases op with ha | ho
          · obtain ⟨p,hp,no⟩ := sep d hd ha k
            exact (no (ih p (by have := back d hd p hp; omega) ((andTrue _ _ ha).mp hi p hp))).elim
          · obtain ⟨p,hp,hptrue⟩ := (orTrue _ _ ho).mp hi
            rw [idx]
            exact .gate hd ho hp (ih p (by have := back d hd p hp; omega) hptrue)
    intro j hj ha k
    cases yes : singleWire C k (n+j) with
    | false => rfl
    | true =>
      obtain ⟨p,hp,no⟩ := sep j hj ha k
      rw [outRule C back k j hj] at yes
      exact (no (reflected k p ((andTrue _ _ ha).mp yes p hp))).elim

/-- Every incidence circuit passing the path test already witnesses the requested normal form. -/
theorem incidence_normal_of_separated (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (mono : Monotone2 C) (back : ReadsBack (N+N) C)
    (computes : ∀ z : Fin (N+N) → Bool, circuitFun (N+N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (separated : SeparatedOrPaths (N+N) C) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size ≤ C.size ∧
      (∀ z : Fin (N+N) → Bool, circuitFun (N+N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D.gates.length, (gateAt D j).op = .and →
        (∀ p : Fin N, singleWire D (Fin.castAdd N p) (N+N+j) = false) ∧
        ∀ l : Fin N, singleWire D (Fin.natAdd N l) (N+N+j) = false) := by
  have clean := (singletonClean_iff_separated (N+N) C mono back).mpr separated
  exact ⟨C,mono,back,le_rfl,computes,fun j hj ha =>
    ⟨fun p => clean j hj ha (Fin.castAdd N p),fun l => clean j hj ha (Fin.natAdd N l)⟩⟩


def signal {n : ℕ} (C : Circuit) (z : Fin n → Bool) (p : ℕ) : Bool :=
  (C.wires (List.ofFn z)).getD p false

private theorem gateSignal {n : ℕ} (C : Circuit) (back : ReadsBack n C) (z : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    signal C z (n+j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (signal C z)) := by
  let w := List.ofFn z
  have b : ∀ t < C.gates.length, ∀ i ∈ (C.gates.getD t unusedGate).inputs, i < w.length + t := by
    intro t ht i hi
    simpa [w] using back t ht i hi
  change (C.gates.foldl step w).getD (n+j) false =
    (C.gates.getD j unusedGate).op.eval ((C.gates.getD j unusedGate).inputs.map (fun i => (C.gates.foldl step w).getD i false))
  have len : w.length = n := by simp [w]
  simpa only [len] using gateRule C.gates w j hj b

noncomputable def badGates (n : ℕ) (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun j => (gateAt C j).op = .and ∧
    ∃ k : Fin n, singleWire C k (n+j) = true

private theorem memBad {n : ℕ} {C : Circuit} {j : ℕ} :
    j ∈ badGates n C ↔ j < C.gates.length ∧ (gateAt C j).op = .and ∧
      ∃ k : Fin n, singleWire C k (n+j) = true := by
  classical
  simp [badGates]

/-- Preserve wire numbers and replace the selected gates by unary OR gates. -/
def copyPins (C : Circuit) (selected : Finset ℕ) (pick : ℕ → ℕ) : Circuit :=
  ⟨C.gates.mapIdx (fun j g => if j ∈ selected then ⟨.or,[pick j]⟩ else g), C.output⟩

private theorem copyAt (C : Circuit) (T : Finset ℕ) (pick : ℕ → ℕ) (j : ℕ) (hj : j < C.gates.length) :
    gateAt (copyPins C T pick) j = if j ∈ T then ⟨.or,[pick j]⟩ else gateAt C j := by
  unfold gateAt copyPins
  rw [List.getD_eq_getElem _ _ (by simp [hj]),List.getD_eq_getElem _ _ hj]
  simp only [List.getElem_mapIdx]

/-- In one pass, copy away any collection of gates whose output equals one of their own inputs.
Every wire value is preserved on every assignment; precisely the selected violations disappear. -/
theorem eliminate_pin_copies (n : ℕ) (C : Circuit) (mono : Monotone2 C) (back : ReadsBack n C)
    (T : Finset ℕ) (pick : ℕ → ℕ)
    (erasable : ∀ j ∈ T, pick j ∈ (gateAt C j).inputs ∧
      ∀ z : Fin n → Bool, signal C z (n+j) = signal C z (pick j)) :
    let D := copyPins C T pick
    Monotone2 D ∧ ReadsBack n D ∧ D.size = C.size ∧
    (∀ (z : Fin n → Bool) i, signal D z i = signal C z i) ∧ badGates n D = badGates n C \ T := by
  classical
  let D := copyPins C T pick
  have len : D.gates.length = C.gates.length := by simp [D,copyPins]
  have atD := copyAt C T pick
  have sameSize : D.size = C.size := len
  have fan : Monotone2 D := by
    intro g hg
    obtain ⟨j,hj,hg'⟩ := List.mem_iff_getElem.mp hg
    have v : j < C.gates.length := by omega
    have that : gateAt D j = g := by simpa only [gateAt,List.getD_eq_getElem _ _ hj] using hg'
    rw [← that,atD j v]
    by_cases sel : j ∈ T
    · simp [sel]
    · rw [ite_eq_right sel]
      apply mono
      unfold gateAt
      rw [List.getD_eq_getElem _ _ v]
      exact List.getElem_mem v
  have reads : ReadsBack n D := by
    intro j hj i hi
    have v : j < C.gates.length := by omega
    rw [atD j v] at hi
    by_cases sel : j ∈ T
    · simp [sel] at hi
      exact hi ▸ back j v (pick j) (erasable j sel).1
    · exact back j v i (by simpa [sel] using hi)
  have same (z : Fin n → Bool) (i : ℕ) : signal D z i = signal C z i := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      let w := List.ofFn z
      have lw : w.length = n := by simp [w]
      by_cases raw : i < n
      · change (D.gates.foldl step w).getD i false = (C.gates.foldl step w).getD i false
        rw [oldRead _ _ _ (by omega),oldRead _ _ _ (by omega)]
      by_cases past : n + C.gates.length ≤ i
      · change (D.gates.foldl step w).getD i false = (C.gates.foldl step w).getD i false
        rw [List.getD_eq_default _ _ (show (D.gates.foldl step w).length ≤ i by rw [lengthRun,lw,len]; exact past),
            List.getD_eq_default _ _ (show (C.gates.foldl step w).length ≤ i by rw [lengthRun,lw]; exact past)]
      let j := i-n
      have idx : i = n+j := by dsimp [j]; omega
      have v : j < C.gates.length := by omega
      have vd : j < D.gates.length := by omega
      have terms : (gateAt D j).inputs.map (signal D z) = (gateAt D j).inputs.map (signal C z) := by
        apply List.map_congr_left
        intro q hq
        exact ih q (by have := reads j vd q hq; omega)
      rw [idx,gateSignal D reads z j vd,terms,atD j v]
      by_cases sel : j ∈ T
      · simpa [sel,GateOp.eval] using (erasable j sel).2 z |>.symm
      · simpa [sel] using (gateSignal C back z j v).symm
  refine ⟨fan,reads,sameSize,same,?_⟩
  have atSingle (k : Fin n) (i : ℕ) : singleWire D k i = singleWire C k i := same _ _
  change badGates n D = badGates n C \ T
  have atCopy (j : ℕ) (hj : j < C.gates.length) :
      gateAt D j = if j ∈ T then ⟨.or,[pick j]⟩ else gateAt C j := atD j hj
  ext j
  by_cases v : j < C.gates.length
  · by_cases sel : j ∈ T
    · simp [memBad,atCopy j v,sel]
    · simp [memBad,len,atCopy j v,sel,atSingle]
  · simp [memBad,len,v]

/-- A gate with comparable operands is erasable by copying the smaller one.
The comparison is on all assignments and never assumes the remainder of the circuit is read-once. -/
theorem erasable_of_dominance {n : ℕ} (C : Circuit) (back : ReadsBack n C) (j a b : ℕ)
    (valid : j < C.gates.length) (op : (gateAt C j).op = .and) (pins : (gateAt C j).inputs = [a,b])
    (dominates : ∀ z : Fin n → Bool, signal C z a = true → signal C z b = true) :
    a ∈ (gateAt C j).inputs ∧ ∀ z : Fin n → Bool, signal C z (n+j) = signal C z a := by
  refine ⟨by simp [pins],?_⟩
  intro z
  rw [gateSignal C back z j valid,op,pins]
  cases ha : signal C z a with
  | false => simp [GateOp.eval,ha]
  | true => simp [GateOp.eval,ha,dominates z ha]

/-- OR-only propagation between two arbitrary wires supplies an assignment-independent dominance proof. -/
inductive OrRoute {n : ℕ} (C : Circuit) (source : ℕ) : ℕ → Prop where
  | refl : OrRoute C source source
  | next {j i : ℕ} (valid : j < C.gates.length) (isOr : (gateAt C j).op = .or)
      (pin : i ∈ (gateAt C j).inputs) : OrRoute C source i → OrRoute C source (n+j)

theorem orRoute_dominates {n : ℕ} (C : Circuit) (back : ReadsBack n C) {a b : ℕ}
    (path : OrRoute (n:=n) C a b) (z : Fin n → Bool) (ha : signal C z a = true) : signal C z b = true := by
  induction path with
  | refl => exact ha
  | @next j i hj hop pin prev ih =>
    rw [gateSignal C back z j hj]
    exact (orTrue _ _ hop).mpr ⟨i,pin,ih⟩

/-- An entire circuit can be normalized whenever each singleton-firing AND can copy one input. -/
theorem normal_of_erasable (n : ℕ) (C : Circuit) (mono : Monotone2 C) (back : ReadsBack n C)
    (can : ∀ j ∈ badGates n C, ∃ p ∈ (gateAt C j).inputs,
      ∀ z : Fin n → Bool, signal C z (n+j) = signal C z p) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size = C.size ∧
      (∀ z : Fin n → Bool, circuitFun n D z = circuitFun n C z) ∧ SingletonClean n D := by
  classical
  let T := badGates n C
  let pick (j : ℕ) := if h : j ∈ T then (can j h).choose else 0
  have works (j : ℕ) (hj : j ∈ T) := (can j hj).choose_spec
  have chosen : ∀ j ∈ T, pick j ∈ (gateAt C j).inputs ∧
      ∀ z : Fin n → Bool, signal C z (n+j) = signal C z (pick j) := by
    intro j hj
    simpa only [pick,dite_eq_left hj] using works j hj
  let D := copyPins C T pick
  obtain ⟨fan,reads,len,equal,removed⟩ := eliminate_pin_copies n C mono back T pick chosen
  refine ⟨D,fan,reads,len,fun z => equal z C.output,?_⟩
  have none : badGates n D = ∅ := by simpa only [T,Finset.sdiff_self] using removed
  intro j hj op k
  cases h : singleWire D k (n+j) with
  | false => rfl
  | true =>
    have mem : j ∈ badGates n D := memBad.mpr ⟨hj,op,k,h⟩
    rw [none] at mem
    exact (Finset.notMem_empty _ mem).elim


/-- For an arbitrary incidence circuit, absorbable bad ANDs suffice for the leased normal form.
The rewrite keeps each gate index and does not need any hypothesis on the incidence graph. -/
theorem incidence_normal_of_erasable (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (mono : Monotone2 C) (back : ReadsBack (N+N) C)
    (computes : ∀ z : Fin (N+N) → Bool, circuitFun (N+N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (can : ∀ j ∈ badGates (N+N) C, ∃ p ∈ (gateAt C j).inputs,
      ∀ z : Fin (N+N) → Bool, signal C z (N+N+j) = signal C z p) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size ≤ C.size ∧
      (∀ z : Fin (N+N) → Bool, circuitFun (N+N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D.gates.length, (gateAt D j).op = .and →
        (∀ p : Fin N, singleWire D (Fin.castAdd N p) (N+N+j) = false) ∧
        ∀ l : Fin N, singleWire D (Fin.natAdd N l) (N+N+j) = false) := by
  obtain ⟨D,fan,read,len,agree,clean⟩ := normal_of_erasable (N+N) C mono back can
  exact ⟨D,fan,read,len.le,fun z => by rw [agree z]; exact computes z,fun j hj op =>
    ⟨fun p => clean j hj op (Fin.castAdd N p),fun l => clean j hj op (Fin.natAdd N l)⟩⟩

/-- Copying a bad gate removes exactly one violation. -/
theorem strict_drop (n : ℕ) (C : Circuit) (mono : Monotone2 C) (back : ReadsBack n C)
    (j p : ℕ) (bad : j ∈ badGates n C) (pin : p ∈ (gateAt C j).inputs)
    (copy : ∀ z : Fin n → Bool, signal C z (n+j) = signal C z p) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size = C.size ∧
      circuitFun n D = circuitFun n C ∧ (badGates n D).card + 1 = (badGates n C).card := by
  classical
  let D := copyPins C {j} (fun _ => p)
  obtain ⟨fan,read,len,agree,removed⟩ := eliminate_pin_copies n C mono back {j} (fun _ => p)
    (by intro k hk; simp only [Finset.mem_singleton] at hk; subst k; exact ⟨pin,copy⟩)
  refine ⟨D,fan,read,len,funext (fun z => agree z C.output),?_⟩
  have rem : badGates n D = (badGates n C).erase j := by
    simpa only [Finset.sdiff_singleton_eq_erase] using removed
  rw [rem]
  exact Finset.card_erase_add_one bad

/-- In a representative minimizing the number of bad gates, each bad binary AND has two incomparable
operand functions. Along with the singleton witnessing badness, these are three distinct patterns. -/
theorem minimal_bad_incomparable (n : ℕ) (C : Circuit) (mono : Monotone2 C) (back : ReadsBack n C)
    (least : ∀ D : Circuit, Monotone2 D → ReadsBack n D → D.size ≤ C.size →
      circuitFun n D = circuitFun n C → (badGates n C).card ≤ (badGates n D).card)
    (j : ℕ) (bad : j ∈ badGates n C) (a b : ℕ) (pins : (gateAt C j).inputs = [a,b]) :
    (∃ z : Fin n → Bool, signal C z a = true ∧ signal C z b = false) ∧
    (∃ z : Fin n → Bool, signal C z a = false ∧ signal C z b = true) := by
  classical
  obtain ⟨valid,op,_⟩ := memBad.mp bad
  have cannot (p : ℕ) (pin : p ∈ (gateAt C j).inputs)
      (copy : ∀ z : Fin n → Bool, signal C z (n+j) = signal C z p) : False := by
    obtain ⟨D,fan,read,len,agree,drop⟩ := strict_drop n C mono back j p bad pin copy
    have bnd := least D fan read len.le agree
    omega
  constructor
  · by_contra h
    have dominates (z : Fin n → Bool) (ha : signal C z a = true) : signal C z b = true := by
      cases hb : signal C z b with
      | false => exact (h ⟨z,ha,hb⟩).elim
      | true => rfl
    obtain ⟨pin,copy⟩ := erasable_of_dominance C back j a b valid op pins dominates
    exact cannot a pin copy
  · by_contra h
    apply cannot b (by simp [pins])
    intro z
    rw [gateSignal C back z j valid,op,pins]
    cases ha : signal C z a <;> cases hb : signal C z b <;> simp [GateOp.eval,ha,hb]
    exact h ⟨z,ha,hb⟩

/-- A genuine incidence circuit with a violation: x AND (x OR y) feeds an AND with y.
Copying x leaves the target x AND y unchanged and makes the circuit singleton-clean. -/
theorem concrete_absorption :
    let C : Circuit := ⟨[⟨.or,[0,1]⟩,⟨.and,[0,2]⟩,⟨.and,[3,1]⟩],4⟩
    let D := copyPins C {1} (fun _ => 0)
    (∀ z : Fin 2 → Bool, circuitFun 2 C z = (z 0 && z 1) ∧ circuitFun 2 D z = (z 0 && z 1)) ∧
    singleWire C (0 : Fin 2) 3 = true ∧ D.size = C.size ∧
    (∀ j : Fin 3, (gateAt D j.val).op = .and → ∀ k : Fin 2, singleWire D k (2+j.val) = false) := by
  let := gateOpDecEq
  decide

/-- Every circuit has a no-larger representative where each remaining bad AND is nullary or has
incomparable operands. In the binary case two separating assignments coexist with the activating
singleton, so all three nonzero patterns occur at the two operands. -/
theorem representative_with_incomparable_violations (n : ℕ) (C : Circuit)
    (mono : Monotone2 C) (back : ReadsBack n C) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size ≤ C.size ∧ circuitFun n D = circuitFun n C ∧
      ∀ j ∈ badGates n D, (gateAt D j).inputs = [] ∨ ∃ a b,
        (gateAt D j).inputs = [a,b] ∧
        (∃ k : Fin n, singleWire D k a = true ∧ singleWire D k b = true) ∧
        (∃ z : Fin n → Bool, signal D z a = true ∧ signal D z b = false) ∧
        (∃ z : Fin n → Bool, signal D z a = false ∧ signal D z b = true) := by
  classical
  let P (count : ℕ) := ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size ≤ C.size ∧
    circuitFun n D = circuitFun n C ∧ (badGates n D).card = count
  have existsCount : ∃ k, P k := ⟨_,C,mono,back,le_rfl,rfl,rfl⟩
  obtain ⟨D,fan,read,len,agree,count⟩ := Nat.find_spec existsCount
  have least (E : Circuit) (m : Monotone2 E) (r : ReadsBack n E) (s : E.size ≤ D.size)
      (e : circuitFun n E = circuitFun n D) : (badGates n D).card ≤ (badGates n E).card := by
    rw [count]
    exact Nat.find_min' existsCount ⟨E,m,r,s.trans len,e.trans agree,rfl⟩
  refine ⟨D,fan,read,len,agree,?_⟩
  intro j bad
  obtain ⟨valid,op,k,firing⟩ := memBad.mp bad
  have arity := (fan (gateAt D j) (by unfold gateAt; rw [List.getD_eq_getElem _ _ valid]; exact List.getElem_mem valid)).2
  cases pins : (gateAt D j).inputs with
  | nil => exact Or.inl rfl
  | cons a tail =>
    cases tail with
    | nil =>
      have eq (z : Fin n → Bool) : signal D z (n+j) = signal D z a := by rw [gateSignal D read z j valid,op,pins]; simp [GateOp.eval]
      obtain ⟨E,m,r,s,e,drop⟩ := strict_drop n D fan read j a bad (by simp [pins]) eq
      have bound := least E m r s.le e
      omega
    | cons b tail =>
      cases tail with
      | nil =>
        rw [outRule D read k j valid] at firing
        have all := (andTrue _ _ op).mp firing
        obtain ⟨sepA,sepB⟩ := minimal_bad_incomparable n D fan read least j bad a b pins
        exact Or.inr ⟨a,b,rfl,⟨k,all a (by simp [pins]),all b (by simp [pins])⟩,sepA,sepB⟩
      | cons c t => simp [pins] at arity

/-- A wire is marked exactly when it is the constant true on all assignments. -/
private def AlwaysTrue (n : ℕ) (C : Circuit) (i : ℕ) := ∀ z : Fin n → Bool, signal C z i = true

private noncomputable def stripGate (n : ℕ) (C : Circuit) (j : ℕ) (g : Gate) : Gate := by
  classical
  exact if AlwaysTrue n C (n+j) then ⟨.or,[]⟩ else if g.op = .and then
    ⟨.and,g.inputs.filter (fun p => decide (¬ AlwaysTrue n C p))⟩ else g

/-- Replace constant-true gates by constant-false placeholders, and bypass all their former uses. -/
noncomputable def stripTrue (n : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.mapIdx (stripGate n C), C.output⟩

private theorem stripAt (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt (stripTrue n C) j = stripGate n C j (gateAt C j) := by
  unfold gateAt stripTrue
  rw [List.getD_eq_getElem _ _ (by simp [hj]),List.getD_eq_getElem _ _ hj]
  simp only [List.getElem_mapIdx]

private theorem rawSignal (n : ℕ) (C : Circuit) (z : Fin n → Bool) (i : Fin n) : signal C z i.val = z i := by
  let w := List.ofFn z
  change (C.gates.foldl step w).getD i.val false = _
  rw [oldRead _ _ _ (by simp [w])]
  simp [w,List.getD_eq_getElem?_getD]

/-- This transformation preserves all nonconstant-true wires and makes every constant-true wire false.
It introduces no new bad gate and every remaining AND has at least one operand. -/
theorem strip_constants (n : ℕ) (C : Circuit) (mono : Monotone2 C) (back : ReadsBack n C) :
    let D := stripTrue n C
    Monotone2 D ∧ ReadsBack n D ∧ D.size = C.size ∧
      (∀ (z : Fin n → Bool) (i : ℕ),
        (AlwaysTrue n C i → signal D z i = false) ∧ (¬ AlwaysTrue n C i → signal D z i = signal C z i)) ∧
      badGates n D ⊆ badGates n C ∧ ∀ j < D.gates.length, (gateAt D j).op = .and → (gateAt D j).inputs ≠ [] := by
  classical
  let D := stripTrue n C
  have len : D.gates.length = C.gates.length := by simp [D,stripTrue]
  have atD := stripAt n C
  have oldMono (j : ℕ) (v : j < C.gates.length) := mono (gateAt C j) (by unfold gateAt; rw [List.getD_eq_getElem _ _ v]; exact List.getElem_mem v)
  have fan : Monotone2 D := by
    intro g hg
    obtain ⟨j,hj,heq⟩ := List.mem_iff_getElem.mp hg
    have v : j < C.gates.length := by omega
    have atj : gateAt D j = g := by simpa only [gateAt,List.getD_eq_getElem _ _ hj] using heq
    rw [← atj,atD j v]
    by_cases mark : AlwaysTrue n C (n+j)
    · simp [stripGate,mark]
    by_cases ha : (gateAt C j).op = .and
    · simp only [stripGate,ite_eq_right mark,ite_eq_left ha]
      exact ⟨by simp, (List.length_filter_le ..).trans (oldMono j v).2⟩
    · simpa [stripGate,mark,ha] using oldMono j v
  have reads : ReadsBack n D := by
    intro j hj p hp
    have v : j < C.gates.length := by omega
    rw [atD j v] at hp
    by_cases mark : AlwaysTrue n C (n+j)
    · simp [stripGate,mark] at hp
    by_cases ha : (gateAt C j).op = .and
    · simp [stripGate,mark,ha] at hp
      exact back j v p hp.1
    · exact back j v p (by simpa [stripGate,mark,ha] using hp)
  have transfer (z : Fin n → Bool) (i : ℕ) :
      (AlwaysTrue n C i → signal D z i = false) ∧ (¬ AlwaysTrue n C i → signal D z i = signal C z i) := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      by_cases raw : i < n
      · let p : Fin n := ⟨i,raw⟩
        have never : ¬ AlwaysTrue n C i := fun h => by have hd := h (fun _ => false); rw [show i=p.val from rfl,rawSignal] at hd; contradiction
        exact ⟨fun h => (never h).elim,fun _ => (rawSignal n D z p).trans (rawSignal n C z p).symm⟩
      by_cases past : n+C.gates.length ≤ i
      · have outside (E : Circuit) (bound : E.gates.length = C.gates.length) : signal E z i = false := by
          change (E.gates.foldl step (List.ofFn z)).getD i false = false
          apply List.getD_eq_default
          simpa [lengthRun,bound] using past
        exact ⟨fun _ => outside D len,fun _ => (outside D len).trans (outside C rfl).symm⟩
      let j := i-n
      have idx : i = n+j := by dsimp [j]; omega
      have v : j < C.gates.length := by omega
      have vd : j < D.gates.length := by omega
      rw [idx]
      constructor
      · intro mark
        rw [gateSignal D reads z j vd,atD j v]
        simp [stripGate,mark,GateOp.eval]
      · intro mark
        have pinwise (p : ℕ) (hp : p ∈ (gateAt C j).inputs) (np : ¬ AlwaysTrue n C p) := (ih p (by have := back j v p hp; omega)).2 np
        rcases (show (gateAt C j).op = .and ∨ (gateAt C j).op = .or by simpa using (oldMono j v).1) with ha | ho
        · apply Bool.eq_iff_iff.mpr
          rw [gateSignal D reads z j vd,atD j v,gateSignal C back z j v]
          simp only [stripGate,ite_eq_right mark,ite_eq_left ha]
          rw [andTrue (⟨.and,(gateAt C j).inputs.filter (fun q => decide (¬ AlwaysTrue n C q))⟩ : Gate) (signal D z) rfl,andTrue _ _ ha]
          constructor
          · intro all p hp
            by_cases cp : AlwaysTrue n C p
            · exact cp z
            · rw [← pinwise p hp cp]; exact all p (by simp [hp,cp])
          · intro all p hp
            simp only [List.mem_filter] at hp
            rw [pinwise p hp.1 (of_decide_eq_true hp.2)]; exact all p hp.1
        · have notAnd : (gateAt C j).op ≠ .and := by simp [ho]
          have notConstant (p : ℕ) (hp : p ∈ (gateAt C j).inputs) : ¬ AlwaysTrue n C p := by
            intro cp
            apply mark
            intro x
            rw [gateSignal C back x j v]
            exact (orTrue _ _ ho).mpr ⟨p,hp,cp x⟩
          rw [gateSignal D reads z j vd,atD j v,gateSignal C back z j v]
          simp only [stripGate,ite_eq_right mark,ite_eq_right notAnd]
          exact congrArg _ (List.map_congr_left (fun p hp => pinwise p hp (notConstant p hp)))
  refine ⟨fan,reads,len,transfer,?_,?_⟩
  · intro j bad
    obtain ⟨hj,op,k,firing⟩ := memBad.mp bad
    change j < D.gates.length at hj
    have v : j < C.gates.length := by omega
    rw [atD j v] at op
    by_cases mark : AlwaysTrue n C (n+j)
    · simp [stripGate,mark] at op
    have ha : (gateAt C j).op = .and := by by_contra no; simp [stripGate,mark,no] at op
    exact memBad.mpr ⟨v,ha,k,((transfer (fun q => decide (q=k)) (n+j)).2 mark).symm.trans firing⟩
  · intro j hj op empty
    change j < D.gates.length at hj
    have v : j < C.gates.length := by omega
    rw [atD j v] at op empty
    by_cases mark : AlwaysTrue n C (n+j)
    · simp [stripGate,mark] at op
    have ha : (gateAt C j).op = .and := by by_contra no; simp [stripGate,mark,no] at op
    simp only [stripGate,ite_eq_right mark,ite_eq_left ha] at empty
    apply mark
    intro z
    rw [gateSignal C back z j v]
    apply (andTrue _ _ ha).mpr
    intro p hp
    by_cases cp : AlwaysTrue n C p
    · exact cp z
    · have mem : p ∈ (gateAt C j).inputs.filter (fun k => decide (¬ AlwaysTrue n C k)) := by simp [hp,cp]
      rw [empty] at mem
      exact (List.not_mem_nil mem).elim

/-- Every monotone backward-reading circuit whose output can be false has a no-larger equivalent
representative with no nullary ANDs and with three concretely witnessed operand patterns at every
singleton-violating AND. In particular, the remaining obstruction can only be a binary AND. -/
theorem binary_incomparable_representative (n : ℕ) (C : Circuit)
    (mono : Monotone2 C) (back : ReadsBack n C) (nontrivial : ∃ z : Fin n → Bool, circuitFun n C z = false) :
    ∃ E : Circuit, Monotone2 E ∧ ReadsBack n E ∧ E.size ≤ C.size ∧ circuitFun n E = circuitFun n C ∧
      (∀ j < E.gates.length, (gateAt E j).op = .and → (gateAt E j).inputs ≠ []) ∧
      ∀ j ∈ badGates n E, ∃ a b,
        (gateAt E j).inputs = [a,b] ∧
        (∃ k : Fin n, singleWire E k a = true ∧ singleWire E k b = true) ∧
        (∃ z : Fin n → Bool, signal E z a = true ∧ signal E z b = false) ∧
        (∃ z : Fin n → Bool, signal E z a = false ∧ signal E z b = true) := by
  classical
  obtain ⟨D,m,r,s,e,obstruction⟩ := representative_with_incomparable_violations n C mono back
  let E := stripTrue n D
  obtain ⟨me,re,se,tr,subset,nonnull⟩ := strip_constants n D m r
  obtain ⟨zero,off⟩ := nontrivial
  have notOut : ¬ AlwaysTrue n D D.output := by
    intro marked
    have on : circuitFun n D zero = true := marked zero
    rw [e,off] at on
    contradiction
  have output : circuitFun n E = circuitFun n D := funext (fun z => (tr z D.output).2 notOut)
  refine ⟨E,me,re,se.le.trans s,output.trans e,nonnull,?_⟩
  intro j bad
  have old := subset bad
  obtain ⟨valid,ha,_⟩ := memBad.mp old
  have op := (memBad.mp bad).2.1
  change (gateAt (stripTrue n D) j).op = .and at op
  rw [stripAt n D j valid] at op
  have notMarked : ¬ AlwaysTrue n D (n+j) := by intro h; simp [stripGate,h] at op
  rcases obstruction j old with empty | ⟨a,b,pins,⟨k,onA,onB⟩,⟨x,xA,xB⟩,⟨y,yA,yB⟩⟩
  · exfalso
    apply notMarked
    intro z
    rw [gateSignal D r z j valid,ha,empty]
    rfl
  · have notA : ¬ AlwaysTrue n D a := by intro h; rw [h y] at yA; contradiction
    have notB : ¬ AlwaysTrue n D b := by intro h; rw [h x] at xB; contradiction
    have ea (z : Fin n → Bool) : signal E z a = signal D z a := (tr z a).2 notA
    have eb (z : Fin n → Bool) : signal E z b = signal D z b := (tr z b).2 notB
    refine ⟨a,b,?_,⟨k,(ea _).trans onA,(eb _).trans onB⟩,⟨x,(ea _).trans xA,(eb _).trans xB⟩,⟨y,(ea _).trans yA,(eb _).trans yB⟩⟩
    change (gateAt (stripTrue n D) j).inputs = [a,b]
    rw [stripAt n D j valid]
    simp [stripGate,notMarked,ha,pins,notA,notB]

/-- Once nullary ANDs have been removed, no wire is true on the all-zero input. -/
theorem all_zero_of_no_nullary (n : ℕ) (D : Circuit) (mono : Monotone2 D) (back : ReadsBack n D)
    (nonnull : ∀ j < D.gates.length, (gateAt D j).op = .and → (gateAt D j).inputs ≠ [])
    (i : ℕ) : signal D (fun _ : Fin n => false) i = false := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases raw : i < n
    · exact rawSignal n D (fun _ => false) ⟨i,raw⟩
    by_cases past : n+D.gates.length ≤ i
    · change (D.gates.foldl step (List.ofFn (fun _ : Fin n => false))).getD i false = false
      apply List.getD_eq_default
      simpa [lengthRun] using past
    let j := i-n
    have idx : i = n+j := by dsimp [j]; omega
    have v : j < D.gates.length := by omega
    have fan := mono (gateAt D j) (by unfold gateAt; rw [List.getD_eq_getElem _ _ v]; exact List.getElem_mem v)
    cases yes : signal D (fun _ : Fin n => false) i with
    | false => rfl
    | true =>
      rw [idx,gateSignal D back (fun _ => false) j v] at yes
      have pinFalse (p : ℕ) (hp : p ∈ (gateAt D j).inputs) := ih p (by have := back j v p hp; omega)
      rcases (show (gateAt D j).op = .and ∨ (gateAt D j).op = .or by simpa using fan.1) with ha | ho
      · obtain ⟨p,hp⟩ := List.exists_mem_of_ne_nil _ (nonnull j v ha)
        have on := (andTrue _ _ ha).mp yes p hp
        rw [pinFalse p hp] at on
        contradiction
      · obtain ⟨p,hp,on⟩ := (orTrue _ _ ho).mp yes
        rw [pinFalse p hp] at on
        contradiction

/-- In the incidence problem one can require an equivalent no-larger circuit whose every remaining
bad AND realizes all four input patterns. The all-zero pattern is realized by the all-zero input,
and the both-true pattern is realized by a raw singleton. -/
theorem incidence_residual_four_patterns (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (mono : Monotone2 C) (back : ReadsBack (N+N) C)
    (computes : ∀ z : Fin (N+N) → Bool, circuitFun (N+N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size ≤ C.size ∧
      (∀ z : Fin (N+N) → Bool, circuitFun (N+N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D.gates.length, (gateAt D j).op = .and → (gateAt D j).inputs ≠ []) ∧
      ∀ j ∈ badGates (N+N) D, ∃ a b, (gateAt D j).inputs = [a,b] ∧
        (signal D (fun _ : Fin (N+N) => false) a = false ∧ signal D (fun _ : Fin (N+N) => false) b = false) ∧
        (∃ k : Fin (N+N), singleWire D k a = true ∧ singleWire D k b = true) ∧
        (∃ z : Fin (N+N) → Bool, signal D z a = true ∧ signal D z b = false) ∧
        (∃ z : Fin (N+N) → Bool, signal D z a = false ∧ signal D z b = true) := by
  let zero := fun _ : Fin (N+N) => false
  have off : circuitFun (N+N) C zero = false := by
    cases h : circuitFun (N+N) C zero with
    | false => rfl
    | true => obtain ⟨_,_,_,on,_⟩ := (computes zero).mp h; contradiction
  obtain ⟨D,m,r,s,e,nonnull,obstruction⟩ := binary_incomparable_representative _ C mono back ⟨zero,off⟩
  refine ⟨D,m,r,s,fun z => by rw [e]; exact computes z,nonnull,?_⟩
  intro j bad
  obtain ⟨a,b,pins,on,left,right⟩ := obstruction j bad
  exact ⟨a,b,pins,⟨all_zero_of_no_nullary _ D m r nonnull a,all_zero_of_no_nullary _ D m r nonnull b⟩,on,left,right⟩

private theorem copy_well_formed (n : ℕ) (C : Circuit) (mono : Monotone2 C) (back : ReadsBack n C)
    (j a : ℕ) (pin : a ∈ (gateAt C j).inputs) :
    let D := copyPins C {j} (fun _ => a)
    Monotone2 D ∧ ReadsBack n D ∧ D.size = C.size := by
  classical
  let D := copyPins C {j} (fun _ => a)
  have len : D.gates.length = C.gates.length := by simp [D,copyPins]
  have atD := copyAt C {j} (fun _ => a)
  refine ⟨?_,?_,len⟩
  · intro g hg
    obtain ⟨h,hv,he⟩ := List.mem_iff_getElem.mp hg
    change h < D.gates.length at hv
    have v : h < C.gates.length := by omega
    have atg : gateAt D h = g := by simpa only [gateAt,List.getD_eq_getElem _ _ hv] using he
    rw [← atg,atD h v]
    by_cases isJ : h = j
    · simp [isJ]
    · simp only [Finset.mem_singleton,ite_eq_right isJ]
      exact mono _ (by unfold gateAt; rw [List.getD_eq_getElem _ _ v]; exact List.getElem_mem v)
  · intro h hv p hp
    change h < D.gates.length at hv
    have v : h < C.gates.length := by omega
    rw [atD h v] at hp
    by_cases isJ : h = j
    · subst h
      have eq : p = a := by simpa using hp
      exact eq ▸ back j v a pin
    · exact back h v p (by simpa [isJ] using hp)

/-- A bad binary AND may be replaced by one operand even when they are incomparable: it suffices
that each consumer is an AND with a different guard wire that forces the discarded operand.
All wires except the replaced gate retain their Boolean function, including arbitrary downstream sharing. -/
theorem eliminate_guarded_and (n : ℕ) (C : Circuit) (mono : Monotone2 C) (back : ReadsBack n C)
    (j a b : ℕ) (bad : j ∈ badGates n C) (pins : (gateAt C j).inputs = [a,b] ∨ (gateAt C j).inputs = [b,a])
    (away : C.output ≠ n+j)
    (guarded : ∀ h < C.gates.length, n+j ∈ (gateAt C h).inputs →
      (gateAt C h).op = .and ∧ ∃ q ∈ (gateAt C h).inputs, q ≠ n+j ∧
        ∀ z : Fin n → Bool, signal C z q = true → signal C z b = true) :
    let D := copyPins C {j} (fun _ => a)
    Monotone2 D ∧ ReadsBack n D ∧ D.size = C.size ∧ circuitFun n D = circuitFun n C ∧
      (∀ (z : Fin n → Bool) (i : ℕ), i ≠ n+j → signal D z i = signal C z i) ∧
      badGates n D = (badGates n C).erase j := by
  classical
  let D := copyPins C {j} (fun _ => a)
  have len : D.gates.length = C.gates.length := by simp [D,copyPins]
  have atD := copyAt C {j} (fun _ => a)
  have aPin : a ∈ (gateAt C j).inputs := by rcases pins with h | h <;> simp [h]
  obtain ⟨m,r,s⟩ := copy_well_formed n C mono back j a aPin
  obtain ⟨jv,ja,_⟩ := memBad.mp bad
  have copied : gateAt D j = ⟨.or,[a]⟩ := by simpa using atD j jv
  have sameAt (t : ℕ) (tv : t < C.gates.length) (diff : t ≠ j) : gateAt D t = gateAt C t := by simpa [diff] using atD t tv
  have eval (z : Fin n → Bool) (i : ℕ) : signal D z i = if i = n+j then signal C z a else signal C z i := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      by_cases raw : i < n
      · have diff : i ≠ n+j := by omega
        rw [ite_eq_right diff]
        exact (rawSignal n D z ⟨i,raw⟩).trans (rawSignal n C z ⟨i,raw⟩).symm
      by_cases past : n+C.gates.length ≤ i
      · have diff : i ≠ n+j := by omega
        have outside (E : Circuit) (l : E.gates.length = C.gates.length) : signal E z i = false := by
          change (E.gates.foldl step (List.ofFn z)).getD i false = false
          apply List.getD_eq_default
          simpa [lengthRun,l] using past
        rw [ite_eq_right diff,outside D len,outside C rfl]
      let t := i-n
      have idx : i = n+t := by dsimp [t]; omega
      have v : t < C.gates.length := by omega
      have vd : t < D.gates.length := by omega
      by_cases isJ : t = j
      · have atJ : i = n+j := by omega
        have aprev := back j jv a aPin
        have prior : signal D z a = signal C z a := by simpa [show a ≠ n+j by omega] using ih a (by omega)
        rw [ite_eq_left atJ,atJ,gateSignal D r z j (by omega),copied]
        simp [GateOp.eval,prior]
      have diff : i ≠ n+j := by omega
      have elsewhere (q : ℕ) (hq : q ∈ (gateAt C t).inputs) (ne : q ≠ n+j) : signal D z q = signal C z q := by
        simpa [ne] using ih q (by have := back t v q hq; omega)
      rw [ite_eq_right diff,idx,gateSignal D r z t vd,sameAt t v isJ,gateSignal C back z t v]
      by_cases used : n+j ∈ (gateAt C t).inputs
      · obtain ⟨gate,q,qpin,neq,force⟩ := guarded t v used
        by_cases bOn : signal C z b = true
        · have original : signal C z (n+j) = signal C z a := by
            rw [gateSignal C back z j jv,ja]
            rcases pins with h | h <;> simp [h,GateOp.eval,bOn]
          have asCopy : signal D z (n+j) = signal C z a := by simpa using ih (n+j) (by have := back t v (n+j) used; omega)
          apply congrArg _ (List.map_congr_left ?_)
          intro p hpin
          by_cases pJ : p = n+j
          · subst p; exact asCopy.trans original.symm
          · exact elsewhere p hpin pJ
        · have off : signal C z q = false := by cases h : signal C z q with | false => rfl | true => exact (bOn (force z h)).elim
          have doff := (elsewhere q qpin neq).trans off
          apply Bool.eq_iff_iff.mpr
          rw [andTrue _ _ gate,andTrue _ _ gate]
          constructor
          · intro all; have h := all q qpin; rw [doff] at h; contradiction
          · intro all; have h := all q qpin; rw [off] at h; contradiction
      · apply congrArg _ (List.map_congr_left ?_)
        intro p hp
        exact elsewhere p hp (by intro h; exact used (h ▸ hp))
  have except (z : Fin n → Bool) (i : ℕ) (ne : i ≠ n+j) : signal D z i = signal C z i := by simpa [ne] using eval z i
  refine ⟨m,r,s,funext (fun z => except z C.output away),except,?_⟩
  change badGates n D = (badGates n C).erase j
  ext t
  by_cases h : t = j
  · subst t; simp [memBad,copied]
  by_cases v : t < C.gates.length
  · have singled (k : Fin n) : singleWire D k (n+t) = singleWire C k (n+t) := except _ _ (by omega)
    simp [memBad,h,len,sameAt t v h,singled]
  · simp [memBad,h,len,v]

/-- In a minimum-bad representative, every non-output bad binary AND has a consumer where
forgetting the specified operand is not protected by any single guarding pin. The conclusion
applies independently to either operand. -/
theorem minimal_bad_has_unguarded_consumer (n : ℕ) (C : Circuit) (mono : Monotone2 C) (back : ReadsBack n C)
    (least : ∀ D : Circuit, Monotone2 D → ReadsBack n D → D.size ≤ C.size →
      circuitFun n D = circuitFun n C → (badGates n C).card ≤ (badGates n D).card)
    (j keep drop : ℕ) (bad : j ∈ badGates n C)
    (pins : (gateAt C j).inputs = [keep,drop] ∨ (gateAt C j).inputs = [drop,keep]) (away : C.output ≠ n+j) :
    ∃ h < C.gates.length, n+j ∈ (gateAt C h).inputs ∧ ¬ ((gateAt C h).op = .and ∧
      ∃ q ∈ (gateAt C h).inputs, q ≠ n+j ∧ ∀ z : Fin n → Bool, signal C z q = true → signal C z drop = true) := by
  classical
  by_contra none
  have all (h : ℕ) (hv : h < C.gates.length) (uses : n+j ∈ (gateAt C h).inputs) :
      (gateAt C h).op = .and ∧ ∃ q ∈ (gateAt C h).inputs, q ≠ n+j ∧
        ∀ z : Fin n → Bool, signal C z q = true → signal C z drop = true := by
    by_contra missing
    exact none ⟨h,hv,uses,missing⟩
  obtain ⟨m,r,s,e,_,erased⟩ := eliminate_guarded_and n C mono back j keep drop bad pins away all
  have lb := least _ m r s.le e
  rw [erased] at lb
  have dec := Finset.card_erase_add_one bad
  omega

/-- An incomparable bad AND really occurs in an incidence circuit for the two edges xz and yz.
All four operand patterns are attainable. Its sole consumer is guarded by z, and copying the
other operand makes the entire circuit clean with the identical output truth table. -/
theorem concrete_guarded_incomparable :
    let C : Circuit := ⟨[⟨.or,[0,1]⟩,⟨.or,[0,2]⟩,⟨.and,[4,5]⟩,⟨.and,[6,2]⟩],7⟩
    let D := copyPins C {2} (fun _ => 4)
    (∀ z : Fin 4 → Bool, circuitFun 4 C z = ((z 0 || z 1) && z 2) ∧ circuitFun 4 D z = ((z 0 || z 1) && z 2)) ∧
      singleWire C (0 : Fin 4) 6 = true ∧
      (∀ a b : Bool, ∃ z : Fin 4 → Bool, signal C z 4 = a ∧ signal C z 5 = b) ∧ D.size = C.size ∧
      (∀ j : Fin 4, (gateAt D j.val).op = .and → ∀ k : Fin 4, singleWire D k (4+j.val) = false) := by
  let := gateOpDecEq
  decide

/-- At this consumer, a single independent input pin cannot guard away the indicated operand. -/
def UnguardedConsumer (n : ℕ) (C : Circuit) (j discard : ℕ) : Prop :=
  ∃ h < C.gates.length, n+j ∈ (gateAt C h).inputs ∧ ¬ ((gateAt C h).op = .and ∧
    ∃ q ∈ (gateAt C h).inputs, q ≠ n+j ∧ ∀ z : Fin n → Bool, signal C z q = true → signal C z discard = true)

/-- A necessary obstruction for the exact incidence task: in a no-larger representative, each
remaining violation is a binary AND attaining every operand pattern, with at least one unguarded
consumer for each possible discarded operand. The two consumers need not be different. -/
theorem incidence_residual_unguarded (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (mono : Monotone2 C) (back : ReadsBack (N+N) C)
    (computes : ∀ z : Fin (N+N) → Bool, circuitFun (N+N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size ≤ C.size ∧
      (∀ z : Fin (N+N) → Bool, circuitFun (N+N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D.gates.length, (gateAt D j).op = .and → (gateAt D j).inputs ≠ []) ∧
      ∀ j ∈ badGates (N+N) D, ∃ a b, (gateAt D j).inputs = [a,b] ∧
        (signal D (fun _ : Fin (N+N) => false) a = false ∧ signal D (fun _ : Fin (N+N) => false) b = false) ∧
        (∃ k : Fin (N+N), singleWire D k a = true ∧ singleWire D k b = true) ∧
        (∃ z : Fin (N+N) → Bool, signal D z a = true ∧ signal D z b = false) ∧
        (∃ z : Fin (N+N) → Bool, signal D z a = false ∧ signal D z b = true) ∧
        UnguardedConsumer (N+N) D j a ∧ UnguardedConsumer (N+N) D j b := by
  classical
  let n := N+N
  let P (count : ℕ) := ∃ M : Circuit, Monotone2 M ∧ ReadsBack n M ∧ M.size ≤ C.size ∧
    circuitFun n M = circuitFun n C ∧ (badGates n M).card = count
  have eligible : ∃ k, P k := ⟨_,C,mono,back,le_rfl,rfl,rfl⟩
  obtain ⟨M,mm,mr,ms,me,count⟩ := Nat.find_spec eligible
  let D := stripTrue n M
  obtain ⟨m,r,sz,tr,subset,nonnull⟩ := strip_constants n M mm mr
  have nz : ¬ AlwaysTrue n M M.output := by
    intro always
    let zero := fun _ : Fin n => false
    have on : circuitFun n M zero = true := always zero
    rw [me] at on
    obtain ⟨_,_,_,impossible,_⟩ := (computes zero).mp on
    contradiction
  have eqD : circuitFun n D = circuitFun n C := (funext (fun z => (tr z M.output).2 nz) : circuitFun n D = circuitFun n M).trans me
  have sizeD : D.size ≤ C.size := sz.le.trans ms
  have least (E : Circuit) (em : Monotone2 E) (er : ReadsBack n E) (es : E.size ≤ D.size) (ee : circuitFun n E = circuitFun n D) :
      (badGates n D).card ≤ (badGates n E).card := by
    apply (Finset.card_le_card subset).trans
    rw [count]
    exact Nat.find_min' eligible ⟨E,em,er,es.trans sizeD,ee.trans eqD,rfl⟩
  refine ⟨D,m,r,sizeD,fun z => by change circuitFun n D z = true ↔ _; rw [eqD]; exact computes z,nonnull,?_⟩
  intro j bad
  obtain ⟨v,ha,k,on⟩ := memBad.mp bad
  have away : D.output ≠ n+j := by
    intro h
    rw [← h] at on
    let one := fun q : Fin n => decide (q=k)
    change circuitFun n D one = true at on
    rw [eqD] at on
    obtain ⟨p,l,_,pon,lon⟩ := (computes one).mp on
    have absurd : Fin.castAdd N p = Fin.natAdd N l := (of_decide_eq_true pon).trans (of_decide_eq_true lon).symm
    have hval := congrArg Fin.val absurd
    simp at hval
    omega
  have arity := (m (gateAt D j) (by unfold gateAt; rw [List.getD_eq_getElem _ _ v]; exact List.getElem_mem v)).2
  cases pins : (gateAt D j).inputs with
  | nil => exact (nonnull j v ha pins).elim
  | cons a tail =>
    cases tail with
    | nil =>
      have cp (z : Fin n → Bool) : signal D z (n+j) = signal D z a := by rw [gateSignal D r z j v,ha,pins]; simp [GateOp.eval]
      obtain ⟨E,em,er,es,ee,drop⟩ := strict_drop n D m r j a bad (by simp [pins]) cp
      have bound := least E em er es.le ee
      omega
    | cons b tail =>
      cases tail with
      | nil =>
        rw [outRule D r k j v] at on
        have all := (andTrue _ _ ha).mp on
        obtain ⟨l,rgt⟩ := minimal_bad_incomparable n D m r least j bad a b pins
        exact ⟨a,b,rfl,⟨all_zero_of_no_nullary n D m r nonnull a,all_zero_of_no_nullary n D m r nonnull b⟩,
          ⟨k,all a (by simp [pins]),all b (by simp [pins])⟩,l,rgt,
          minimal_bad_has_unguarded_consumer n D m r least j b a bad (Or.inr pins) away,
          minimal_bad_has_unguarded_consumer n D m r least j a b bad (Or.inl pins) away⟩
      | cons c t => simp [pins] at arity

end PEqualNP.Local3456
