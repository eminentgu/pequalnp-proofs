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

end PEqualNP.Local3456
