import PEqualNP.Defs

namespace PEqualNP.Research.GuardedReaders

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover

/-- An acyclic exact-two AND/OR program on named input ports. Each gate gives the remaining
program one additional port, named `none`. Older ports remain accessible through `some`. -/
inductive Net : Type → Type 1 where
  | output {α : Type} (a : α) : Net α
  | gate {α : Type} (isAnd : Bool) (a b : α) (tail : Net (Option α)) : Net α

def bin (op p q : Bool) : Bool := if op then p && q else p || q

def Net.size {α : Type} : Net α → Nat
  | .output _ => 0
  | .gate _ _ _ rest => rest.size + 1

def Net.value {α : Type} (s : Net α) (v : α → Bool) : Bool := match s with
  | .output a => v a
  | .gate op a b rest => rest.value (fun z => z.elim (bin op (v a) (v b)) v)

def Net.emit {α : Type} (s : Net α) (next : Nat) (r : α → Nat) : Circuit := match s with
  | .output a => ⟨[],r a⟩
  | .gate op a b rest =>
    let D := rest.emit (next+1) (fun z => z.elim next r)
    ⟨⟨if op then .and else .or,[r a,r b]⟩ :: D.gates,D.output⟩

private theorem evalBin (op : Bool) (p q : Bool) :
    (if op then GateOp.and else .or).eval [p,q] = bin op p q := by
  cases op <;> simp [GateOp.eval,bin]

theorem Net.emit_spec {α} (s : Net α) (w : List Bool) (r : α → Nat)
    (bound : ∀ a, r a < w.length) :
    (s.emit w.length r).eval w = s.value (fun a => w.getD (r a) false) := by
  induction s generalizing w with
  | output a => rfl
  | gate op a b rest ih =>
    let bit := bin op (w.getD (r a) false) (w.getD (r b) false)
    let extended := w ++ [bit]
    have len : extended.length = w.length+1 := by simp [extended]
    let rr : Option _ → Nat := fun z => z.elim w.length r
    have legal : ∀ z, rr z < extended.length := by
      intro z
      cases z with
      | none => rw [len]; exact Nat.lt_succ_self _
      | some p => rw [len]; exact Nat.lt_succ_of_lt (bound p)
    have val : (fun z => extended.getD (rr z) false) =
        (fun z => z.elim bit (fun a => w.getD (r a) false)) := by
      funext z
      cases z with
      | none => simp [rr,extended,List.getD_eq_getElem?_getD]
      | some p => exact List.getD_append _ _ _ _ (bound p)
    have spec := ih extended rr legal
    rw [val,len] at spec
    change ((rest.emit (w.length+1) rr).wires (w ++ [_])).getD (rest.emit (w.length+1) rr).output false = _
    simpa [Circuit.eval,extended,bit,Net.value,evalBin] using spec

theorem Net.emit_size {α} (s : Net α) (n : Nat) (r : α → Nat) : (s.emit n r).size = s.size := by
  induction s generalizing n with
  | output => rfl
  | gate op a b s ih => exact congrArg (· + 1) (ih (n+1) _)

theorem Net.emit_mono {α} (s : Net α) (n : Nat) (r : α → Nat) : Monotone2 (s.emit n r) := by
  induction s generalizing n with
  | output => simp [Net.emit,Monotone2]
  | gate op a b s ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · cases op <;> simp
    · exact ih (n+1) _ _ hg

def Net.rename {α β : Type} (s : Net α) (f : α → β) : Net β := match s with
  | .output a => .output (f a)
  | .gate op a b rest => .gate op (f a) (f b) (rest.rename (Option.map f))

theorem Net.rename_value {α β} (s : Net α) (f : α → β) (v : β → Bool) :
    (s.rename f).value v = s.value (fun a => v (f a)) := by
  induction s generalizing β with
  | output => rfl
  | gate op a b rest ih =>
    simp only [Net.rename,Net.value,ih]
    congr 1
    funext z
    cases z <;> rfl

theorem Net.rename_size {α β} (s : Net α) (f : α → β) : (s.rename f).size = s.size := by
  induction s generalizing β with
  | output => rfl
  | gate op a b rest ih => simp only [Net.rename,Net.size,ih]

theorem bin_mono {op a b c d : Bool}
    (ac : a = true → c = true) (bd : b = true → d = true) :
    bin op a b = true → bin op c d = true := by
  cases op <;> cases a <;> cases b <;> simp_all [bin]

theorem Net.value_mono {α} (s : Net α) {v w : α → Bool} (le : ∀ i, v i = true → w i = true) :
    s.value v = true → s.value w = true := by
  induction s with
  | output a => exact le a
  | gate op a b rest ih =>
    apply ih
    intro z
    cases z with
    | none => exact bin_mono (le a) (le b)
    | some a => exact le a

/-- A reader with guard `h` and alternative `b` exposes `h ∧ (shared ∨ b)` to the rest
of the circuit. The remainder may reuse any earlier public input or guarded result. -/
inductive Readers : Type → Type 1 where
  | finish {α : Type} (suffix : Net α) : Readers α
  | reader {α : Type} (takeLeft : Bool) (guard alt : α) (tail : Readers (Option α)) : Readers α

def Readers.value {α : Type} (s : Readers α) (read : Bool → Bool) (v : α → Bool) : Bool := match s with
  | .finish suffix => suffix.value v
  | .reader side g b rest => rest.value read (fun z => z.elim (v g && (read side || v b)) v)

def Readers.size {α : Type} (s : Readers α) : Nat := match s with
  | .finish suffix => suffix.size
  | .reader _ _ _ rest => rest.size + 2

def Readers.compile {α β : Type} (s : Readers α) (read : Bool → β) (f : α → β) : Net β := match s with
  | .finish suffix => suffix.rename f
  | .reader side g b rest =>
    .gate false (read side) (f b) <| .gate true (.some (f g)) .none <|
      rest.compile (fun k => .some (.some (read k))) (fun z => z.elim .none (fun a => .some (.some (f a))))

theorem Readers.compile_size {α β} (s : Readers α) (read : Bool → β) (f : α → β) :
    (s.compile read f).size = s.size := by
  induction s generalizing β with
  | finish t => exact t.rename_size f
  | reader side g b rest ih => simp [Readers.compile,Net.size,Readers.size,ih,Nat.add_assoc]

theorem Readers.compile_value {α β} (s : Readers α) (read : Bool → β) (f : α → β) (v : β → Bool) :
    (s.compile read f).value v = s.value (fun k => v (read k)) (fun a => v (f a)) := by
  induction s generalizing β with
  | finish t => exact t.rename_value f v
  | reader side g b rest ih =>
    simp only [Readers.compile,Readers.value,Net.value,ih]
    congr 1
    funext z
    cases z <;> rfl

theorem Readers.value_mono {α} (s : Readers α) {a b : Bool → Bool} {v w : α → Bool}
    (ht : ∀ k, a k = true → b k = true) (hw : ∀ k, v k = true → w k = true) :
    s.value a v = true → s.value b w = true := by
  induction s with
  | finish t => exact t.value_mono hw
  | reader side g alt rest ih =>
    apply ih
    intro z
    cases z with
    | some j => exact hw j
    | none =>
      exact bin_mono (op := true) (hw g) (bin_mono (op := false) (ht side) (hw alt))

/-- The only potentially distinguishing row at a reader has guard=1, alternative=0,
the chosen operand=1 and the discarded operand=0. The condition is checked on the
old circuit's guarded values, with no comparisons of entire suffix computations. -/
def Readers.guarded {α : Type} (s : Readers α) (l r : Bool) (v : α → Bool) : Prop := match s with
  | .finish _ => True
  | .reader side g b rest =>
    (v g = true → v b = false → (if side then l else r) = true → (l && r) = true) ∧
    rest.guarded l r (fun z => z.elim (v g && ((l && r) || v b)) v)

theorem Readers.guarded_value {α} (s : Readers α) (l r : Bool) (v : α → Bool)
    (h : s.guarded l r v) :
    s.value (fun side => if side then l else r) v = s.value (fun _ => l && r) v := by
  induction s with
  | finish => rfl
  | reader side g b rest ih =>
    have equal : (v g && ((if side then l else r) || v b)) = (v g && ((l && r) || v b)) := by
      have hlocal := h.1
      cases side <;> cases l <;> cases r <;> cases hg : v g <;> cases hb : v b <;> simp_all
    simp only [Readers.value,equal]
    exact ih _ h.2

/-- One physical gate computes the common AND in the original layout. The rewritten
layout routes the two original operands independently to their chosen readers. -/
def Readers.original {α} (s : Readers α) (l r : α) : Net α :=
  .gate true l r (s.compile (fun _ => none) some)

def Readers.rerouted {α} (s : Readers α) (l r : α) : Net α :=
  s.compile (fun side => if side then l else r) id

theorem Readers.original_value {α} (s : Readers α) (l r : α) (v : α → Bool) :
    (s.original l r).value v = s.value (fun _ => v l && v r) v := by
  simp [Readers.original,Net.value,Readers.compile_value,bin]

theorem Readers.rerouted_value {α} (s : Readers α) (l r : α) (v : α → Bool) :
    (s.rerouted l r).value v = s.value (fun k => if k then v l else v r) v := by
  rw [Readers.rerouted,Readers.compile_value]
  congr 1
  funext k
  cases k <;> rfl

/-- Append an emitted program after an arbitrary existing physical prefix. -/
def attach {α} (n : Nat) (prefixGates : List Gate) (port : α → Nat) (s : Net α) : Circuit :=
  let D := s.emit (n+prefixGates.length) port
  ⟨prefixGates ++ D.gates,D.output⟩

def before (prefixGates : List Gate) {n : Nat} (x : Fin n → Bool) :=
  (⟨prefixGates,0⟩ : Circuit).wires (List.ofFn x)

private lemma wireCount (gs : List Gate) (bits : List Bool) :
    ((⟨gs,0⟩ : Circuit).wires bits).length = bits.length + gs.length := by
  induction gs generalizing bits with
  | nil => simp [Circuit.wires]
  | cons g gs ih =>
    change ((⟨gs,0⟩ : Circuit).wires (bits ++ [_])).length = _
    rw [ih]
    simp; omega

theorem attach_value {α} (n : Nat) (gs : List Gate) (port : α → Nat) (s : Net α)
    (bound : ∀ a, port a < n + gs.length) (x : Fin n → Bool) :
    circuitFun n (attach n gs port s) x = s.value (fun a => (before gs x).getD (port a) false) := by
  have len : (before gs x).length = n+gs.length := by simp [before,wireCount]
  have h := s.emit_spec (before gs x) port (fun a => len ▸ bound a)
  rw [len] at h
  simpa [attach,circuitFun,Circuit.eval,Circuit.wires,List.foldl_append,before] using h

theorem attach_size {α} (n : Nat) (gs : List Gate) (port : α → Nat) (s : Net α) :
    (attach n gs port s).size = gs.length + s.size := by
  change (gs ++ (s.emit _ _).gates).length = _
  rw [List.length_append]
  exact congrArg _ (s.emit_size _ _)

theorem attach_mono {α} (n : Nat) (gs : List Gate) (port : α → Nat) (s : Net α)
    (m : Monotone2 ⟨gs,0⟩) : Monotone2 (attach n gs port s) := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact m g h
  · exact s.emit_mono _ _ g h

/-- On true rows, selecting either operand can only increase monotone circuit values. On
false rows, the guarded reader condition implies equality at every exported reader port.
The suffix may reuse any number of reader outputs or original prefix wires. -/
theorem shared_gate_exchange {n : Nat} {α : Type} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gs : List Gate) (port : α → Nat) (s : Readers α) (l r : α)
    (bound : ∀ a, port a < n + gs.length) (m : Monotone2 ⟨gs,0⟩)
    (correct : circuitFun n (attach n gs port (s.original l r)) = graphFun G ∅)
    (guards : ∀ x : Fin n → Bool, graphFun G ∅ x = false →
      let v := fun a => (before gs x).getD (port a) false
      s.guarded (v l) (v r) v) :
    let C := attach n gs port (s.original l r)
    let D := attach n gs port (s.rerouted l r)
    Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size + 1 = C.size := by
  refine ⟨attach_mono n gs port _ m,?_,?_⟩
  · funext x
    let v := fun a => (before gs x).getD (port a) false
    have old := congrFun correct x
    rw [attach_value _ _ _ _ bound,Readers.original_value] at old
    rw [attach_value _ _ _ _ bound,Readers.rerouted_value]
    cases hx : graphFun G ∅ x with
    | false => exact (s.guarded_value (v l) (v r) v (guards x hx)).trans (old.trans hx)
    | true =>
      apply s.value_mono (fun k => ?_) (fun _ h => h) (old.trans hx)
      cases k <;> simp_all
  · simp [attach_size,Readers.original,Readers.rerouted,Net.size,Readers.compile_size,Nat.add_assoc]

/-- Thus a least circuit with this many-reader layout has an independent input on which
at least one proposed reader bypass introduces a new true value at its guarded output. -/
theorem optimal_forces_failed_guard {n : Nat} {α : Type} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gs : List Gate) (port : α → Nat) (s : Readers α) (l r : α)
    (bound : ∀ a, port a < n + gs.length) (m : Monotone2 ⟨gs,0⟩)
    (correct : circuitFun n (attach n gs port (s.original l r)) = graphFun G ∅)
    (optimum : IsMinimalMonoCircuit n (attach n gs port (s.original l r))) :
    ∃ x : Fin n → Bool, graphFun G ∅ x = false ∧
      let v := fun a => (before gs x).getD (port a) false
      ¬ s.guarded (v l) (v r) v := by
  by_contra! h
  obtain ⟨mono,eq,size⟩ := shared_gate_exchange G gs port s l r bound m correct
    (fun x hx => Classical.byContradiction (h x hx))
  have lower := optimum.2 _ mono (eq.trans correct.symm)
  omega

end PEqualNP.Research.GuardedReaders
