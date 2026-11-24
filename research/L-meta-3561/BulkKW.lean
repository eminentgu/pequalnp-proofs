import VerifiedCore

namespace PEqualNP.Research3561.BulkKW
open SignedReadOnceKW

/-- The candidate at bit i owns two pairs of cells, called A and B in the proof.
The four test rows are located in four consecutive blocks of stride n. -/
def masks (base n : Nat) (w : Sig) : Nat × Nat :=
  let pos₁ := w.1 >>> base
  let neg₁ := w.2 >>> base
  let pos₂ := w.1 >>> (base+n)
  let neg₂ := w.2 >>> (base+n)
  let neg₃ := w.2 >>> (base+2*n)
  let pos₄ := w.1 >>> (base+3*n)
  ((pos₁ ^^^ neg₁) ||| (pos₂ ^^^ neg₂),(pos₁ ^^^ neg₃) ||| (pos₄ ^^^ neg₂))

/-- First and second components mark candidate tests met by at least one wire.
The third marks a repeated A label, a repeated B label, or a label shared between A and B. -/
def scan (f : Sig → Nat × Nat) : List Sig → Nat × Nat × Nat
  | [] => (0,0,0)
  | w :: ws =>
    let (a,b) := f w
    let (x,y,bad) := scan f ws
    (a ||| x,b ||| y,bad ||| (a &&& x) ||| (b &&& y) ||| (a &&& b))

private theorem seenA {f : Sig → Nat × Nat} {w : List Sig} (i : Nat) (a : Sig) (ha : a ∈ w)
    (bitA : (f a).1.testBit i = true) : (scan f w).1.testBit i = true := by
  induction w with
  | nil => simp at ha
  | cons b bs ih =>
    rcases List.mem_cons.mp ha with rfl | mem
    · simp [scan,Nat.testBit_or,bitA]
    · simp [scan,Nat.testBit_or,ih mem]

private theorem seenB {f : Sig → Nat × Nat} {w : List Sig} (i : Nat) (a : Sig) (ha : a ∈ w)
    (bitB : (f a).2.testBit i = true) : (scan f w).2.1.testBit i = true := by
  induction w with
  | nil => simp at ha
  | cons b bs ih =>
    rcases List.mem_cons.mp ha with rfl | mem
    · simp [scan,Nat.testBit_or,bitB]
    · simp [scan,Nat.testBit_or,ih mem]

private def Unique (f : Sig → Bool) (w : List Sig) :=
  ∀ a ∈ w, ∀ b ∈ w, f a = true → f b = true → a = b

private theorem unique_cons {p : Sig → Bool} {a : Sig} {w : List Sig} (old : Unique p w)
    (apart : p a = true → ∀ b ∈ w, p b ≠ true) : Unique p (a::w) := by
  intro x hx y hy px py
  by_cases ex : x = a
  · subst x
    rcases List.mem_cons.mp hy with e | ym
    · exact e.symm
    · exact (apart px y ym py).elim
  · have xm := (List.mem_cons.mp hx).resolve_left ex
    rcases List.mem_cons.mp hy with e | ym
    · subst y
      exact (apart py x xm px).elim
    · exact old x xm y ym px py

theorem clean {f : Sig → Nat × Nat} {w : List Sig} {i : Nat}
    (ok : (scan f w).2.2.testBit i = false) :
    Unique (fun a => (f a).1.testBit i) w ∧ Unique (fun a => (f a).2.testBit i) w ∧
    ∀ a ∈ w, (f a).1.testBit i = true → (f a).2.testBit i ≠ true := by
  induction w with
  | nil => simp [Unique]
  | cons x ws ih =>
    simp only [scan,Nat.testBit_or,Nat.testBit_and,Bool.or_eq_false_iff] at ok
    obtain ⟨one,two,disjoint⟩ := ih ok.1.1.1
    refine ⟨unique_cons one ?_,unique_cons two ?_,?_⟩
    · intro yes y hy flag
      have hit := seenA i y hy flag
      simp [yes,hit] at ok
    · intro yes y hy flag
      have hit := seenB i y hy flag
      simp [yes,hit] at ok
    · intro y hy ya yb
      rcases List.mem_cons.mp hy with rfl|hy
      · simp [ya,yb] at ok
      · exact disjoint y hy ya yb

theorem xor_true {a b : Bool} (h : a ≠ b) : (a.xor b) = true := by
  cases a <;> cases b <;> simp_all

/-- Each clean candidate forces incompatible labels on the same mixed cell of a tiling. -/
theorem no_tiling {w : List Sig} {base n i : Nat} (hi : i < n) (bound : base+4*n ≤ 414)
    (ok : (scan (masks base n) w).2.2.testBit i = false) : ¬ Tiling w.toFinset := by
  rintro ⟨label,leg,rect⟩
  let r₁ : Fin 414 := ⟨base+i,by omega⟩
  let r₂ : Fin 414 := ⟨base+n+i,by omega⟩
  let r₃ : Fin 414 := ⟨base+2*n+i,by omega⟩
  let r₄ : Fin 414 := ⟨base+3*n+i,by omega⟩
  have belongs (p n : Fin 414) : label p n ∈ w := List.mem_toFinset.mp (leg p n).1
  have sep (p n : Fin 414) := xor_true (leg p n).2
  have ca (a : Sig) : (masks base n a).1.testBit i =
      ((bit true r₁ a).xor (bit false r₁ a) || (bit true r₂ a).xor (bit false r₂ a)) := by
    simp [masks,bit,r₁,r₂,Nat.testBit_or,Nat.testBit_xor,Nat.testBit_shiftRight,Nat.add_comm]
  have cb (a : Sig) : (masks base n a).2.testBit i =
      ((bit true r₁ a).xor (bit false r₃ a) || (bit true r₄ a).xor (bit false r₂ a)) := by
    simp [masks,bit,r₁,r₂,r₃,r₄,Nat.testBit_or,Nat.testBit_xor,Nat.testBit_shiftRight,Nat.add_comm]
  obtain ⟨one,two,apart⟩ := clean ok
  have h₁ : (masks base n (label r₁ r₁)).1.testBit i = true := by rw [ca]; simp [sep r₁ r₁]
  have h₂ : (masks base n (label r₂ r₂)).1.testBit i = true := by rw [ca]; simp [sep r₂ r₂]
  have h₃ : (masks base n (label r₁ r₃)).2.testBit i = true := by rw [cb]; simp [sep r₁ r₃]
  have h₄ : (masks base n (label r₄ r₂)).2.testBit i = true := by rw [cb]; simp [sep r₄ r₂]
  have ra := rect r₁ r₁ r₂ r₂ (one _ (belongs _ _) _ (belongs _ _) h₁ h₂)
  have rb := rect r₁ r₃ r₄ r₂ (two _ (belongs _ _) _ (belongs _ _) h₃ h₄)
  exact apart _ (belongs _ _) h₁ (by rwa [← ra,rb])

/-- All candidates are evaluated in parallel using three arbitrary-precision integers. -/
def excludes (base n : Nat) (w : List Sig) : Bool :=
  let mask := 2^n - 1
  decide ((scan (masks base n) w).2.2 &&& mask ≠ mask)

theorem missing_bit {n bits : Nat} (notAll : bits &&& (2^n-1) ≠ 2^n-1) :
    ∃ i < n, bits.testBit i = false := by
  by_contra! all
  apply notAll
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · simp [Nat.testBit_and,Nat.testBit_two_pow_sub_one,hi,all i hi]
  · simp [Nat.testBit_and,Nat.testBit_two_pow_sub_one,hi]

theorem excludes_sound {base n k t : Nat} {v : List Wire} (bound : base+4*n ≤ 414)
    (sat : v.length+t=k+1) (yes : excludes base n (sigsOf v) = true) : Impossible k t v := by
  intro m hm S τ rep run
  obtain ⟨nd,hs,_⟩ := rep
  subst S
  have card : (sigsOf v).toFinset.card = v.length := by rw [List.toFinset_card_of_nodup nd,sigsOf_length]
  have cap := (live_size run.live).2
  obtain ⟨i,hi,ok⟩ := missing_bit (of_decide_eq_true yes)
  exact no_tiling hi bound ok (signed_tiling_of_live run.live (by omega))

end PEqualNP.Research3561.BulkKW
