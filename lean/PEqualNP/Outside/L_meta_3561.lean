import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3561

-- The live-signal extraction and the 544 test pairs come from the public
-- Petersen graph certificates L-meta-1672 and L-meta-2913 (Josh and contributors).
namespace Core

abbrev Sig := Nat × Nat
def top : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def bnot (x : Nat) : Nat := x ^^^ top
def zero : Sig := (0, 0)
def one : Sig := (top, top)
def target : Sig := (top, 0)
def neg (a : Sig) : Sig := (bnot a.1, bnot a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1, a.2 ||| b.2) else (a.1 &&& b.1, a.2 &&& b.2)
def sep (d : Bool) (a : Sig) : Nat :=
  if d then a.1 ^^^ a.2 else a.1 &&& bnot a.2
def unionSep (d : Bool) : List Sig → Nat
  | [] => 0
  | a :: l => sep d a ||| unionSep d l
def Valid1 (x : Nat) : Prop := ∀ j, 544 ≤ j → x.testBit j = false
def Valid (a : Sig) : Prop := Valid1 a.1 ∧ Valid1 a.2
def proper (a : Sig) : Prop := Valid a ∧ a ≠ zero ∧ a ≠ one
lemma top_eq_pow : top = 2 ^ 272 * 2 ^ 272 - 1 := by decide
lemma pow_add_testBit (a b j : Nat) : (2 ^ a * 2 ^ b - 1).testBit j = decide (j < a + b) := by
  rw [← Nat.pow_add, Nat.testBit_two_pow_sub_one]
lemma testBit_top (j : Nat) : top.testBit j = decide (j < 544) := by
  rw [top_eq_pow]; exact pow_add_testBit 272 272 j
lemma testBit_bnot {x : Nat} (hx : Valid1 x) (j : Nat) :
    (bnot x).testBit j = if j < 544 then !(x.testBit j) else false := by
  simp only [bnot, Nat.testBit_xor, testBit_top]
  by_cases hj : j < 544
  · simp [hj]
  · simp [hj, hx j (by omega)]
lemma testBit_bnot_lt (x : Nat) {j : Nat} (hj : j < 544) :
    (bnot x).testBit j = !(x.testBit j) := by
  simp [bnot, Nat.testBit_xor, testBit_top, hj]
lemma valid1_zero : Valid1 0 := fun _ _ => Nat.zero_testBit _
lemma valid1_top : Valid1 top := fun j hj => by rw [testBit_top]; simp [show ¬ j < 544 by omega]
lemma valid1_bnot {x : Nat} (hx : Valid1 x) : Valid1 (bnot x) := fun j hj => by
  rw [testBit_bnot hx]; simp [show ¬ j < 544 by omega]
lemma valid1_and {x y : Nat} (hx : Valid1 x) : Valid1 (x &&& y) := fun j hj => by
  rw [Nat.testBit_and, hx j hj]; rfl
lemma valid1_or {x y : Nat} (hx : Valid1 x) (hy : Valid1 y) : Valid1 (x ||| y) := fun j hj => by
  rw [Nat.testBit_or, hx j hj, hy j hj]; rfl
lemma valid1_xor {x y : Nat} (hx : Valid1 x) (hy : Valid1 y) : Valid1 (x ^^^ y) := fun j hj => by
  rw [Nat.testBit_xor, hx j hj, hy j hj]; rfl
lemma lt_pow_mul_testBit {a b x j : Nat} (hx : x < 2 ^ a * 2 ^ b) (hj : a + b ≤ j) :
    x.testBit j = false := by
  rw [← Nat.pow_add] at hx
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hj))
lemma valid1_of_le_top {x : Nat} (h : x ≤ top) : Valid1 x := fun j hj => by
  have hlt : x < 2 ^ 272 * 2 ^ 272 := by
    have hp : 0 < 2 ^ 272 * 2 ^ 272 := by decide
    rw [top_eq_pow] at h; omega
  exact lt_pow_mul_testBit hlt hj
lemma valid_zero : Valid zero := ⟨valid1_zero, valid1_zero⟩
lemma valid_one : Valid one := ⟨valid1_top, valid1_top⟩
lemma valid_target : Valid target := ⟨valid1_top, valid1_zero⟩
lemma valid_neg {a : Sig} (ha : Valid a) : Valid (neg a) := ⟨valid1_bnot ha.1, valid1_bnot ha.2⟩
lemma valid_bin {d : Bool} {a b : Sig} (ha : Valid a) (hb : Valid b) : Valid (bin d a b) := by
  cases d
  · exact ⟨valid1_and ha.1, valid1_and ha.2⟩
  · exact ⟨valid1_or ha.1 hb.1, valid1_or ha.2 hb.2⟩
lemma valid_sep {d : Bool} {a : Sig} (ha : Valid a) : Valid1 (sep d a) := by
  cases d
  · exact valid1_and ha.1
  · exact valid1_xor ha.1 ha.2
lemma valid_unionSep {d : Bool} {v : List Sig} (hv : ∀ a ∈ v, Valid a) : Valid1 (unionSep d v) := by
  induction v with
  | nil => exact valid1_zero
  | cons a l ih =>
    exact valid1_or (valid_sep (hv a (by simp))) (ih (fun x hx => hv x (by simp [hx])))
lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d
  · simp [bin, Nat.and_comm]
  · simp [bin, Nat.or_comm]
lemma bin_laws {a : Sig} (ha : Valid a) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  obtain ⟨p, n⟩ := a
  obtain ⟨hp, hn⟩ := ha
  have land_top {x : Nat} (hx : Valid1 x) : x &&& top = x := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_and, testBit_top]
    by_cases hj : j < 544 <;> simp [hj]
    exact hx j (by omega)
  have lor_top {x : Nat} (hx : Valid1 x) : x ||| top = top := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_or, testBit_top]
    by_cases hj : j < 544 <;> simp [hj]
    exact hx j (by omega)
  simp [bin, one, zero, land_top hp, land_top hn, lor_top hp, lor_top hn]
lemma neg_laws : neg zero = one ∧ neg one = zero := by
  have h1 : bnot 0 = top := by simp [bnot]
  have h2 : bnot top = 0 := by simp [bnot]
  exact ⟨Prod.ext h1 h1, Prod.ext h2 h2⟩
lemma target_proper : proper target :=
  ⟨valid_target, by unfold target zero top; decide, by unfold target one top; decide⟩
lemma testBit_land (x y i : Nat) : (Nat.land x y).testBit i = (x.testBit i && y.testBit i) := Nat.testBit_and x y i
lemma testBit_lor (x y i : Nat) : (Nat.lor x y).testBit i = (x.testBit i || y.testBit i) := Nat.testBit_or x y i
lemma testBit_lxor (x y i : Nat) : (Nat.xor x y).testBit i = (x.testBit i != y.testBit i) := by
  simp [bne]
abbrev Cov := Nat × Nat × Nat
def ValidCov (c : Cov) : Prop :=
  Valid1 c.1 ∧ Valid1 c.2.1 ∧ Valid1 c.2.2 ∧
  (∀ i, c.2.1.testBit i = true → c.1.testBit i = true) ∧
  (∀ i, c.2.2.testBit i = true → c.1.testBit i = true)
def covAdd (z : Nat) (c : Cov) : Cov :=
  (Nat.lor z c.1,
   Nat.land (Nat.xor z c.1) (Nat.lor z c.2.1),
   Nat.xor c.2.2 (Nat.land z (Nat.xor c.2.2 c.2.1)))
def coverage (d : Bool) (v : List Sig) : Cov :=
  v.foldr (fun a c => covAdd (sep d a) c) (0, 0, 0)
def takeOne (c : Cov) (a : Nat) : Nat := Nat.xor c.1 (Nat.land c.2.1 a)
def takeTwo (c : Cov) (a b : Nat) : Nat :=
  Nat.xor c.1 (Nat.lor (Nat.land c.2.1 (Nat.lor a b)) (Nat.land c.2.2 (Nat.land a b)))
lemma validCov_zero : ValidCov (0, 0, 0) :=
  ⟨valid1_zero, valid1_zero, valid1_zero, fun _ h => by simp at h, fun _ h => by simp at h⟩
lemma validCov_add {z : Nat} {c : Cov} (hz : Valid1 z) (hc : ValidCov c) : ValidCov (covAdd z c) := by
  refine ⟨valid1_or hz hc.1, valid1_and (valid1_xor hz hc.1), valid1_xor hc.2.2.1 (valid1_and hz), ?_, ?_⟩
  · intro i h; have h1 := hc.2.2.2.1 i
    simp only [covAdd, testBit_land, testBit_lor, testBit_lxor] at h ⊢
    revert h h1; cases z.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> simp
  · intro i h; have h1 := hc.2.2.2.1 i; have h2 := hc.2.2.2.2 i
    simp only [covAdd, testBit_land, testBit_lor, testBit_lxor] at h ⊢
    revert h h1 h2; cases z.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;>
      cases c.2.2.testBit i <;> simp
lemma validCov_coverage (d : Bool) {v : List Sig} (hv : ∀ a ∈ v, Valid a) : ValidCov (coverage d v) := by
  induction v with
  | nil => exact validCov_zero
  | cons a l ih => exact validCov_add (valid_sep (hv a (by simp))) (ih (fun x hx => hv x (by simp [hx])))
lemma cov_one {c : Cov} {a : Nat} (hc : ValidCov c) : takeOne (covAdd a c) a = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := hc.2.2.2.1 i
  simp only [takeOne, covAdd, testBit_land, testBit_lor, testBit_lxor]
  revert h1; cases a.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> simp
lemma cov_two {c : Cov} {a b : Nat} (hc : ValidCov c) :
    takeTwo (covAdd a (covAdd b c)) a b = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := hc.2.2.2.1 i; have h2 := hc.2.2.2.2 i
  simp only [takeTwo, covAdd, testBit_land, testBit_lor, testBit_lxor]
  revert h1 h2; cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
    cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> simp
lemma cov_two_unique_disj {c : Cov} {a b : Nat} (hc : ValidCov c) :
    Nat.land (Nat.land (covAdd a (covAdd b c)).2.1 a) b = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := hc.2.2.2.1 i
  simp only [covAdd, testBit_land, testBit_lor, testBit_lxor, Nat.zero_testBit]
  revert h1; cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
    cases c.2.1.testBit i <;> simp
lemma covAdd_swap {c : Cov} {a b : Nat} (hc : ValidCov c) :
    covAdd a (covAdd b c) = covAdd b (covAdd a c) := by
  have h1 := hc.2.2.2.1; have h2 := hc.2.2.2.2
  refine Prod.ext (Nat.eq_of_testBit_eq fun i => ?_)
    (Prod.ext (Nat.eq_of_testBit_eq fun i => ?_) (Nat.eq_of_testBit_eq fun i => ?_))
  · simp only [covAdd, testBit_lor]; cases a.testBit i <;> cases b.testBit i <;> rfl
  · have h1i := h1 i; simp only [covAdd, testBit_land, testBit_lor, testBit_lxor]
    revert h1i; cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> simp
  · have h1i := h1 i; have h2i := h2 i; simp only [covAdd, testBit_land, testBit_lor, testBit_lxor]
    revert h1i h2i; cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> simp
lemma cov_perm (d : Bool) {l r : List Sig} (hl : ∀ a ∈ l, Valid a) (h : l.Perm r) :
    coverage d l = coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih =>
    exact congrArg (covAdd (sep d a)) (ih (fun x hx => hl x (by simp [hx])))
  | swap a b t =>
    exact covAdd_swap (validCov_coverage d (fun x hx => hl x (by simp [hx])))
  | trans h1 _ ih1 ih2 =>
    exact (ih1 hl).trans (ih2 (fun x hx => hl x (h1.mem_iff.2 hx)))
lemma cov_union (d : Bool) (v : List Sig) : (coverage d v).1 = unionSep d v := by
  induction v with
  | nil => rfl
  | cons a v ih => change sep d a ||| (coverage d v).1 = sep d a ||| unionSep d v; rw [ih]
def dropped (del v : List Sig) : List Sig := v.filter (fun x => !(del.contains x))
def keepOf (U : Finset Sig) (del : List Sig) : List Sig := del.filter (fun a => decide (a ∈ U))
lemma edit_list {v del : List Sig} {U : Finset Sig}
    (hv : v.Nodup) (hd : del.Nodup) (he : v.toFinset = del.toFinset ∪ U) :
    (keepOf U del ++ dropped del v).Nodup ∧ (keepOf U del ++ dropped del v).toFinset = U := by
  have memv (x : Sig) : x ∈ v ↔ x ∈ del ∨ x ∈ U := by
    rw [← List.mem_toFinset, he]; simp
  constructor
  · rw [List.nodup_append]
    refine ⟨hd.filter _, hv.filter _, ?_⟩
    intro a ha b hb eq; subst b
    simp [keepOf] at ha; simp [dropped] at hb; exact hb.2 ha.1
  · ext x
    simp only [List.mem_toFinset, List.mem_append, List.mem_filter, keepOf, dropped,
      decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, memv]
    by_cases h : x ∈ del <;> simp_all
lemma recover_perm (del v : List Sig) (hv : v.Nodup) (hd : del.Nodup)
    (hs : ∀ x ∈ del, x ∈ v) : v.Perm (del ++ dropped del v) := by
  apply List.perm_of_nodup_nodup_toFinset_eq hv
  · rw [List.nodup_append]
    refine ⟨hd, hv.filter _, ?_⟩
    intro a ha b hb e; subst b; simp [dropped] at hb; exact hb.2 ha
  · ext x
    simp only [List.mem_toFinset, List.mem_append, dropped, List.mem_filter, Bool.not_eq_true',
      List.contains_eq_mem, decide_eq_false_iff_not]
    by_cases h : x ∈ del <;> simp_all
lemma one_rest (d : Bool) {v : List Sig} {a : Sig} (hv : v.Nodup) (hval : ∀ x ∈ v, Valid x)
    (ha : a ∈ v) :
    v.length - 1 = (dropped [a] v).length ∧
      takeOne (coverage d v) (sep d a) = unionSep d (dropped [a] v) := by
  have p := recover_perm [a] v hv (by simp) (by simpa using ha)
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d hval p]
    have hrest : ∀ x ∈ dropped [a] v, Valid x := fun x hx =>
      hval x (List.mem_of_mem_filter hx)
    exact (cov_one (validCov_coverage d hrest)).trans (cov_union d _)
lemma two_rest (d : Bool) {v : List Sig} {a b : Sig} (hv : v.Nodup) (hval : ∀ x ∈ v, Valid x)
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    v.length - 2 = (dropped [a, b] v).length ∧
      takeTwo (coverage d v) (sep d a) (sep d b) = unionSep d (dropped [a, b] v) := by
  have p := recover_perm [a, b] v hv (by simp [hab]) (by simp [ha, hb])
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d hval p]
    have hrest : ∀ x ∈ dropped [a, b] v, Valid x := fun x hx =>
      hval x (List.mem_of_mem_filter hx)
    exact (cov_two (validCov_coverage d hrest)).trans (cov_union d _)
lemma two_rest_disj (d : Bool) {v : List Sig} {a b : Sig} (hv : v.Nodup) (hval : ∀ x ∈ v, Valid x)
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    Nat.land (Nat.land (coverage d v).2.1 (sep d a)) (sep d b) = 0 := by
  have p := recover_perm [a, b] v hv (by simp [hab]) (by simp [ha, hb])
  rw [cov_perm d hval p]
  exact cov_two_unique_disj (validCov_coverage d (fun x hx => hval x (List.mem_of_mem_filter hx)))
inductive Live : Nat → Nat → Finset Sig → Prop
  | stop : Live 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k + 1) (t + 1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k + 1) t (insert a (insert b U))
lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop => simpa using target_proper
  | unary ha _ _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha, hb, fun a h => ih a (Finset.mem_insert_of_mem h)⟩
lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card + t ≤ k + 1 := by
  induction h with
  | stop => simp
  | @unary k t U a _ hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega, by omega⟩
  | @binary k t U a b d _ _ _ hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega, by omega⟩
lemma sep_unary (t : Nat) {a : Sig} (ha : Valid a) (i : Nat) (hi : i < 544)
    (h : (sep (decide (0 < t)) (neg a)).testBit i = true) :
    (sep true a).testBit i = true := by
  cases ht : decide (0 < t)
  · simp only [sep, neg, ht, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and,
      Nat.testBit_xor, testBit_bnot (valid1_bnot ha.2), testBit_bnot ha.1, testBit_bnot ha.2,
      hi] at h ⊢
    cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;> simp [hx, hy] at h ⊢
  · simp only [sep, neg, ht, ite_true, Nat.testBit_xor,
      testBit_bnot ha.1, testBit_bnot ha.2, hi] at h ⊢
    cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;> simp [hx, hy] at h ⊢
lemma sep_binary (t d : Bool) {a b : Sig} (_ha : Valid a) (_hb : Valid b) (i : Nat) (hi : i < 544)
    (h : (sep t (bin d a b)).testBit i = true) :
    (sep t a).testBit i = true ∨ (sep t b).testBit i = true := by
  cases t <;> cases d <;>
    simp only [sep, bin, Bool.false_eq_true, ite_true, ite_false, Nat.testBit_xor,
      Nat.testBit_and, Nat.testBit_or, testBit_bnot_lt _ hi] at h ⊢ <;>
    revert h <;>
    cases a.1.testBit i <;> cases a.2.testBit i <;>
    cases b.1.testBit i <;> cases b.2.testBit i <;> simp
lemma sep_weaken (t : Nat) {a : Sig} (ha : Valid a) (i : Nat) (hi : i < 544)
    (h : (sep (decide (0 < t)) a).testBit i = true) : (sep true a).testBit i = true := by
  cases ht : decide (0 < t)
  · simp only [sep, ht, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and,
      Nat.testBit_xor, testBit_bnot ha.2, hi] at h ⊢
    cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;> simp [hx, hy] at h ⊢
  · simpa [ht] using h
lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 544) :
    ∃ a ∈ S, (sep (decide (0 < t)) a).testBit i = true := by
  induction h with
  | stop =>
    refine ⟨target, by simp, ?_⟩
    simp [sep, target, Nat.testBit_and, testBit_top, testBit_bnot valid1_zero, hi]
  | unary ha _ tail ih =>
    obtain ⟨x, hx, h⟩ := ih
    simp only [Finset.mem_insert] at hx
    simp only [Nat.zero_lt_succ, decide_true]
    rcases hx with rfl | hU
    · exact ⟨_, Finset.mem_insert_self _ _, sep_unary _ ha.1 i hi h⟩
    · exact ⟨x, Finset.mem_insert_of_mem hU,
        sep_weaken _ (live_proper tail x (Finset.mem_insert_of_mem hU)).1 i hi h⟩
  | binary ha hb _ _ _ ih =>
    obtain ⟨x, hx, h⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl | hU
    · rcases sep_binary _ _ ha.1 hb.1 i hi h with h | h
      · exact ⟨_, Finset.mem_insert_self _ _, h⟩
      · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h⟩
    · exact ⟨x, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU), h⟩
lemma mem_unionSep (d : Bool) (v : List Sig) (i : Nat) :
    (unionSep d v).testBit i = true ↔ ∃ a ∈ v, (sep d a).testBit i = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a v ih =>
    simp only [unionSep, Nat.testBit_or, Bool.or_eq_true, ih, List.mem_cons, exists_eq_or_imp]
lemma live_cover {k t S} {v : List Sig} (h : Live k t S) (he : v.toFinset = S) :
    unionSep (decide (0 < t)) v = top := by
  have hv : ∀ a ∈ v, Valid a := fun a ha => (live_proper h a (he ▸ List.mem_toFinset.mpr ha)).1
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_top]
  by_cases hi : i < 544
  · simp only [hi, decide_true]
    obtain ⟨a, hm, ha⟩ := live_sep h i hi
    exact (mem_unionSep _ _ _).2 ⟨a, List.mem_toFinset.mp (he.symm ▸ hm), ha⟩
  · simp only [hi, decide_false]
    exact valid_unionSep hv i (by omega)
lemma union_append (d : Bool) (l r : List Sig) :
    unionSep d (l ++ r) = unionSep d l ||| unionSep d r := by
  induction l with
  | nil => simp [unionSep]
  | cons a l ih => simp [unionSep, ih, Nat.or_assoc]
open PEqualNP.CircuitLowerBounds
def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero
def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w
lemma valid_getD {w : List Sig} (hw : ∀ a ∈ w, Valid a) (i : Nat) : Valid (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact valid_zero
  | some a => exact hw a (List.mem_of_getElem? h)
lemma gv_valid {w : List Sig} (hw : ∀ a ∈ w, Valid a) (g : Gate) : Valid (gv w g) := by
  obtain ⟨o, l⟩ := g
  cases o with
  | and =>
    change Valid ((l.map (fun i => w.getD i zero)).foldr (bin false) one)
    induction l with
    | nil => exact valid_one
    | cons i l ih => exact valid_bin (valid_getD hw i) ih
  | or =>
    change Valid ((l.map (fun i => w.getD i zero)).foldr (bin true) zero)
    induction l with
    | nil => exact valid_zero
    | cons i l ih => exact valid_bin (valid_getD hw i) ih
  | not =>
    cases l with
    | nil => exact valid_neg valid_zero
    | cons i _ => exact valid_neg (valid_getD hw i)
  | mod _ => exact valid_zero
  | maj => exact valid_zero
def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬ proper v
lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.2.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)
lemma operand_cases {w : List Sig} {a : Sig} (hva : Valid a) (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hva, hz, ho⟩), hva, hz, ho⟩)
def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)
lemma bin_rep {w a b} (d : Bool) (hva : Valid a) (hvb : Valid b)
    (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.2.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2.2 rfl)
  obtain ⟨a1, a0, az, ao, aa, aa'⟩ := bin_laws hva
  obtain ⟨b1, b0, bz, bo, bb, bb'⟩ := bin_laws hvb
  rcases operand_cases hva ha with rfl | rfl | ⟨ham, hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hvb hb with rfl | rfl | ⟨hbm, hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a = b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d, a, b, ham, hbm, hap, hbp, he, rfl⟩)
lemma gate_rep {w : List Sig} (hw : ∀ a ∈ w, Valid a) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  obtain ⟨ho, hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.2.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2.2 rfl)
  have nx (a : Sig) (hva : Valid a) (ha : represented w a) :
      represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases hva ha with rfl | rfl | ⟨hm, hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a, hm, hp, rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ valid_zero rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
          (bin_laws (valid_getD hw i)).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
          (bin_laws (valid_getD hw i)).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (valid_getD hw i) (get_rep w i)
    | cons j l =>
      cases l with
      | cons _ _ => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
            (bin_laws (valid_getD hw j)).1] using
            bin_rep false (valid_getD hw i) (valid_getD hw j) (get_rep w i) (get_rep w j)
        · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
            (bin_laws (valid_getD hw j)).2.1] using
            bin_rep true (valid_getD hw i) (valid_getD hw j) (get_rep w i) (get_rep w j)
        · exact nx _ (valid_getD hw i) (get_rep w i)
lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' t' S', k' ≤ k + 1 ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, t, S, by omega, h, ?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a, ha, hp', eq⟩ | ⟨d, a, b, ha, hb, pa, pb, hab, eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv; obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_, _, _, Nat.le_refl _, Live.unary hp' hf ht, by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv; obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_, _, _, Nat.le_refl _, Live.binary pa pb hab hf ht,
          by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, t, S, by omega, h, ?_⟩
    intro a ha; have hn : a ≠ z := fun hh => hm (hh ▸ ha); simpa [hn] using sub a ha
lemma extract (gs : List Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0, 0, {target}, by simp, Live.stop, by simpa [execute] using hout⟩
  | cons g gs ih =>
    have hw' : ∀ a ∈ w ++ [gv w g], Valid a := by
      intro a ha; rcases List.mem_append.mp ha with ha | ha
      · exact hw a ha
      · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
    obtain ⟨k, t, S, hk, ht, hs⟩ := ih (w ++ [gv w g]) hw' (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l, u, T, hl, hu, hT⟩ := pull_gate ht (gate_rep hw g (legal g (by simp))) hs
    exact ⟨l, u, T, by simp; omega, hu, hT⟩
def bit (side : Bool) (i : Fin 544) (a : Sig) : Bool :=
  (if side then a.1 else a.2).testBit i.val
lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit, zero]
lemma bit_one (s i) : bit s i one = true := by
  cases s <;> simp [bit, one, testBit_top, i.isLt]
lemma bit_neg (s i) {a : Sig} (ha : Valid a) : bit s i (neg a) = !(bit s i a) := by
  cases s
  · simp [bit, neg, testBit_bnot ha.2, i.isLt]
  · simp [bit, neg, testBit_bnot ha.1, i.isLt]
lemma bit_bin (s i d) (a b : Sig) : bit s i (bin d a b) =
    (if d then bit s i a || bit s i b else bit s i a && bit s i b) := by
  cases s <;> cases d <;> simp [bit, bin, Nat.testBit_and, Nat.testBit_or]
lemma b_read (s i) (w : List Sig) (j : Nat) :
    (w.map (bit s i)).getD j false = bit s i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _ _).symm
  | some a => rfl
lemma run_bit (s i) (g : Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    bit s i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit s i)).getD j false) := by
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _ _
    | cons a l ih =>
      change bit s i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _ _
    | cons a l ih =>
      change bit s i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) || x) ih
  · cases l with
    | nil => exact (bit_neg s i valid_zero).trans (by rw [bit_zero]; rfl)
    | cons a l => exact bit_neg s i (valid_getD hw a)
lemma execute_bits (gs : List Gate) (s i) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit s i) =
    gs.foldl (fun (l : List Bool) g => l ++ [g.op.eval (g.inputs.map fun j => l.getD j false)])
      (w.map (bit s i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hw' : ∀ a ∈ w ++ [gv w g], Valid a := by
      intro a ha; rcases List.mem_append.mp ha with ha | ha
      · exact hw a ha
      · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
    change (execute gs (w ++ [gv w g])).map _ = _
    rw [ih _ hw' (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons, List.map_append, List.map_singleton, run_bit s i g w hw (hg g (by simp))]
def raw0 : Sig := (0xd00840601f4421818078000a2129b51a00c4000000000000000003fffffc000000003ffc210fe00847f007e01f83e01107e03e042084423f0fc3c08220842122287e3e0f, 0xd00840601f402101006900003025800fc0015115115115115115115115115115115115100007e00003f003e00f83e00003e01e000000001f0fc3c00000000000003e3e07)
def raw1 : Sig := (0x22711003e089dc400f86503046564050c10c000000000000003ffc000000000003ffffffe0f82017c010fc20208423f0fc21e208410884411044517e1f805f05e7c20279, 0x22711003e089c4400c80f0f0464001f0000208e08e08e08e08e08e08e08e08e08e08e08fe0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038)
def raw2 : Sig := (0xd08e898c4f73b366313c010002406001c218000000000003ffc000000000003fffffc000421043f883ff880041084422084244fc027c3e022ffc0f84010be21e40847fd0, 0xd08c898c0f4232200114000180106603c000c50c50c50c50c50c50c50c50c50c50c50c50000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0)
def raw3 : Sig := (0x2e70710c3a98468430e9001600840aa50430000000003ffc000000000003fffffc00000084208421082110448ffc0044fffe00109f90089ff08802085ffc800897ffc480, 0x2610200030984084302900000006007c00001a41a41a41a41a41a41a41a41a41a41a41a400000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000)
def raw4 : Sig := (0x9a73810c4269c604311a0cc31b88fae4060000000000000000000003fffffc000000003ff0101fffc400083f21081ff1084087fe4003fe441008fffe210001ff9088802, 0x9a71810c0269c604316f0fe07987f800002a4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000)
def raw5 : Sig := (0xc521aa3f0052e6a8fc00fa61100170002883ffc003ffc000000003ffc0000000000000010842084210822109042108882108917fffffc00802010fffffffffe000101004, 0x421a21f001086a0b000f00000007800000006c06c06c06c06c06c06c06c06c06c06c06c0000000000000000000000000000007fffffc00000000fffffffffe000000000)
def raw6 : Sig := (0xdd0607e081fc081f82030480cc1600401100003ffc000000003ffc0000000000000000021084108421044213ffffff004001007ffffffffffffff0100400040102000020, 0xdd0207e00174080e82030000081f800000003703703703703703703703703703703703700000000000000003fffffe000000007ffffffffffffff0000000000000000000)
def raw7 : Sig := (0x3d9a469100a4491a44033300060000000a00000003ffc003ffc000000000000000000003ffffff0002080003ffffffffffffffa108211000041004208821085000002100, 0x2912440000a4491a44030f000fe000000003383383383383383383383383383383383383fffffe0000000003ffffffffffffff8000000000000000000000000000000000)
def raw8 : Sig := (0x22d5cc423103113108c4ccf3980000003403fffffc003ffc000000000000000000000003fffffffffffffffe084210008210004210422110882228411042108004210000, 0xc448000003111108c40ffff00000000003c03c03c03c03c03c03c03c03c03c03c03c03fffffffffffffffc000000000000000000000000000000000000000000000000)
def raw : List Sig := [raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7, raw8]
def sample (s : Bool) (i : Fin 544) (j : Fin 9) : Bool :=
  bit s i (raw.getD j.val zero)
def edgeF (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
set_option maxRecDepth 20000 in
lemma sample_ok : ∀ (s : Bool) (i : Fin 544), edgeF (sample s i) = s := by decide +kernel
lemma raw_id : List.ofFn (fun j : Fin 9 => raw.getD j.val zero) = raw := rfl
lemma sample_list (s i) : List.ofFn (sample s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 9 => raw.getD j.val zero)).map (bit s i) := by
      rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]
lemma raw_lt : raw.all (fun a => decide (a.1 ≤ top ∧ a.2 ≤ top)) = true := by decide +kernel
lemma raw_valid : ∀ a ∈ raw, Valid a := by
  intro a ha
  have h := of_decide_eq_true (List.all_eq_true.mp raw_lt a ha)
  exact ⟨valid1_of_le_top h.1, valid1_of_le_top h.2⟩

def encoded (x : Fin 9 → Bool) : List Bool :=
  List.ofFn (Function.update x 4 false) ++ [x 0 || x 4, x 4 || x 1]

def bank : List Sig := [raw0,raw1,raw2,raw3,zero,raw5,raw6,raw7,raw8,
  bin true raw0 raw4,bin true raw4 raw1]

def signals : List Sig := [raw0,raw1,raw2,raw3,raw5,raw6,raw7,raw8,
  bin true raw0 raw4,bin true raw4 raw1]

lemma validOfBound {w : List Sig} (h : w.all (fun a => decide (a.1 ≤ top ∧ a.2 ≤ top)) = true) :
    ∀ a ∈ w, Valid a := by
  intro a ha
  have hb := of_decide_eq_true ((List.all_eq_true.mp h) a ha)
  exact ⟨valid1_of_le_top hb.1, valid1_of_le_top hb.2⟩
lemma bankValid : ∀ a ∈ bank, Valid a := validOfBound (by decide +kernel)
lemma signalValid : ∀ a ∈ signals, Valid a := validOfBound (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma bankMaps : ∀ (s : Bool) (i : Fin 544), bank.map (bit s i) = encoded (sample s i) := by
  decide +kernel
lemma everySignal : signals.all (fun a => unionSep true (signals.erase a) != top) = true := by decide +kernel
lemma necessarySignals {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ signals) : signals.toFinset = S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_, hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp everySignal a hr
  have cov : unionSep true (signals.erase a) = top := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [testBit_top]
    by_cases hi : i < 544
    · simp only [hi, decide_true]
      obtain ⟨b, hb, h⟩ := live_sep l i hi
      have ba : b ≠ a := fun he => hn (he ▸ hb)
      have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
      exact (mem_unionSep true _ _).2 ⟨b, hm, sep_weaken _ (live_proper l b hb).1 i hi h⟩
    · simp only [hi, decide_false]
      exact valid_unionSep (fun x hx => signalValid x (List.mem_of_mem_erase hx)) i (by omega)
  simp [cov] at fail
lemma execute_valid (gs : List Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a) :
    ∀ a ∈ execute gs w, Valid a := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    apply ih (w ++ [gv w g])
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hw a ha
    · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
lemma bankTarget (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 9 → Bool, C.eval (encoded x) = edgeF x) : target ∈ execute C.gates bank := by
  let w := execute C.gates bank
  have hwv : ∀ a ∈ w, Valid a := execute_valid C.gates bank bankValid
  have hproj (s : Bool) (i : Fin 544) : bit s i (w.getD C.output zero) = s := by
    rw [← b_read]
    change ((execute C.gates bank).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ bankValid (fun g hg => (h g hg).1)]
    have eq := he (sample s i)
    rw [← bankMaps, sample_ok] at eq
    exact eq
  have hvout : Valid (w.getD C.output zero) := valid_getD hwv C.output
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply Nat.eq_of_testBit_eq; intro i
      rw [target, testBit_top]
      by_cases hi : i < 544
      · simpa [bit, hi] using hproj true ⟨i, hi⟩
      · rw [hvout.1 i (by omega)]; simp [hi]
    · apply Nat.eq_of_testBit_eq; intro i
      by_cases hi : i < 544
      · simpa [bit, target] using hproj false ⟨i, hi⟩
      · rw [hvout.2 i (by omega), target]; exact (Nat.zero_testBit i).symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

theorem extractedBank (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 9 → Bool, C.eval (encoded x) = edgeF x) :
    ∃ k t, k ≤ C.size ∧ Live k t signals.toFinset ∧ t + 9 ≤ k := by
  obtain ⟨k,t,S,hk,run,sub⟩ := extract C.gates bank bankValid legal (bankTarget C legal computes)
  have eq : signals.toFinset = S := necessarySignals run (by
    intro a ha
    have hb := sub a ha
    have positive := (live_proper run a ha).2.1
    simpa [signals,bank,List.mem_cons,positive] using hb)
  subst S
  have bound := (live_size run).2
  have card : signals.toFinset.card = 10 := by decide +kernel
  rw [card] at bound
  exact ⟨k,t,hk,run,by omega⟩

end Core

namespace Core
open PEqualNP.CircuitLowerBounds
inductive Tag where
  | tNone
  | tDeg3
  | tSpec0
  | tSpec1
  deriving DecidableEq, BEq
instance : LawfulBEq Tag where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | contradiction
  rfl {a} := by cases a <;> rfl
abbrev Wire := Sig × Tag
def Tag.toNat : Tag → Nat
  | .tNone => 0
  | .tDeg3 => 1
  | .tSpec0 => 2
  | .tSpec1 => 3
def tagOfNat : Nat → Tag
  | 0 => .tNone
  | 1 => .tDeg3
  | 2 => .tSpec0
  | _ => .tSpec1
def updUnaryTag (τ : Sig → Tag) (a : Sig) (x : Sig) : Tag :=
  if x = neg a then (if τ a = .tDeg3 then .tSpec1 else .tNone) else τ x
def updAndTag (τ : Sig → Tag) (a b : Sig) (x : Sig) : Tag :=
  if x = bin false a b then (if τ a = .tDeg3 ∨ τ b = .tDeg3 then .tSpec0 else .tNone) else τ x
def updOrTag (τ : Sig → Tag) (a b : Sig) (x : Sig) : Tag :=
  if x = bin true a b then .tNone
  else if x = a ∧ τ a = .tDeg3 then .tSpec0
  else if x = b ∧ τ b = .tDeg3 then .tSpec0
  else τ x
inductive TRestricted : Nat → Nat → Finset Sig → (Sig → Tag) → Prop
  | stop {τ} : TRestricted 0 0 {target} τ
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} {τ : Sig → Tag}
      (ha : proper a) (hf : neg a ∉ insert a U)
      (hr1 : τ a ≠ .tSpec0 ∧ τ a ≠ .tSpec1)
      (hr2 : τ a = .tDeg3 → a ∉ U)
      (tail : TRestricted k t (insert (neg a) U) (updUnaryTag τ a)) :
      TRestricted (k + 1) (t + 1) (insert a U) τ
  | binaryAnd {k t : Nat} {U : Finset Sig} {a b : Sig} {τ : Sig → Tag}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hf : bin false a b ∉ insert a (insert b U))
      (hra : τ a ≠ .tSpec0 ∧ (τ a ≠ .tNone → a ∉ U))
      (hrb : τ b ≠ .tSpec0 ∧ (τ b ≠ .tNone → b ∉ U))
      (tail : TRestricted k t (insert (bin false a b) U) (updAndTag τ a b)) :
      TRestricted (k + 1) t (insert a (insert b U)) τ
  | binaryOr {k t : Nat} {U : Finset Sig} {a b : Sig} {τ : Sig → Tag}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hf : bin true a b ∉ insert a (insert b U))
      (hra : τ a ≠ .tSpec1 ∧ (τ a = .tSpec0 → a ∉ U))
      (hrb : τ b ≠ .tSpec1 ∧ (τ b = .tSpec0 → b ∉ U))
      (tail : TRestricted k t (insert (bin true a b) U) (updOrTag τ a b)) :
      TRestricted (k + 1) t (insert a (insert b U)) τ
lemma TRestricted.live {k t S τ} (h : TRestricted k t S τ) : Live k t S := by
  induction h with
  | stop => exact Live.stop
  | unary ha hf _ _ _ ih => exact Live.unary ha hf ih
  | binaryAnd ha hb hab hf _ _ _ ih => exact Live.binary ha hb hab hf ih
  | binaryOr ha hb hab hf _ _ _ ih => exact Live.binary ha hb hab hf ih
def sigsOf (v : List Wire) : List Sig := v.map Prod.fst
def Represents (v : List Wire) (S : Finset Sig) (τ : Sig → Tag) : Prop :=
  (sigsOf v).Nodup ∧ (sigsOf v).toFinset = S ∧ ∀ w ∈ v, w.2 = τ w.1
def droppedW (del : List Sig) (v : List Wire) : List Wire :=
  v.filter (fun w => !(del.contains w.1))
def unionSepW (d : Bool) : List Wire → Nat
  | [] => 0
  | w :: l => sep d w.1 ||| unionSepW d l
def coverageW (d : Bool) (v : List Wire) : Cov :=
  v.foldr (fun w c => covAdd (sep d w.1) c) (0, 0, 0)
lemma sigsOf_droppedW (del : List Sig) (v : List Wire) :
    sigsOf (droppedW del v) = dropped del (sigsOf v) := by
  induction v with
  | nil => rfl
  | cons w l ih =>
    unfold sigsOf droppedW dropped at ih ⊢
    simp only [List.map_cons, List.filter_cons]
    cases del.contains w.1
    · simp only [Bool.not_false, ite_true, List.map_cons, ih]
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false, ih]
lemma unionSepW_eq (d : Bool) (v : List Wire) : unionSepW d v = unionSep d (sigsOf v) := by
  induction v with
  | nil => rfl
  | cons w l ih => simp [unionSepW, unionSep, sigsOf, ih]
lemma coverageW_eq (d : Bool) (v : List Wire) : coverageW d v = coverage d (sigsOf v) := by
  induction v with
  | nil => rfl
  | cons w l ih =>
    change covAdd (sep d w.1) (coverageW d l) = covAdd (sep d w.1) (coverage d (sigsOf l))
    rw [ih]
lemma sigsOf_length (v : List Wire) : (sigsOf v).length = v.length := List.length_map ..
lemma mem_sigsOf_iff {v : List Wire} {a : Sig} {τ : Sig → Tag}
    (ht : ∀ w ∈ v, w.2 = τ w.1) : (a, τ a) ∈ v ↔ a ∈ sigsOf v := by
  constructor
  · intro h; exact List.mem_map.mpr ⟨(a, τ a), h, rfl⟩
  · intro h; obtain ⟨w, hw, heq⟩ := List.mem_map.mp h
    have htag := ht w hw
    have : w = (a, τ a) := Prod.ext heq (by rw [htag, heq])
    rwa [← this]
def tagEq : Tag → Tag → Bool
  | .tNone, .tNone => true
  | .tDeg3, .tDeg3 => true
  | .tSpec0, .tSpec0 => true
  | .tSpec1, .tSpec1 => true
  | _, _ => false
lemma tagEq_iff {a b : Tag} : tagEq a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [tagEq]
def isNotSpec0 : Tag → Bool | .tSpec0 => false | _ => true
def isNotSpec1 : Tag → Bool | .tSpec1 => false | _ => true
def isNoneTag : Tag → Bool | .tNone => true | _ => false
def isDeg3Tag : Tag → Bool | .tDeg3 => true | _ => false
def sigEq (a b : Sig) : Bool := Nat.beq a.1 b.1 && Nat.beq a.2 b.2
lemma sigEq_iff {a b : Sig} : sigEq a b = true ↔ a = b := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp only [sigEq, Bool.and_eq_true, Nat.beq_eq, Prod.mk.injEq]
lemma nat_beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false :=
  Bool.eq_false_iff.mpr fun e => h (Nat.beq_eq.mp e)
def gateAvail (g : Sig) : List Wire → Bool
  | [] => !sigEq g zero && !sigEq g one
  | w :: l => !sigEq w.1 g && gateAvail g l
lemma gateAvail_eq_true {v : List Wire} {g : Sig} (hg : g ∉ sigsOf v) (hp : proper g) :
    gateAvail g v = true := by
  induction v with
  | nil =>
    simp only [gateAvail, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, sigEq_iff]
    exact ⟨hp.2.1, hp.2.2⟩
  | cons w l ih =>
    simp only [sigsOf, List.map_cons, List.mem_cons, not_or] at hg
    simp only [gateAvail, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, sigEq_iff]
    exact ⟨Ne.symm hg.1, ih hg.2⟩
def dropOne (a : Sig) : List Wire → List Wire
  | [] => []
  | w :: l => if sigEq w.1 a then dropOne a l else w :: dropOne a l
lemma dropOne_eq (a : Sig) (v : List Wire) : dropOne a v = droppedW [a] v := by
  induction v with
  | nil => rfl
  | cons w l ih =>
    simp only [dropOne, droppedW, List.filter_cons, List.contains_eq_mem, List.mem_singleton, ih]
    by_cases h : w.1 = a
    · have hs : sigEq w.1 a = true := sigEq_iff.mpr h
      rw [hs]; simp [h]
    · have hs : sigEq w.1 a = false := Bool.eq_false_iff.mpr (fun e => h (sigEq_iff.mp e))
      rw [hs]; simp [h]
def dropTwo (a b : Sig) : List Wire → List Wire
  | [] => []
  | w :: l => if sigEq w.1 a || sigEq w.1 b then dropTwo a b l else w :: dropTwo a b l
lemma dropTwo_eq (a b : Sig) (v : List Wire) : dropTwo a b v = droppedW [a, b] v := by
  induction v with
  | nil => rfl
  | cons w l ih =>
    simp only [dropTwo, droppedW, List.filter_cons, List.contains_eq_mem, List.mem_cons,
      List.not_mem_nil, or_false, ih]
    by_cases h1 : w.1 = a
    · have hs1 : sigEq w.1 a = true := sigEq_iff.mpr h1
      rw [hs1]; simp [h1]
    · have hs1 : sigEq w.1 a = false := Bool.eq_false_iff.mpr (fun e => h1 (sigEq_iff.mp e))
      by_cases h2 : w.1 = b
      · have hs2 : sigEq w.1 b = true := sigEq_iff.mpr h2
        rw [hs1, hs2]; simp [h2]
      · have hs2 : sigEq w.1 b = false := Bool.eq_false_iff.mpr (fun e => h2 (sigEq_iff.mp e))
        rw [hs1, hs2]; simp [h1, h2]
def sep0 (a : Sig) : Nat := Nat.land a.1 (Nat.xor a.2 top)
def sep1 (a : Sig) : Nat := Nat.xor a.1 a.2
lemma sep0_eq (a : Sig) : sep0 a = sep false a := rfl
lemma sep1_eq (a : Sig) : sep1 a = sep true a := rfl
structure WSep where
  w : Wire
  p : Nat
  n : Nat
  tg : Tag
  s : Nat
def mkSep0 (w : Wire) : WSep := ⟨w, w.1.1, w.1.2, w.2, sep0 w.1⟩
def mkSep1 (w : Wire) : WSep := ⟨w, w.1.1, w.1.2, w.2, sep1 w.1⟩
def buildSeps0 : List Wire → List WSep × Cov
  | [] => ([], (0, 0, 0))
  | w :: l =>
    let (ls, c) := buildSeps0 l
    let s := sep0 w.1
    (⟨w, w.1.1, w.1.2, w.2, s⟩ :: ls, covAdd s c)
def buildSeps1 : List Wire → List WSep × Cov
  | [] => ([], (0, 0, 0))
  | w :: l =>
    let (ls, c) := buildSeps1 l
    let s := sep1 w.1
    (⟨w, w.1.1, w.1.2, w.2, s⟩ :: ls, covAdd s c)
lemma buildSeps0_eq (v : List Wire) : buildSeps0 v = (v.map mkSep0, coverageW false v) := by
  induction v with
  | nil => rfl
  | cons w l ih => simp only [buildSeps0, ih, List.map_cons, mkSep0]; rfl
lemma buildSeps1_eq (v : List Wire) : buildSeps1 v = (v.map mkSep1, coverageW true v) := by
  induction v with
  | nil => rfl
  | cons w l ih => simp only [buildSeps1, ih, List.map_cons, mkSep1]; rfl
structure WAct0 where
  w : Wire
  p : Nat
  n : Nat
  tg : Tag
  s : Nat
  u : Nat
def mkAct0 (uMask : Nat) (w : Wire) : WAct0 :=
  let s := sep0 w.1
  ⟨w, w.1.1, w.1.2, w.2, s, Nat.land uMask s⟩
def buildActs0 (uMask : Nat) : List WSep → List WAct0
  | [] => []
  | a :: l => ⟨a.w, a.p, a.n, a.tg, a.s, Nat.land uMask a.s⟩ :: buildActs0 uMask l
lemma buildActs0_map (uMask : Nat) (v : List Wire) :
    buildActs0 uMask (v.map mkSep0) = v.map (mkAct0 uMask) := by
  induction v with
  | nil => rfl
  | cons w l ih => simp only [List.map_cons, buildActs0, mkSep0, mkAct0, ih]
structure WAct1 where
  w : Wire
  p : Nat
  n : Nat
  tg : Tag
  s : Nat
  up : Nat
  un : Nat
def mkAct1 (uMask : Nat) (w : Wire) : WAct1 :=
  let s := sep1 w.1
  let u := Nat.land uMask s
  ⟨w, w.1.1, w.1.2, w.2, s, Nat.land u w.1.1, Nat.land u w.1.2⟩
def buildActs1 (uMask : Nat) : List WSep → List WAct1
  | [] => []
  | a :: l =>
    let u := Nat.land uMask a.s
    ⟨a.w, a.p, a.n, a.tg, a.s, Nat.land u a.p, Nat.land u a.n⟩ :: buildActs1 uMask l
lemma buildActs1_map (uMask : Nat) (v : List Wire) :
    buildActs1 uMask (v.map mkSep1) = v.map (mkAct1 uMask) := by
  induction v with
  | nil => rfl
  | cons w l ih => simp only [List.map_cons, buildActs1, mkSep1, mkAct1, ih]
def fastPair0 (r : List Wire → Bool) (v : List Wire) (c : Cov) (a b : WAct0) : Bool :=
  let tryAnd :=
    isNotSpec0 a.tg && isNotSpec0 b.tg &&
    Nat.beq (Nat.land a.u b.p) a.u && Nat.beq (Nat.land b.u a.p) b.u &&
    let gp := Nat.land a.p b.p
    let gn := Nat.land a.n b.n
    let g : Sig := (gp, gn)
    Nat.beq (Nat.lor (Nat.land gp (Nat.xor gn top)) (takeTwo c a.s b.s)) top &&
    gateAvail g v &&
    let gt := if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone
    r ((g, gt) :: dropTwo a.w.1 b.w.1 v)
  let tryOr :=
    isNotSpec1 a.tg && isNotSpec1 b.tg &&
    Nat.beq (Nat.land a.u b.n) 0 && Nat.beq (Nat.land b.u a.n) 0 &&
    let gp := Nat.lor a.p b.p
    let gn := Nat.lor a.n b.n
    let g : Sig := (gp, gn)
    Nat.beq (Nat.lor (Nat.land gp (Nat.xor gn top)) (takeTwo c a.s b.s)) top &&
    gateAvail g v &&
    r ((g, .tNone) :: dropTwo a.w.1 b.w.1 v)
  tryAnd || tryOr
def fastPair1 (r : List Wire → Bool) (v : List Wire) (c : Cov) (a b : WAct1) : Bool :=
  let tryAnd :=
    isNotSpec0 a.tg && isNotSpec0 b.tg &&
    Nat.beq (Nat.land a.up b.p) a.up && Nat.beq (Nat.land b.up a.p) b.up &&
    Nat.beq (Nat.land a.un b.n) a.un && Nat.beq (Nat.land b.un a.n) b.un &&
    let gp := Nat.land a.p b.p
    let gn := Nat.land a.n b.n
    let g : Sig := (gp, gn)
    Nat.beq (Nat.lor (Nat.xor gp gn) (takeTwo c a.s b.s)) top &&
    gateAvail g v &&
    let gt := if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone
    r ((g, gt) :: dropTwo a.w.1 b.w.1 v)
  let tryOr :=
    isNotSpec1 a.tg && isNotSpec1 b.tg &&
    Nat.beq (Nat.land a.up b.n) 0 && Nat.beq (Nat.land b.up a.n) 0 &&
    Nat.beq (Nat.land a.un b.p) 0 && Nat.beq (Nat.land b.un a.p) 0 &&
    let gp := Nat.lor a.p b.p
    let gn := Nat.lor a.n b.n
    let g : Sig := (gp, gn)
    Nat.beq (Nat.lor (Nat.xor gp gn) (takeTwo c a.s b.s)) top &&
    gateAvail g v &&
    r ((g, .tNone) :: dropTwo a.w.1 b.w.1 v)
  tryAnd || tryOr
def tryKeeps1 (r : List Wire → Bool) (v : List Wire) (a b : Sig)
    (base sa sb : Nat) (g wa wb : Wire) (ka kb ua ub : Bool) : Bool :=
  let ok0 := ua && ub && Nat.beq base top
  let okA := ka && ub && Nat.beq (Nat.lor base sa) top
  let okB := kb && ua && Nat.beq (Nat.lor base sb) top
  (ok0 || okA || okB) && gateAvail g.1 v &&
    let rest := dropTwo a b v
    ((ok0 && r (g :: rest)) ||
     (okA && r (g :: wa :: rest)) ||
     (okB && r (g :: wb :: rest)))
def tryKeeps2 (r : List Wire → Bool) (v : List Wire) (a b : Sig)
    (base sa sb : Nat) (g wa wb : Wire) (ka kb : Bool) : Bool :=
  let ok0 := Nat.beq base top
  let okA := ka && Nat.beq (Nat.lor base sa) top
  let okB := kb && Nat.beq (Nat.lor base sb) top
  let okAB := ka && kb && Nat.beq (Nat.lor (Nat.lor base sa) sb) top
  (ok0 || okA || okB || okAB) && gateAvail g.1 v &&
    let rest := dropTwo a b v
    ((ok0 && r (g :: rest)) ||
     (okA && r (g :: wa :: rest)) ||
     (okB && r (g :: wb :: rest)) ||
     (okAB && r (g :: wa :: wb :: rest)))
def slow1Pair0 (r : List Wire → Bool) (v : List Wire) (c : Cov) (a b : WAct0) : Bool :=
  let tryAnd :=
    isNotSpec0 a.tg && isNotSpec0 b.tg &&
    let ka := isNoneTag a.tg
    let kb := isNoneTag b.tg
    let ua := Nat.beq (Nat.land a.u b.p) a.u
    let ub := Nat.beq (Nat.land b.u a.p) b.u
    (ua || ub) && (ua || ka) && (ub || kb) &&
    let gp := Nat.land a.p b.p
    let gn := Nat.land a.n b.n
    let base := Nat.lor (Nat.land gp (Nat.xor gn top)) (takeTwo c a.s b.s)
    let gt := if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone
    tryKeeps1 r v a.w.1 b.w.1 base a.s b.s ((gp, gn), gt) a.w b.w ka kb ua ub
  let tryOr :=
    isNotSpec1 a.tg && isNotSpec1 b.tg &&
    let ka := isNotSpec0 a.tg
    let kb := isNotSpec0 b.tg
    let ua := Nat.beq (Nat.land a.u b.n) 0
    let ub := Nat.beq (Nat.land b.u a.n) 0
    (ua || ub) && (ua || ka) && (ub || kb) &&
    let gp := Nat.lor a.p b.p
    let gn := Nat.lor a.n b.n
    let base := Nat.lor (Nat.land gp (Nat.xor gn top)) (takeTwo c a.s b.s)
    let wa : Wire := (a.w.1, if isDeg3Tag a.tg then .tSpec0 else .tNone)
    let wb : Wire := (b.w.1, if isDeg3Tag b.tg then .tSpec0 else .tNone)
    tryKeeps1 r v a.w.1 b.w.1 base a.s b.s ((gp, gn), .tNone) wa wb ka kb ua ub
  tryAnd || tryOr
def slow1Pair1 (r : List Wire → Bool) (v : List Wire) (c : Cov) (a b : WAct1) : Bool :=
  let tryAnd :=
    isNotSpec0 a.tg && isNotSpec0 b.tg &&
    let ka := isNoneTag a.tg
    let kb := isNoneTag b.tg
    let ua := Nat.beq (Nat.land a.up b.p) a.up && Nat.beq (Nat.land a.un b.n) a.un
    let ub := Nat.beq (Nat.land b.up a.p) b.up && Nat.beq (Nat.land b.un a.n) b.un
    (ua || ub) && (ua || ka) && (ub || kb) &&
    let gp := Nat.land a.p b.p
    let gn := Nat.land a.n b.n
    let base := Nat.lor (Nat.xor gp gn) (takeTwo c a.s b.s)
    let gt := if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone
    tryKeeps1 r v a.w.1 b.w.1 base a.s b.s ((gp, gn), gt) a.w b.w ka kb ua ub
  let tryOr :=
    isNotSpec1 a.tg && isNotSpec1 b.tg &&
    let ka := isNotSpec0 a.tg
    let kb := isNotSpec0 b.tg
    let ua := Nat.beq (Nat.land a.up b.n) 0 && Nat.beq (Nat.land a.un b.p) 0
    let ub := Nat.beq (Nat.land b.up a.n) 0 && Nat.beq (Nat.land b.un a.p) 0
    (ua || ub) && (ua || ka) && (ub || kb) &&
    let gp := Nat.lor a.p b.p
    let gn := Nat.lor a.n b.n
    let base := Nat.lor (Nat.xor gp gn) (takeTwo c a.s b.s)
    let wa : Wire := (a.w.1, if isDeg3Tag a.tg then .tSpec0 else .tNone)
    let wb : Wire := (b.w.1, if isDeg3Tag b.tg then .tSpec0 else .tNone)
    tryKeeps1 r v a.w.1 b.w.1 base a.s b.s ((gp, gn), .tNone) wa wb ka kb ua ub
  tryAnd || tryOr
def slow2Pair0 (r : List Wire → Bool) (v : List Wire) (c : Cov) (a b : WAct0) : Bool :=
  let tryAnd :=
    isNotSpec0 a.tg && isNotSpec0 b.tg &&
    let ka := isNoneTag a.tg
    let kb := isNoneTag b.tg
    (ka || Nat.beq (Nat.land a.u b.p) a.u) && (kb || Nat.beq (Nat.land b.u a.p) b.u) &&
    let gp := Nat.land a.p b.p
    let gn := Nat.land a.n b.n
    let base := Nat.lor (Nat.land gp (Nat.xor gn top)) (takeTwo c a.s b.s)
    let gt := if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone
    tryKeeps2 r v a.w.1 b.w.1 base a.s b.s ((gp, gn), gt) a.w b.w ka kb
  let tryOr :=
    isNotSpec1 a.tg && isNotSpec1 b.tg &&
    let ka := isNotSpec0 a.tg
    let kb := isNotSpec0 b.tg
    (ka || Nat.beq (Nat.land a.u b.n) 0) && (kb || Nat.beq (Nat.land b.u a.n) 0) &&
    let gp := Nat.lor a.p b.p
    let gn := Nat.lor a.n b.n
    let base := Nat.lor (Nat.land gp (Nat.xor gn top)) (takeTwo c a.s b.s)
    let wa : Wire := (a.w.1, if isDeg3Tag a.tg then .tSpec0 else .tNone)
    let wb : Wire := (b.w.1, if isDeg3Tag b.tg then .tSpec0 else .tNone)
    tryKeeps2 r v a.w.1 b.w.1 base a.s b.s ((gp, gn), .tNone) wa wb ka kb
  tryAnd || tryOr
def slow2Pair1 (r : List Wire → Bool) (v : List Wire) (c : Cov) (a b : WAct1) : Bool :=
  let tryAnd :=
    isNotSpec0 a.tg && isNotSpec0 b.tg &&
    let ka := isNoneTag a.tg
    let kb := isNoneTag b.tg
    (ka || (Nat.beq (Nat.land a.up b.p) a.up && Nat.beq (Nat.land a.un b.n) a.un)) &&
    (kb || (Nat.beq (Nat.land b.up a.p) b.up && Nat.beq (Nat.land b.un a.n) b.un)) &&
    let gp := Nat.land a.p b.p
    let gn := Nat.land a.n b.n
    let base := Nat.lor (Nat.xor gp gn) (takeTwo c a.s b.s)
    let gt := if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone
    tryKeeps2 r v a.w.1 b.w.1 base a.s b.s ((gp, gn), gt) a.w b.w ka kb
  let tryOr :=
    isNotSpec1 a.tg && isNotSpec1 b.tg &&
    let ka := isNotSpec0 a.tg
    let kb := isNotSpec0 b.tg
    (ka || (Nat.beq (Nat.land a.up b.n) 0 && Nat.beq (Nat.land a.un b.p) 0)) &&
    (kb || (Nat.beq (Nat.land b.up a.n) 0 && Nat.beq (Nat.land b.un a.p) 0)) &&
    let gp := Nat.lor a.p b.p
    let gn := Nat.lor a.n b.n
    let base := Nat.lor (Nat.xor gp gn) (takeTwo c a.s b.s)
    let wa : Wire := (a.w.1, if isDeg3Tag a.tg then .tSpec0 else .tNone)
    let wb : Wire := (b.w.1, if isDeg3Tag b.tg then .tSpec0 else .tNone)
    tryKeeps2 r v a.w.1 b.w.1 base a.s b.s ((gp, gn), .tNone) wa wb ka kb
  tryAnd || tryOr
def scanFast0One (r : List Wire → Bool) (v : List Wire) (c : Cov) (a : WAct0) : List WAct0 → Bool
  | [] => false
  | b :: l => fastPair0 r v c a b || scanFast0One r v c a l
def scanFast0 (r : List Wire → Bool) (v : List Wire) (c : Cov) : List WAct0 → Bool
  | [] => false
  | a :: l => scanFast0One r v c a l || scanFast0 r v c l
def scanFast1One (r : List Wire → Bool) (v : List Wire) (c : Cov) (a : WAct1) : List WAct1 → Bool
  | [] => false
  | b :: l => fastPair1 r v c a b || scanFast1One r v c a l
def scanFast1 (r : List Wire → Bool) (v : List Wire) (c : Cov) : List WAct1 → Bool
  | [] => false
  | a :: l => scanFast1One r v c a l || scanFast1 r v c l
def scanSlow10One (r : List Wire → Bool) (v : List Wire) (c : Cov) (a : WAct0) : List WAct0 → Bool
  | [] => false
  | b :: l => slow1Pair0 r v c a b || scanSlow10One r v c a l
def scanSlow10 (r : List Wire → Bool) (v : List Wire) (c : Cov) : List WAct0 → Bool
  | [] => false
  | a :: l => scanSlow10One r v c a l || scanSlow10 r v c l
def scanSlow11One (r : List Wire → Bool) (v : List Wire) (c : Cov) (a : WAct1) : List WAct1 → Bool
  | [] => false
  | b :: l => slow1Pair1 r v c a b || scanSlow11One r v c a l
def scanSlow11 (r : List Wire → Bool) (v : List Wire) (c : Cov) : List WAct1 → Bool
  | [] => false
  | a :: l => scanSlow11One r v c a l || scanSlow11 r v c l
def scanSlow20One (r : List Wire → Bool) (v : List Wire) (c : Cov) (a : WAct0) : List WAct0 → Bool
  | [] => false
  | b :: l => slow2Pair0 r v c a b || scanSlow20One r v c a l
def scanSlow20 (r : List Wire → Bool) (v : List Wire) (c : Cov) : List WAct0 → Bool
  | [] => false
  | a :: l => scanSlow20One r v c a l || scanSlow20 r v c l
def scanSlow21One (r : List Wire → Bool) (v : List Wire) (c : Cov) (a : WAct1) : List WAct1 → Bool
  | [] => false
  | b :: l => slow2Pair1 r v c a b || scanSlow21One r v c a l
def scanSlow21 (r : List Wire → Bool) (v : List Wire) (c : Cov) : List WAct1 → Bool
  | [] => false
  | a :: l => scanSlow21One r v c a l || scanSlow21 r v c l
def unaryScan0 (lim n : Nat) (r : List Wire → Bool) (v : List Wire) (c : Cov) : List WSep → Bool
  | [] => false
  | a :: l =>
    (isNotSpec0 a.tg && isNotSpec1 a.tg &&
      let gp := Nat.xor a.p top
      let gn := Nat.xor a.n top
      let base := Nat.lor (Nat.land gp (Nat.xor gn top)) (takeOne c a.s)
      let ka := !isDeg3Tag a.tg && Nat.ble (n + 2) lim
      let ok0 := Nat.beq base top
      let okA := ka && Nat.beq (Nat.lor base a.s) top
      (ok0 || okA) && gateAvail (gp, gn) v &&
        let gt := if isDeg3Tag a.tg then Tag.tSpec1 else Tag.tNone
        let rest := dropOne a.w.1 v
        ((ok0 && r (((gp, gn), gt) :: rest)) ||
         (okA && r (((gp, gn), gt) :: a.w :: rest)))) ||
    unaryScan0 lim n r v c l
def unaryScan1 (lim n : Nat) (r : List Wire → Bool) (v : List Wire) (c : Cov) : List WSep → Bool
  | [] => false
  | a :: l =>
    (isNotSpec0 a.tg && isNotSpec1 a.tg &&
      let gp := Nat.xor a.p top
      let gn := Nat.xor a.n top
      let base := Nat.lor (Nat.xor gp gn) (takeOne c a.s)
      let ka := !isDeg3Tag a.tg && Nat.ble (n + 2) lim
      let ok0 := Nat.beq base top
      let okA := ka && Nat.beq (Nat.lor base a.s) top
      (ok0 || okA) && gateAvail (gp, gn) v &&
        let gt := if isDeg3Tag a.tg then Tag.tSpec1 else Tag.tNone
        let rest := dropOne a.w.1 v
        ((ok0 && r (((gp, gn), gt) :: rest)) ||
         (okA && r (((gp, gn), gt) :: a.w :: rest)))) ||
    unaryScan1 lim n r v c l
def binaryMoves (k t len : Nat) (r : List Wire → Bool) (v : List Wire) : Bool :=
  let lim := k - t + 1
  if Nat.beq t 0 then
    let (seps, c) := buildSeps0 v
    let acts := buildActs0 c.2.1 seps
    if Nat.beq len (lim + 1) then scanFast0 r v c acts
    else if Nat.beq len lim then scanSlow10 r v c acts
    else scanSlow20 r v c acts
  else
    let (seps, c) := buildSeps1 v
    let acts := buildActs1 c.2.1 seps
    if Nat.beq len (lim + 1) then scanFast1 r v c acts
    else if Nat.beq len lim then scanSlow11 r v c acts
    else scanSlow21 r v c acts
def unaryMoves (k t len : Nat) (r : List Wire → Bool) (v : List Wire) : Bool :=
  if Nat.beq t 0 then
    let (seps, c) := buildSeps0 v
    unaryScan0 (k - t + 1) (len - 1) r v c seps
  else
    let (seps, c) := buildSeps1 v
    unaryScan1 (k - t + 1) (len - 1) r v c seps
def stepTest (k t : Nat) (v : List Wire) (u b : List Wire → Bool) : Bool :=
  let len := v.length
  if Nat.blt (k + 1) t || Nat.blt (k + 1 - t + 1) len then false else
    (match v with | [w] => sigEq w.1 target | _ => false) ||
    (Nat.blt 0 t && unaryMoves k (t - 1) len u v) ||
    binaryMoves k t len b v
def search : Nat → Nat → List Wire → Bool
  | 0, _, v => match v with | [w] => sigEq w.1 target | _ => false
  | k + 1, t, v => stepTest k t v (search k (t - 1)) (search k t)
def scanPairs {α : Type} (p : α → α → Bool) : List α → Bool
  | [] => false
  | a :: t => t.any (p a) || scanPairs p t
lemma scanPairs_complete {α : Type} (p : α → α → Bool) {a b : α} {v : List α}
    (ha : a ∈ v) (hb : b ∈ v) (hne : a ≠ b)
    (hab : p a b = true) (hba : p b a = true) : scanPairs p v = true := by
  induction v with
  | nil => simp at ha
  | cons h v ih =>
    simp only [scanPairs, Bool.or_eq_true]
    by_cases eqA : a = h
    · subst h; exact Or.inl (List.any_eq_true.mpr ⟨b, (List.mem_cons.mp hb).resolve_left (Ne.symm hne), hab⟩)
    · have ha' := (List.mem_cons.mp ha).resolve_left eqA
      by_cases eqB : b = h
      · subst h; exact Or.inl (List.any_eq_true.mpr ⟨a, ha', hba⟩)
      · exact Or.inr (ih ha' ((List.mem_cons.mp hb).resolve_left eqB))
lemma scanFast0One_eq (r v c a l) : scanFast0One r v c a l = l.any (fastPair0 r v c a) := by
  induction l with | nil => rfl | cons b l ih => simp [scanFast0One, ih]
lemma scanFast0_eq (r v c l) : scanFast0 r v c l = scanPairs (fastPair0 r v c) l := by
  induction l with | nil => rfl | cons a l ih => simp [scanFast0, scanPairs, scanFast0One_eq, ih]
lemma scanFast1One_eq (r v c a l) : scanFast1One r v c a l = l.any (fastPair1 r v c a) := by
  induction l with | nil => rfl | cons b l ih => simp [scanFast1One, ih]
lemma scanFast1_eq (r v c l) : scanFast1 r v c l = scanPairs (fastPair1 r v c) l := by
  induction l with | nil => rfl | cons a l ih => simp [scanFast1, scanPairs, scanFast1One_eq, ih]
lemma scanSlow10One_eq (r v c a l) : scanSlow10One r v c a l = l.any (slow1Pair0 r v c a) := by
  induction l with | nil => rfl | cons b l ih => simp [scanSlow10One, ih]
lemma scanSlow10_eq (r v c l) : scanSlow10 r v c l = scanPairs (slow1Pair0 r v c) l := by
  induction l with | nil => rfl | cons a l ih => simp [scanSlow10, scanPairs, scanSlow10One_eq, ih]
lemma scanSlow11One_eq (r v c a l) : scanSlow11One r v c a l = l.any (slow1Pair1 r v c a) := by
  induction l with | nil => rfl | cons b l ih => simp [scanSlow11One, ih]
lemma scanSlow11_eq (r v c l) : scanSlow11 r v c l = scanPairs (slow1Pair1 r v c) l := by
  induction l with | nil => rfl | cons a l ih => simp [scanSlow11, scanPairs, scanSlow11One_eq, ih]
lemma scanSlow20One_eq (r v c a l) : scanSlow20One r v c a l = l.any (slow2Pair0 r v c a) := by
  induction l with | nil => rfl | cons b l ih => simp [scanSlow20One, ih]
lemma scanSlow20_eq (r v c l) : scanSlow20 r v c l = scanPairs (slow2Pair0 r v c) l := by
  induction l with | nil => rfl | cons a l ih => simp [scanSlow20, scanPairs, scanSlow20One_eq, ih]
lemma scanSlow21One_eq (r v c a l) : scanSlow21One r v c a l = l.any (slow2Pair1 r v c a) := by
  induction l with | nil => rfl | cons b l ih => simp [scanSlow21One, ih]
lemma scanSlow21_eq (r v c l) : scanSlow21 r v c l = scanPairs (slow2Pair1 r v c) l := by
  induction l with | nil => rfl | cons a l ih => simp [scanSlow21, scanPairs, scanSlow21One_eq, ih]
lemma unique_and_0 {c : Cov} {a b : Sig} {extra : Nat} (hc : ValidCov c)
    (hex : Nat.land (Nat.land c.2.1 (sep0 a)) extra = 0)
    (h : Nat.lor (Nat.lor (sep0 (bin false a b)) (takeTwo c (sep0 a) (sep0 b))) extra = top) :
    Nat.land (Nat.land c.2.1 (sep0 a)) b.1 = Nat.land c.2.1 (sep0 a) := by
  apply Nat.eq_of_testBit_eq; intro i
  have hh := congrArg (fun z : Nat => z.testBit i) h
  have hx := congrArg (fun z : Nat => z.testBit i) hex
  have h1 := hc.2.2.2.1 i
  by_cases hi : i < 544
  · simp only [sep0, bin, takeTwo, testBit_land, testBit_lor, testBit_lxor, testBit_top,
      Nat.testBit_and, hi, decide_true, Nat.zero_testBit, Bool.false_eq_true, ite_false] at hh hx ⊢
    revert hh hx h1
    cases a.1.testBit i <;> cases a.2.testBit i <;> cases b.1.testBit i <;>
      cases b.2.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;>
      cases extra.testBit i <;> simp
  · simp [hc.2.1 i (by omega)]
lemma unique_or_0 {c : Cov} {a b : Sig} {extra : Nat} (hc : ValidCov c)
    (hex : Nat.land (Nat.land c.2.1 (sep0 a)) extra = 0)
    (h : Nat.lor (Nat.lor (sep0 (bin true a b)) (takeTwo c (sep0 a) (sep0 b))) extra = top) :
    Nat.land (Nat.land c.2.1 (sep0 a)) b.2 = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  have hh := congrArg (fun z : Nat => z.testBit i) h
  have hx := congrArg (fun z : Nat => z.testBit i) hex
  have h1 := hc.2.2.2.1 i
  by_cases hi : i < 544
  · simp only [sep0, bin, takeTwo, testBit_land, testBit_lor, testBit_lxor, testBit_top,
      Nat.testBit_or, hi, decide_true, Nat.zero_testBit, ite_true] at hh hx ⊢
    revert hh hx h1
    cases a.1.testBit i <;> cases a.2.testBit i <;> cases b.1.testBit i <;>
      cases b.2.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;>
      cases extra.testBit i <;> simp
  · simp [hc.2.1 i (by omega)]
lemma unique_and_1 {c : Cov} {a b : Sig} {extra : Nat} (hc : ValidCov c)
    (hex : Nat.land (Nat.land c.2.1 (sep1 a)) extra = 0)
    (h : Nat.lor (Nat.lor (sep1 (bin false a b)) (takeTwo c (sep1 a) (sep1 b))) extra = top) :
    Nat.land (Nat.land (Nat.land c.2.1 (sep1 a)) a.1) b.1 = Nat.land (Nat.land c.2.1 (sep1 a)) a.1 ∧
    Nat.land (Nat.land (Nat.land c.2.1 (sep1 a)) a.2) b.2 = Nat.land (Nat.land c.2.1 (sep1 a)) a.2 := by
  constructor <;> (
    apply Nat.eq_of_testBit_eq; intro i
    have hh := congrArg (fun z : Nat => z.testBit i) h
    have hx := congrArg (fun z : Nat => z.testBit i) hex
    have h1 := hc.2.2.2.1 i
    by_cases hi : i < 544
    · simp only [sep1, bin, takeTwo, testBit_land, testBit_lor, testBit_lxor, testBit_top,
        Nat.testBit_and, hi, decide_true, Nat.zero_testBit, Bool.false_eq_true, ite_false] at hh hx ⊢
      revert hh hx h1
      cases a.1.testBit i <;> cases a.2.testBit i <;> cases b.1.testBit i <;>
        cases b.2.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;>
        cases extra.testBit i <;> simp
    · simp [hc.2.1 i (by omega)])
lemma unique_or_1 {c : Cov} {a b : Sig} {extra : Nat} (hc : ValidCov c)
    (hex : Nat.land (Nat.land c.2.1 (sep1 a)) extra = 0)
    (h : Nat.lor (Nat.lor (sep1 (bin true a b)) (takeTwo c (sep1 a) (sep1 b))) extra = top) :
    Nat.land (Nat.land (Nat.land c.2.1 (sep1 a)) a.1) b.2 = 0 ∧
    Nat.land (Nat.land (Nat.land c.2.1 (sep1 a)) a.2) b.1 = 0 := by
  constructor <;> (
    apply Nat.eq_of_testBit_eq; intro i
    have hh := congrArg (fun z : Nat => z.testBit i) h
    have hx := congrArg (fun z : Nat => z.testBit i) hex
    have h1 := hc.2.2.2.1 i
    by_cases hi : i < 544
    · simp only [sep1, bin, takeTwo, testBit_land, testBit_lor, testBit_lxor, testBit_top,
        Nat.testBit_or, hi, decide_true, Nat.zero_testBit, ite_true] at hh hx ⊢
      revert hh hx h1
      cases a.1.testBit i <;> cases a.2.testBit i <;> cases b.1.testBit i <;>
        cases b.2.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;>
        cases extra.testBit i <;> simp
    · simp [hc.2.1 i (by omega)])
lemma unaryScan0_mem {lim n : Nat} {r : List Wire → Bool} {v : List Wire} {c : Cov}
    {a : WSep} {l : List WSep} (ha : a ∈ l)
    (hok : (isNotSpec0 a.tg && isNotSpec1 a.tg &&
      let gp := Nat.xor a.p top; let gn := Nat.xor a.n top
      let base := Nat.lor (Nat.land gp (Nat.xor gn top)) (takeOne c a.s)
      let ka := !isDeg3Tag a.tg && Nat.ble (n + 2) lim
      let ok0 := Nat.beq base top
      let okA := ka && Nat.beq (Nat.lor base a.s) top
      (ok0 || okA) && gateAvail (gp, gn) v &&
        let gt := if isDeg3Tag a.tg then Tag.tSpec1 else Tag.tNone
        let rest := dropOne a.w.1 v
        ((ok0 && r (((gp, gn), gt) :: rest)) || (okA && r (((gp, gn), gt) :: a.w :: rest)))) = true) :
    unaryScan0 lim n r v c l = true := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    simp only [unaryScan0, Bool.or_eq_true]
    rcases List.mem_cons.mp ha with rfl | hx
    · exact Or.inl hok
    · exact Or.inr (ih hx)
lemma unaryScan1_mem {lim n : Nat} {r : List Wire → Bool} {v : List Wire} {c : Cov}
    {a : WSep} {l : List WSep} (ha : a ∈ l)
    (hok : (isNotSpec0 a.tg && isNotSpec1 a.tg &&
      let gp := Nat.xor a.p top; let gn := Nat.xor a.n top
      let base := Nat.lor (Nat.xor gp gn) (takeOne c a.s)
      let ka := !isDeg3Tag a.tg && Nat.ble (n + 2) lim
      let ok0 := Nat.beq base top
      let okA := ka && Nat.beq (Nat.lor base a.s) top
      (ok0 || okA) && gateAvail (gp, gn) v &&
        let gt := if isDeg3Tag a.tg then Tag.tSpec1 else Tag.tNone
        let rest := dropOne a.w.1 v
        ((ok0 && r (((gp, gn), gt) :: rest)) || (okA && r (((gp, gn), gt) :: a.w :: rest)))) = true) :
    unaryScan1 lim n r v c l = true := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    simp only [unaryScan1, Bool.or_eq_true]
    rcases List.mem_cons.mp ha with rfl | hx
    · exact Or.inl hok
    · exact Or.inr (ih hx)
lemma unary_found {m t k : Nat} {U : Finset Sig} {a : Sig} {τ : Sig → Tag} {v : List Wire}
    {r : List Wire → Bool}
    (ha : proper a) (hrep : Represents v (insert a U) τ) (hle : m ≤ k)
    (fresh : neg a ∉ insert a U)
    (hr1 : τ a ≠ .tSpec0 ∧ τ a ≠ .tSpec1) (hr2 : τ a = .tDeg3 → a ∉ U)
    (l : TRestricted m t (insert (neg a) U) (updUnaryTag τ a))
    (ih : ∀ w : List Wire, Represents w (insert (neg a) U) (updUnaryTag τ a) → r w = true) :
    unaryMoves k t v.length r v = true := by
  obtain ⟨hndS, heS, htag⟩ := hrep
  have hval : ∀ x ∈ sigsOf v, Valid x := by
    intro x hx
    rcases Finset.mem_insert.mp (heS ▸ List.mem_toFinset.mpr hx) with rfl | hxU
    · exact ha.1
    · exact (live_proper l.live x (Finset.mem_insert_of_mem hxU)).1
  have ahS : a ∈ sigsOf v := List.mem_toFinset.mp (heS.symm ▸ Finset.mem_insert_self _ _)
  have ah : (a, τ a) ∈ v := (mem_sigsOf_iff htag).mpr ahS
  let rest := droppedW [a] v
  let gTag : Tag := if isDeg3Tag (τ a) then .tSpec1 else .tNone
  let g : Wire := (neg a, gTag)
  let h : List Wire := if a ∈ U then [(a, τ a)] else []
  have hSigsH : sigsOf h = keepOf U [a] := by by_cases hm : a ∈ U <;> simp [h, sigsOf, keepOf, hm]
  obtain ⟨hn, eq⟩ := edit_list (del := [a]) (U := U) hndS (by simp) (by simpa using heS)
  have hSigsHR : sigsOf (h ++ rest) = keepOf U [a] ++ dropped [a] (sigsOf v) := by
    change (h ++ rest).map Prod.fst = _
    rw [List.map_append, show h.map Prod.fst = keepOf U [a] from hSigsH,
      show rest.map Prod.fst = dropped [a] (sigsOf v) from sigsOf_droppedW [a] v]
  have nn : neg a ∉ sigsOf v := fun hm => fresh (heS ▸ List.mem_toFinset.mpr hm)
  have nz : neg a ∉ U := fun hm => fresh (Finset.mem_insert_of_mem hm)
  have hnd : (sigsOf (g :: (h ++ rest))).Nodup := by
    change (neg a :: sigsOf (h ++ rest)).Nodup; rw [hSigsHR]
    exact List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm), hn⟩
  have e : (sigsOf (g :: (h ++ rest))).toFinset = insert (neg a) U := by
    change (neg a :: sigsOf (h ++ rest)).toFinset = _; rw [List.toFinset_cons, hSigsHR, eq]
  have htag' : ∀ w ∈ g :: (h ++ rest), w.2 = updUnaryTag τ a w.1 := by
    intro w hw; rcases List.mem_cons.mp hw with rfl | hw'
    · simp only [g, gTag, updUnaryTag, ite_true]; cases τ a <;> rfl
    · have hwV : w ∈ v := by
        rcases List.mem_append.mp hw' with hh | hr
        · by_cases hm : a ∈ U
          · simp only [h, hm, ite_true, List.mem_singleton] at hh; exact hh ▸ ah
          · simp [h, hm] at hh
        · exact List.mem_of_mem_filter hr
      have hwNe : w.1 ≠ neg a := fun heq => nn (heq ▸ List.mem_map_of_mem hwV)
      simp [updUnaryTag, hwNe, htag w hwV]
  have hr := ih _ ⟨hnd, e, htag'⟩
  obtain ⟨ht, hc⟩ := live_size l.live
  rw [← e, List.toFinset_card_of_nodup hnd] at hc
  simp only [sigsOf, List.map_cons, List.map_append, List.length_cons, List.length_append,
    List.length_map] at hc
  have hav : gateAvail (neg a) v = true :=
    gateAvail_eq_true nn (live_proper l.live _ (Finset.mem_insert_self _ _))
  have hns0 : isNotSpec0 (τ a) = true := by cases hta : τ a <;> simp [isNotSpec0]; exact hr1.1 hta
  have hns1 : isNotSpec1 (τ a) = true := by cases hta : τ a <;> simp [isNotSpec1]; exact hr1.2 hta
  have cv := live_cover l.live e
  simp only [sigsOf, List.map_cons, List.map_append, unionSep, union_append] at cv
  have hcv' : (sep (decide (0 < t)) (neg a) ||| unionSep (decide (0 < t)) (sigsOf rest)) |||
      unionSepW (decide (0 < t)) h = top := by
    rw [unionSepW_eq, ← cv]; unfold sigsOf; ac_rfl
  obtain ⟨hlen, hmask⟩ := one_rest (decide (0 < t)) hndS hval ahS
  rw [sigsOf_length, ← sigsOf_droppedW, sigsOf_length] at hlen
  change v.length - 1 = rest.length at hlen
  rw [← sigsOf_droppedW] at hmask
  change takeOne (coverage (decide (0 < t)) (sigsOf v)) (sep (decide (0 < t)) a) =
    unionSep (decide (0 < t)) (sigsOf rest) at hmask
  have hdrop : dropOne a v = rest := dropOne_eq a v
  unfold unaryMoves
  by_cases ht0 : t = 0
  · subst ht0
    have hdt0 : decide (0 < 0) = false := rfl
    rw [hdt0] at hcv' hmask
    simp only [Nat.beq_refl, ite_true, buildSeps0_eq]
    apply unaryScan0_mem (a := mkSep0 (a, τ a)) (List.mem_map_of_mem ah)
    simp only [mkSep0, coverageW_eq]
    change (isNotSpec0 (τ a) && isNotSpec1 (τ a) &&
      let base := Nat.lor (sep false (neg a)) (takeOne (coverage false (sigsOf v)) (sep false a))
      let ka := !isDeg3Tag (τ a) && Nat.ble (v.length - 1 + 2) (k - 0 + 1)
      let ok0 := Nat.beq base top
      let okA := ka && Nat.beq (Nat.lor base (sep false a)) top
      (ok0 || okA) && gateAvail (neg a) v &&
        let rest' := dropOne a v
        ((ok0 && r (g :: rest')) || (okA && r (g :: (a, τ a) :: rest')))) = true
    rw [hmask, hdrop]
    by_cases haU : a ∈ U
    · have hnd3 : (!isDeg3Tag (τ a)) = true := by
        cases hta : τ a <;> simp [isDeg3Tag]; exact hr2 hta haU
      have hlenH : h.length = 1 := by simp [h, haU]
      have hle' : Nat.ble (v.length - 1 + 2) (k - 0 + 1) = true := Nat.ble_eq.mpr (by omega)
      have hcovA : Nat.lor (Nat.lor (sep false (neg a)) (unionSep false (sigsOf rest))) (sep false a) = top := by
        simpa [h, haU, unionSepW] using hcv'
      have hrA : r (g :: (a, τ a) :: rest) = true := by simpa [h, haU] using hr
      simp only [hns0, hns1, hnd3, hle', hcovA, Nat.beq_refl, hav, hrA, Bool.true_and, Bool.or_true]
    · have hcov0 : Nat.lor (sep false (neg a)) (unionSep false (sigsOf rest)) = top := by
        simpa [h, haU, unionSepW] using hcv'
      have hr0 : r (g :: rest) = true := by simpa [h, haU] using hr
      simp only [hns0, hns1, hcov0, Nat.beq_refl, hav, hr0, Bool.true_and, Bool.true_or]
  · have hbf : Nat.beq t 0 = false := nat_beq_false ht0
    have hdt : decide (0 < t) = true := decide_eq_true (by omega)
    rw [hdt] at hcv' hmask
    simp only [hbf, Bool.false_eq_true, ite_false, buildSeps1_eq]
    apply unaryScan1_mem (a := mkSep1 (a, τ a)) (List.mem_map_of_mem ah)
    simp only [mkSep1, coverageW_eq]
    change (isNotSpec0 (τ a) && isNotSpec1 (τ a) &&
      let base := Nat.lor (sep true (neg a)) (takeOne (coverage true (sigsOf v)) (sep true a))
      let ka := !isDeg3Tag (τ a) && Nat.ble (v.length - 1 + 2) (k - t + 1)
      let ok0 := Nat.beq base top
      let okA := ka && Nat.beq (Nat.lor base (sep true a)) top
      (ok0 || okA) && gateAvail (neg a) v &&
        let rest' := dropOne a v
        ((ok0 && r (g :: rest')) || (okA && r (g :: (a, τ a) :: rest')))) = true
    rw [hmask, hdrop]
    by_cases haU : a ∈ U
    · have hnd3 : (!isDeg3Tag (τ a)) = true := by
        cases hta : τ a <;> simp [isDeg3Tag]; exact hr2 hta haU
      have hlenH : h.length = 1 := by simp [h, haU]
      have hle' : Nat.ble (v.length - 1 + 2) (k - t + 1) = true := Nat.ble_eq.mpr (by omega)
      have hcovA : Nat.lor (Nat.lor (sep true (neg a)) (unionSep true (sigsOf rest))) (sep true a) = top := by
        simpa [h, haU, unionSepW] using hcv'
      have hrA : r (g :: (a, τ a) :: rest) = true := by simpa [h, haU] using hr
      simp only [hns0, hns1, hnd3, hle', hcovA, Nat.beq_refl, hav, hrA, Bool.true_and, Bool.or_true]
    · have hcov0 : Nat.lor (sep true (neg a)) (unionSep true (sigsOf rest)) = top := by
        simpa [h, haU, unionSepW] using hcv'
      have hr0 : r (g :: rest) = true := by simpa [h, haU] using hr
      simp only [hns0, hns1, hcov0, Nat.beq_refl, hav, hr0, Bool.true_and, Bool.true_or]
lemma bor_l {p q : Bool} (h : p = true) : (p || q) = true := by simp [h]
lemma bor_r {p q : Bool} (h : q = true) : (p || q) = true := by simp [h]
lemma band2 {p q : Bool} (hp : p = true) (hq : q = true) : (p && q) = true := by simp [hp, hq]
lemma tryKeeps1_guard {r v a b base sa sb g wa wb ka kb ua ub}
    (h : tryKeeps1 r v a b base sa sb g wa wb ka kb ua ub = true) :
    (ua || ub) = true ∧ (ua || ka) = true ∧ (ub || kb) = true := by
  cases ka <;> cases kb <;> cases ua <;> cases ub <;> simp_all [tryKeeps1]
lemma tryKeeps1_0 {r v a b base sa sb g wa wb ka kb ua ub}
    (h1 : ua = true) (h2 : ub = true) (h3 : base = top)
    (h4 : gateAvail g.1 v = true) (h5 : r (g :: dropTwo a b v) = true) :
    tryKeeps1 r v a b base sa sb g wa wb ka kb ua ub = true := by
  simp only [tryKeeps1, h1, h2, h3, Nat.beq_refl, h4, h5, Bool.true_and, Bool.true_or]
lemma tryKeeps1_A {r v a b base sa sb g wa wb ka kb ua ub}
    (h1 : ka = true) (h2 : ub = true) (h3 : Nat.lor base sa = top)
    (h4 : gateAvail g.1 v = true) (h5 : r (g :: wa :: dropTwo a b v) = true) :
    tryKeeps1 r v a b base sa sb g wa wb ka kb ua ub = true := by
  simp only [tryKeeps1, h1, h2, h3, Nat.beq_refl, h4, h5, Bool.true_and, Bool.true_or, Bool.or_true]
lemma tryKeeps1_B {r v a b base sa sb g wa wb ka kb ua ub}
    (h1 : kb = true) (h2 : ua = true) (h3 : Nat.lor base sb = top)
    (h4 : gateAvail g.1 v = true) (h5 : r (g :: wb :: dropTwo a b v) = true) :
    tryKeeps1 r v a b base sa sb g wa wb ka kb ua ub = true := by
  simp only [tryKeeps1, h1, h2, h3, Nat.beq_refl, h4, h5, Bool.true_and, Bool.or_true]
lemma tryKeeps2_0 {r v a b base sa sb g wa wb ka kb}
    (h3 : base = top) (h4 : gateAvail g.1 v = true) (h5 : r (g :: dropTwo a b v) = true) :
    tryKeeps2 r v a b base sa sb g wa wb ka kb = true := by
  simp only [tryKeeps2, h3, Nat.beq_refl, h4, h5, Bool.true_and, Bool.true_or]
lemma tryKeeps2_A {r v a b base sa sb g wa wb ka kb}
    (h1 : ka = true) (h3 : Nat.lor base sa = top)
    (h4 : gateAvail g.1 v = true) (h5 : r (g :: wa :: dropTwo a b v) = true) :
    tryKeeps2 r v a b base sa sb g wa wb ka kb = true := by
  simp only [tryKeeps2, h1, h3, Nat.beq_refl, h4, h5, Bool.true_and, Bool.true_or, Bool.or_true]
lemma tryKeeps2_B {r v a b base sa sb g wa wb ka kb}
    (h1 : kb = true) (h3 : Nat.lor base sb = top)
    (h4 : gateAvail g.1 v = true) (h5 : r (g :: wb :: dropTwo a b v) = true) :
    tryKeeps2 r v a b base sa sb g wa wb ka kb = true := by
  simp only [tryKeeps2, h1, h3, Nat.beq_refl, h4, h5, Bool.true_and, Bool.true_or, Bool.or_true]
lemma tryKeeps2_AB {r v a b base sa sb g wa wb ka kb}
    (h1 : ka = true) (h2 : kb = true) (h3 : Nat.lor (Nat.lor base sa) sb = top)
    (h4 : gateAvail g.1 v = true) (h5 : r (g :: wa :: wb :: dropTwo a b v) = true) :
    tryKeeps2 r v a b base sa sb g wa wb ka kb = true := by
  simp only [tryKeeps2, h1, h2, h3, Nat.beq_refl, h4, h5, Bool.true_and, Bool.or_true]
lemma fastPair0_and {r v c a b}
    (h1 : isNotSpec0 a.tg = true) (h2 : isNotSpec0 b.tg = true)
    (h3 : Nat.land a.u b.p = a.u) (h4 : Nat.land b.u a.p = b.u)
    (h5 : Nat.lor (Nat.land (Nat.land a.p b.p) (Nat.xor (Nat.land a.n b.n) top)) (takeTwo c a.s b.s) = top)
    (h6 : gateAvail (Nat.land a.p b.p, Nat.land a.n b.n) v = true)
    (h7 : r (((Nat.land a.p b.p, Nat.land a.n b.n),
      if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone) :: dropTwo a.w.1 b.w.1 v) = true) :
    fastPair0 r v c a b = true := by
  simp only [fastPair0, h1, h2, h3, h4, h5, Nat.beq_refl, h6, h7, Bool.true_and, Bool.true_or]
lemma fastPair0_or {r v c a b}
    (h1 : isNotSpec1 a.tg = true) (h2 : isNotSpec1 b.tg = true)
    (h3 : Nat.land a.u b.n = 0) (h4 : Nat.land b.u a.n = 0)
    (h5 : Nat.lor (Nat.land (Nat.lor a.p b.p) (Nat.xor (Nat.lor a.n b.n) top)) (takeTwo c a.s b.s) = top)
    (h6 : gateAvail (Nat.lor a.p b.p, Nat.lor a.n b.n) v = true)
    (h7 : r (((Nat.lor a.p b.p, Nat.lor a.n b.n), .tNone) :: dropTwo a.w.1 b.w.1 v) = true) :
    fastPair0 r v c a b = true := by
  simp only [fastPair0, h1, h2, h3, h4, h5, Nat.beq_refl, h6, h7, Bool.true_and, Bool.or_true]
lemma fastPair1_and {r v c a b}
    (h1 : isNotSpec0 a.tg = true) (h2 : isNotSpec0 b.tg = true)
    (h3a : Nat.land a.up b.p = a.up) (h3b : Nat.land b.up a.p = b.up)
    (h4a : Nat.land a.un b.n = a.un) (h4b : Nat.land b.un a.n = b.un)
    (h5 : Nat.lor (Nat.xor (Nat.land a.p b.p) (Nat.land a.n b.n)) (takeTwo c a.s b.s) = top)
    (h6 : gateAvail (Nat.land a.p b.p, Nat.land a.n b.n) v = true)
    (h7 : r (((Nat.land a.p b.p, Nat.land a.n b.n),
      if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone) :: dropTwo a.w.1 b.w.1 v) = true) :
    fastPair1 r v c a b = true := by
  simp only [fastPair1, h1, h2, h3a, h3b, h4a, h4b, h5, Nat.beq_refl, h6, h7, Bool.true_and, Bool.true_or]
lemma fastPair1_or {r v c a b}
    (h1 : isNotSpec1 a.tg = true) (h2 : isNotSpec1 b.tg = true)
    (h3a : Nat.land a.up b.n = 0) (h3b : Nat.land b.up a.n = 0)
    (h4a : Nat.land a.un b.p = 0) (h4b : Nat.land b.un a.p = 0)
    (h5 : Nat.lor (Nat.xor (Nat.lor a.p b.p) (Nat.lor a.n b.n)) (takeTwo c a.s b.s) = top)
    (h6 : gateAvail (Nat.lor a.p b.p, Nat.lor a.n b.n) v = true)
    (h7 : r (((Nat.lor a.p b.p, Nat.lor a.n b.n), .tNone) :: dropTwo a.w.1 b.w.1 v) = true) :
    fastPair1 r v c a b = true := by
  simp only [fastPair1, h1, h2, h3a, h3b, h4a, h4b, h5, Nat.beq_refl, h6, h7, Bool.true_and, Bool.or_true]
lemma slow1Pair0_and {r v c a b}
    (h1 : isNotSpec0 a.tg = true) (h2 : isNotSpec0 b.tg = true)
    (ht : tryKeeps1 r v a.w.1 b.w.1
      (Nat.lor (Nat.land (Nat.land a.p b.p) (Nat.xor (Nat.land a.n b.n) top)) (takeTwo c a.s b.s))
      a.s b.s ((Nat.land a.p b.p, Nat.land a.n b.n),
        if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone)
      a.w b.w (isNoneTag a.tg) (isNoneTag b.tg)
      (Nat.beq (Nat.land a.u b.p) a.u) (Nat.beq (Nat.land b.u a.p) b.u) = true) :
    slow1Pair0 r v c a b = true := by
  obtain ⟨g1, g2, g3⟩ := tryKeeps1_guard ht
  simp only [slow1Pair0, h1, h2, g1, g2, g3, ht, Bool.true_and, Bool.true_or]
lemma slow1Pair0_or {r v c a b}
    (h1 : isNotSpec1 a.tg = true) (h2 : isNotSpec1 b.tg = true)
    (ht : tryKeeps1 r v a.w.1 b.w.1
      (Nat.lor (Nat.land (Nat.lor a.p b.p) (Nat.xor (Nat.lor a.n b.n) top)) (takeTwo c a.s b.s))
      a.s b.s ((Nat.lor a.p b.p, Nat.lor a.n b.n), .tNone)
      (a.w.1, if isDeg3Tag a.tg then .tSpec0 else .tNone)
      (b.w.1, if isDeg3Tag b.tg then .tSpec0 else .tNone)
      (isNotSpec0 a.tg) (isNotSpec0 b.tg)
      (Nat.beq (Nat.land a.u b.n) 0) (Nat.beq (Nat.land b.u a.n) 0) = true) :
    slow1Pair0 r v c a b = true := by
  obtain ⟨g1, g2, g3⟩ := tryKeeps1_guard ht
  simp only [slow1Pair0, h1, h2, g1, g2, g3, ht, Bool.true_and, Bool.or_true]
lemma slow1Pair1_and {r v c a b}
    (h1 : isNotSpec0 a.tg = true) (h2 : isNotSpec0 b.tg = true)
    (ht : tryKeeps1 r v a.w.1 b.w.1
      (Nat.lor (Nat.xor (Nat.land a.p b.p) (Nat.land a.n b.n)) (takeTwo c a.s b.s))
      a.s b.s ((Nat.land a.p b.p, Nat.land a.n b.n),
        if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone)
      a.w b.w (isNoneTag a.tg) (isNoneTag b.tg)
      (Nat.beq (Nat.land a.up b.p) a.up && Nat.beq (Nat.land a.un b.n) a.un)
      (Nat.beq (Nat.land b.up a.p) b.up && Nat.beq (Nat.land b.un a.n) b.un) = true) :
    slow1Pair1 r v c a b = true := by
  obtain ⟨g1, g2, g3⟩ := tryKeeps1_guard ht
  simp only [slow1Pair1, h1, h2, g1, g2, g3, ht, Bool.true_and, Bool.true_or]
lemma slow1Pair1_or {r v c a b}
    (h1 : isNotSpec1 a.tg = true) (h2 : isNotSpec1 b.tg = true)
    (ht : tryKeeps1 r v a.w.1 b.w.1
      (Nat.lor (Nat.xor (Nat.lor a.p b.p) (Nat.lor a.n b.n)) (takeTwo c a.s b.s))
      a.s b.s ((Nat.lor a.p b.p, Nat.lor a.n b.n), .tNone)
      (a.w.1, if isDeg3Tag a.tg then .tSpec0 else .tNone)
      (b.w.1, if isDeg3Tag b.tg then .tSpec0 else .tNone)
      (isNotSpec0 a.tg) (isNotSpec0 b.tg)
      (Nat.beq (Nat.land a.up b.n) 0 && Nat.beq (Nat.land a.un b.p) 0)
      (Nat.beq (Nat.land b.up a.n) 0 && Nat.beq (Nat.land b.un a.p) 0) = true) :
    slow1Pair1 r v c a b = true := by
  obtain ⟨g1, g2, g3⟩ := tryKeeps1_guard ht
  simp only [slow1Pair1, h1, h2, g1, g2, g3, ht, Bool.true_and, Bool.or_true]
lemma slow2Pair0_and {r v c a b}
    (h1 : isNotSpec0 a.tg = true) (h2 : isNotSpec0 b.tg = true)
    (ga : (isNoneTag a.tg || Nat.beq (Nat.land a.u b.p) a.u) = true)
    (gb : (isNoneTag b.tg || Nat.beq (Nat.land b.u a.p) b.u) = true)
    (ht : tryKeeps2 r v a.w.1 b.w.1
      (Nat.lor (Nat.land (Nat.land a.p b.p) (Nat.xor (Nat.land a.n b.n) top)) (takeTwo c a.s b.s))
      a.s b.s ((Nat.land a.p b.p, Nat.land a.n b.n),
        if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone)
      a.w b.w (isNoneTag a.tg) (isNoneTag b.tg) = true) :
    slow2Pair0 r v c a b = true := by
  simp only [slow2Pair0, h1, h2, ga, gb, ht, Bool.true_and, Bool.true_or]
lemma slow2Pair0_or {r v c a b}
    (h1 : isNotSpec1 a.tg = true) (h2 : isNotSpec1 b.tg = true)
    (ga : (isNotSpec0 a.tg || Nat.beq (Nat.land a.u b.n) 0) = true)
    (gb : (isNotSpec0 b.tg || Nat.beq (Nat.land b.u a.n) 0) = true)
    (ht : tryKeeps2 r v a.w.1 b.w.1
      (Nat.lor (Nat.land (Nat.lor a.p b.p) (Nat.xor (Nat.lor a.n b.n) top)) (takeTwo c a.s b.s))
      a.s b.s ((Nat.lor a.p b.p, Nat.lor a.n b.n), .tNone)
      (a.w.1, if isDeg3Tag a.tg then .tSpec0 else .tNone)
      (b.w.1, if isDeg3Tag b.tg then .tSpec0 else .tNone)
      (isNotSpec0 a.tg) (isNotSpec0 b.tg) = true) :
    slow2Pair0 r v c a b = true := by
  simp only [slow2Pair0, h1, h2, ga, gb, ht, Bool.true_and, Bool.or_true]
lemma slow2Pair1_and {r v c a b}
    (h1 : isNotSpec0 a.tg = true) (h2 : isNotSpec0 b.tg = true)
    (ga : (isNoneTag a.tg || (Nat.beq (Nat.land a.up b.p) a.up && Nat.beq (Nat.land a.un b.n) a.un)) = true)
    (gb : (isNoneTag b.tg || (Nat.beq (Nat.land b.up a.p) b.up && Nat.beq (Nat.land b.un a.n) b.un)) = true)
    (ht : tryKeeps2 r v a.w.1 b.w.1
      (Nat.lor (Nat.xor (Nat.land a.p b.p) (Nat.land a.n b.n)) (takeTwo c a.s b.s))
      a.s b.s ((Nat.land a.p b.p, Nat.land a.n b.n),
        if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone)
      a.w b.w (isNoneTag a.tg) (isNoneTag b.tg) = true) :
    slow2Pair1 r v c a b = true := by
  simp only [slow2Pair1, h1, h2, ga, gb, ht, Bool.true_and, Bool.true_or]
lemma slow2Pair1_or {r v c a b}
    (h1 : isNotSpec1 a.tg = true) (h2 : isNotSpec1 b.tg = true)
    (ga : (isNotSpec0 a.tg || (Nat.beq (Nat.land a.up b.n) 0 && Nat.beq (Nat.land a.un b.p) 0)) = true)
    (gb : (isNotSpec0 b.tg || (Nat.beq (Nat.land b.up a.n) 0 && Nat.beq (Nat.land b.un a.p) 0)) = true)
    (ht : tryKeeps2 r v a.w.1 b.w.1
      (Nat.lor (Nat.xor (Nat.lor a.p b.p) (Nat.lor a.n b.n)) (takeTwo c a.s b.s))
      a.s b.s ((Nat.lor a.p b.p, Nat.lor a.n b.n), .tNone)
      (a.w.1, if isDeg3Tag a.tg then .tSpec0 else .tNone)
      (b.w.1, if isDeg3Tag b.tg then .tSpec0 else .tNone)
      (isNotSpec0 a.tg) (isNotSpec0 b.tg) = true) :
    slow2Pair1 r v c a b = true := by
  simp only [slow2Pair1, h1, h2, ga, gb, ht, Bool.true_and, Bool.or_true]
lemma pair_and_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {τ : Sig → Tag} {v : List Wire}
    {r : List Wire → Bool}
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hrep : Represents v (insert a (insert b U)) τ) (hle : m ≤ k)
    (fresh : bin false a b ∉ insert a (insert b U))
    (hra : τ a ≠ .tSpec0 ∧ (τ a ≠ .tNone → a ∉ U))
    (hrb : τ b ≠ .tSpec0 ∧ (τ b ≠ .tNone → b ∉ U))
    (l : TRestricted m t (insert (bin false a b) U) (updAndTag τ a b))
    (ih : ∀ w : List Wire, Represents w (insert (bin false a b) U) (updAndTag τ a b) → r w = true) :
    let lim := k - t + 1
    let c0 := coverageW false v
    let c1 := coverageW true v
    (t = 0 →
      (v.length = lim + 1 → fastPair0 r v c0 (mkAct0 c0.2.1 (a, τ a)) (mkAct0 c0.2.1 (b, τ b)) = true) ∧
      (v.length = lim → slow1Pair0 r v c0 (mkAct0 c0.2.1 (a, τ a)) (mkAct0 c0.2.1 (b, τ b)) = true) ∧
      slow2Pair0 r v c0 (mkAct0 c0.2.1 (a, τ a)) (mkAct0 c0.2.1 (b, τ b)) = true) ∧
    (t ≠ 0 →
      (v.length = lim + 1 → fastPair1 r v c1 (mkAct1 c1.2.1 (a, τ a)) (mkAct1 c1.2.1 (b, τ b)) = true) ∧
      (v.length = lim → slow1Pair1 r v c1 (mkAct1 c1.2.1 (a, τ a)) (mkAct1 c1.2.1 (b, τ b)) = true) ∧
      slow2Pair1 r v c1 (mkAct1 c1.2.1 (a, τ a)) (mkAct1 c1.2.1 (b, τ b)) = true) := by
  obtain ⟨hndS, heS, htag⟩ := hrep
  have hval : ∀ x ∈ sigsOf v, Valid x := by
    intro x hx
    rcases Finset.mem_insert.mp (heS ▸ List.mem_toFinset.mpr hx) with rfl | hx1
    · exact ha.1
    rcases Finset.mem_insert.mp hx1 with rfl | hxU
    · exact hb.1
    · exact (live_proper l.live x (Finset.mem_insert_of_mem hxU)).1
  have ahS : a ∈ sigsOf v := List.mem_toFinset.mp (heS.symm ▸ Finset.mem_insert_self _ _)
  have bhS : b ∈ sigsOf v := List.mem_toFinset.mp (heS.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have ah : (a, τ a) ∈ v := (mem_sigsOf_iff htag).mpr ahS
  have bh : (b, τ b) ∈ v := (mem_sigsOf_iff htag).mpr bhS
  let rest := droppedW [a, b] v
  let gTag : Tag := if isDeg3Tag (τ a) || isDeg3Tag (τ b) then .tSpec0 else .tNone
  let g : Wire := (bin false a b, gTag)
  let h : List Wire := (if a ∈ U then [(a, τ a)] else []) ++ (if b ∈ U then [(b, τ b)] else [])
  have hSigsH : sigsOf h = keepOf U [a, b] := by
    by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U <;> simp [h, sigsOf, keepOf, haU, hbU]
  obtain ⟨hn, eq⟩ := edit_list (del := [a, b]) (U := U) hndS (by simp [hab]) (by simpa using heS)
  have hSigsHR : sigsOf (h ++ rest) = keepOf U [a, b] ++ dropped [a, b] (sigsOf v) := by
    change (h ++ rest).map Prod.fst = _
    rw [List.map_append, show h.map Prod.fst = keepOf U [a, b] from hSigsH,
      show rest.map Prod.fst = dropped [a, b] (sigsOf v) from sigsOf_droppedW [a, b] v]
  have nn : bin false a b ∉ sigsOf v := fun hm => fresh (heS ▸ List.mem_toFinset.mpr hm)
  have nz : bin false a b ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hnd : (sigsOf (g :: (h ++ rest))).Nodup := by
    change (bin false a b :: sigsOf (h ++ rest)).Nodup; rw [hSigsHR]
    exact List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm), hn⟩
  have e : (sigsOf (g :: (h ++ rest))).toFinset = insert (bin false a b) U := by
    change (bin false a b :: sigsOf (h ++ rest)).toFinset = _; rw [List.toFinset_cons, hSigsHR, eq]
  have htag' : ∀ w ∈ g :: (h ++ rest), w.2 = updAndTag τ a b w.1 := by
    intro w hw; rcases List.mem_cons.mp hw with rfl | hw'
    · simp only [g, gTag, updAndTag, ite_true]; cases τ a <;> cases τ b <;> rfl
    · have hwV : w ∈ v := by
        rcases List.mem_append.mp hw' with hh | hr
        · rcases List.mem_append.mp hh with h1 | h2
          · by_cases haU : a ∈ U
            · simp only [haU, ite_true, List.mem_singleton] at h1; exact h1 ▸ ah
            · simp [haU] at h1
          · by_cases hbU : b ∈ U
            · simp only [hbU, ite_true, List.mem_singleton] at h2; exact h2 ▸ bh
            · simp [hbU] at h2
        · exact List.mem_of_mem_filter hr
      have hwNe : w.1 ≠ bin false a b := fun heq => nn (heq ▸ List.mem_map_of_mem hwV)
      simp [updAndTag, hwNe, htag w hwV]
  have hr := ih _ ⟨hnd, e, htag'⟩
  obtain ⟨ht, hc⟩ := live_size l.live
  rw [← e, List.toFinset_card_of_nodup hnd] at hc
  simp only [sigsOf, List.map_cons, List.map_append, List.length_cons, List.length_append,
    List.length_map] at hc
  have hav : gateAvail (bin false a b) v = true :=
    gateAvail_eq_true nn (live_proper l.live _ (Finset.mem_insert_self _ _))
  have hnsa : isNotSpec0 (τ a) = true := by cases hta : τ a <;> simp [isNotSpec0]; exact hra.1 hta
  have hnsb : isNotSpec0 (τ b) = true := by cases htb : τ b <;> simp [isNotSpec0]; exact hrb.1 htb
  have hka : a ∈ U → isNoneTag (τ a) = true := fun hm => by
    cases hta : τ a <;> simp [isNoneTag]; all_goals exact hra.2 (by simp [hta]) hm
  have hkb : b ∈ U → isNoneTag (τ b) = true := fun hm => by
    cases htb : τ b <;> simp [isNoneTag]; all_goals exact hrb.2 (by simp [htb]) hm
  have hdrop : dropTwo a b v = rest := dropTwo_eq a b v
  have cv := live_cover l.live e
  simp only [sigsOf, List.map_cons, List.map_append, unionSep, union_append] at cv
  have hcv' : (sep (decide (0 < t)) (bin false a b) ||| unionSep (decide (0 < t)) (sigsOf rest)) |||
      unionSepW (decide (0 < t)) h = top := by
    rw [unionSepW_eq, ← cv]; unfold sigsOf; ac_rfl
  obtain ⟨hlen, hmask⟩ := two_rest (decide (0 < t)) hndS hval ahS bhS hab
  rw [sigsOf_length, ← sigsOf_droppedW, sigsOf_length] at hlen
  change v.length - 2 = rest.length at hlen
  rw [← sigsOf_droppedW] at hmask
  change takeTwo (coverage (decide (0 < t)) (sigsOf v)) (sep (decide (0 < t)) a) (sep (decide (0 < t)) b) =
    unionSep (decide (0 < t)) (sigsOf rest) at hmask
  have hdisjAB := two_rest_disj (decide (0 < t)) hndS hval ahS bhS hab
  have hdisjBA := two_rest_disj (decide (0 < t)) hndS hval bhS ahS hab.symm
  have hvc := validCov_coverage (decide (0 < t)) hval
  constructor
  · intro ht0; subst ht0
    have hdt0 : decide (0 < 0) = false := rfl
    rw [hdt0] at hcv' hmask hdisjAB hdisjBA hvc
    have hcv0 : Nat.lor (Nat.lor (sep0 (bin false a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b)))
        (unionSepW false h) = top := by simpa [hmask, sep0_eq] using hcv'
    have h0zero : ∀ x : Nat, Nat.land x 0 = 0 := fun x => Nat.and_zero x
    have huA0 : a ∉ U → Nat.land (Nat.land (coverage false (sigsOf v)).2.1 (sep0 a)) b.1 =
        Nat.land (coverage false (sigsOf v)).2.1 (sep0 a) := fun hna => by
      by_cases hbU : b ∈ U
      · exact unique_and_0 hvc (by simpa [sep0_eq] using hdisjAB) (by simpa [h, hna, hbU, unionSepW, sep0_eq] using hcv0)
      · exact unique_and_0 hvc (h0zero _) (by simpa [h, hna, hbU, unionSepW] using hcv0)
    have huB0 : b ∉ U → Nat.land (Nat.land (coverage false (sigsOf v)).2.1 (sep0 b)) a.1 =
        Nat.land (coverage false (sigsOf v)).2.1 (sep0 b) := fun hnb => by
      have hcomm : Nat.lor (Nat.lor (sep0 (bin false b a)) (takeTwo (coverage false (sigsOf v)) (sep0 b) (sep0 a)))
          (unionSepW false h) = top := by
        rw [bin_comm]; simpa [takeTwo, Nat.or_comm, Nat.and_comm] using hcv0
      by_cases haU : a ∈ U
      · exact unique_and_0 hvc (by simpa [sep0_eq] using hdisjBA) (by simpa [h, haU, hnb, unionSepW, sep0_eq] using hcomm)
      · exact unique_and_0 hvc (h0zero _) (by simpa [h, haU, hnb, unionSepW] using hcomm)
    refine ⟨?_, ?_, ?_⟩
    · intro hlv
      have hh0 : h.length = 0 := by omega
      have hna : a ∉ U := fun hm => by simp [h, hm] at hh0
      have hnb : b ∉ U := fun hm => by simp [h, hm] at hh0
      have htop : Nat.lor (sep0 (bin false a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b)) = top := by
        simpa [h, hna, hnb, unionSepW] using hcv0
      have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, hna, hnb] using hr
      rw [coverageW_eq]
      exact fastPair0_and hnsa hnsb (huA0 hna) (huB0 hnb) htop hav hr0
    · intro hlv
      have hh1 : h.length ≤ 1 := by omega
      rw [coverageW_eq]
      apply slow1Pair0_and hnsa hnsb
      by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U
      · simp [h, haU, hbU] at hh1
      · have htopA : Nat.lor (Nat.lor (sep0 (bin false a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 a) = top := by
          simpa [h, haU, hbU, unionSepW, sep0_eq] using hcv0
        have hrA : r (g :: (a, τ a) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact tryKeeps1_A (hka haU) (Nat.beq_eq.mpr (huB0 hbU)) htopA hav hrA
      · have htopB : Nat.lor (Nat.lor (sep0 (bin false a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 b) = top := by
          simpa [h, haU, hbU, unionSepW, sep0_eq] using hcv0
        have hrB : r (g :: (b, τ b) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact tryKeeps1_B (hkb hbU) (Nat.beq_eq.mpr (huA0 haU)) htopB hav hrB
      · have htop : Nat.lor (sep0 (bin false a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b)) = top := by
          simpa [h, haU, hbU, unionSepW] using hcv0
        have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact tryKeeps1_0 (Nat.beq_eq.mpr (huA0 haU)) (Nat.beq_eq.mpr (huB0 hbU)) htop hav hr0
    · rw [coverageW_eq]
      by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U
      · have htopAB : Nat.lor (Nat.lor (Nat.lor (sep0 (bin false a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 a)) (sep0 b) = top := by
          have : unionSepW false h = sep0 a ||| sep0 b := by simp [h, haU, hbU, unionSepW, sep0_eq]
          rw [this] at hcv0; exact (Nat.or_assoc _ _ _).trans hcv0
        have hrAB : r (g :: (a, τ a) :: (b, τ b) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair0_and hnsa hnsb (bor_l (hka haU)) (bor_l (hkb hbU)) (tryKeeps2_AB (hka haU) (hkb hbU) htopAB hav hrAB)
      · have htopA : Nat.lor (Nat.lor (sep0 (bin false a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 a) = top := by
          simpa [h, haU, hbU, unionSepW, sep0_eq] using hcv0
        have hrA : r (g :: (a, τ a) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair0_and hnsa hnsb (bor_l (hka haU)) (bor_r (Nat.beq_eq.mpr (huB0 hbU))) (tryKeeps2_A (hka haU) htopA hav hrA)
      · have htopB : Nat.lor (Nat.lor (sep0 (bin false a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 b) = top := by
          simpa [h, haU, hbU, unionSepW, sep0_eq] using hcv0
        have hrB : r (g :: (b, τ b) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair0_and hnsa hnsb (bor_r (Nat.beq_eq.mpr (huA0 haU))) (bor_l (hkb hbU)) (tryKeeps2_B (hkb hbU) htopB hav hrB)
      · have htop : Nat.lor (sep0 (bin false a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b)) = top := by
          simpa [h, haU, hbU, unionSepW] using hcv0
        have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair0_and hnsa hnsb (bor_r (Nat.beq_eq.mpr (huA0 haU))) (bor_r (Nat.beq_eq.mpr (huB0 hbU))) (tryKeeps2_0 htop hav hr0)
  · intro ht0
    have hdt : decide (0 < t) = true := decide_eq_true (by omega)
    rw [hdt] at hcv' hmask hdisjAB hdisjBA hvc
    have hcv1 : Nat.lor (Nat.lor (sep1 (bin false a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b)))
        (unionSepW true h) = top := by simpa [hmask, sep1_eq] using hcv'
    have h0zero : ∀ x : Nat, Nat.land x 0 = 0 := fun x => Nat.and_zero x
    have huA1 : a ∉ U →
        Nat.land (Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 a)) a.1) b.1 =
          Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 a)) a.1 ∧
        Nat.land (Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 a)) a.2) b.2 =
          Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 a)) a.2 := fun hna => by
      by_cases hbU : b ∈ U
      · exact unique_and_1 hvc (by simpa [sep1_eq] using hdisjAB) (by simpa [h, hna, hbU, unionSepW, sep1_eq] using hcv1)
      · exact unique_and_1 hvc (h0zero _) (by simpa [h, hna, hbU, unionSepW] using hcv1)
    have huB1 : b ∉ U →
        Nat.land (Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 b)) b.1) a.1 =
          Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 b)) b.1 ∧
        Nat.land (Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 b)) b.2) a.2 =
          Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 b)) b.2 := fun hnb => by
      have hcomm : Nat.lor (Nat.lor (sep1 (bin false b a)) (takeTwo (coverage true (sigsOf v)) (sep1 b) (sep1 a)))
          (unionSepW true h) = top := by
        rw [bin_comm]; simpa [takeTwo, Nat.or_comm, Nat.and_comm] using hcv1
      by_cases haU : a ∈ U
      · exact unique_and_1 hvc (by simpa [sep1_eq] using hdisjBA) (by simpa [h, haU, hnb, unionSepW, sep1_eq] using hcomm)
      · exact unique_and_1 hvc (h0zero _) (by simpa [h, haU, hnb, unionSepW] using hcomm)
    refine ⟨?_, ?_, ?_⟩
    · intro hlv
      have hh0 : h.length = 0 := by omega
      have hna : a ∉ U := fun hm => by simp [h, hm] at hh0
      have hnb : b ∉ U := fun hm => by simp [h, hm] at hh0
      have htop : Nat.lor (sep1 (bin false a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b)) = top := by
        simpa [h, hna, hnb, unionSepW] using hcv1
      have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, hna, hnb] using hr
      have ⟨u1, u2⟩ := huA1 hna; have ⟨v1, v2⟩ := huB1 hnb
      rw [coverageW_eq]
      exact fastPair1_and hnsa hnsb u1 v1 u2 v2 htop hav hr0
    · intro hlv
      have hh1 : h.length ≤ 1 := by omega
      rw [coverageW_eq]
      apply slow1Pair1_and hnsa hnsb
      by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U
      · simp [h, haU, hbU] at hh1
      · have htopA : Nat.lor (Nat.lor (sep1 (bin false a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 a) = top := by
          simpa [h, haU, hbU, unionSepW, sep1_eq] using hcv1
        have hrA : r (g :: (a, τ a) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨v1, v2⟩ := huB1 hbU
        exact tryKeeps1_A (hka haU) (band2 (Nat.beq_eq.mpr v1) (Nat.beq_eq.mpr v2)) htopA hav hrA
      · have htopB : Nat.lor (Nat.lor (sep1 (bin false a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 b) = top := by
          simpa [h, haU, hbU, unionSepW, sep1_eq] using hcv1
        have hrB : r (g :: (b, τ b) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨u1, u2⟩ := huA1 haU
        exact tryKeeps1_B (hkb hbU) (band2 (Nat.beq_eq.mpr u1) (Nat.beq_eq.mpr u2)) htopB hav hrB
      · have htop : Nat.lor (sep1 (bin false a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b)) = top := by
          simpa [h, haU, hbU, unionSepW] using hcv1
        have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨u1, u2⟩ := huA1 haU; have ⟨v1, v2⟩ := huB1 hbU
        exact tryKeeps1_0 (band2 (Nat.beq_eq.mpr u1) (Nat.beq_eq.mpr u2)) (band2 (Nat.beq_eq.mpr v1) (Nat.beq_eq.mpr v2)) htop hav hr0
    · rw [coverageW_eq]
      by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U
      · have htopAB : Nat.lor (Nat.lor (Nat.lor (sep1 (bin false a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 a)) (sep1 b) = top := by
          have : unionSepW true h = sep1 a ||| sep1 b := by simp [h, haU, hbU, unionSepW, sep1_eq]
          rw [this] at hcv1; exact (Nat.or_assoc _ _ _).trans hcv1
        have hrAB : r (g :: (a, τ a) :: (b, τ b) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair1_and hnsa hnsb (bor_l (hka haU)) (bor_l (hkb hbU)) (tryKeeps2_AB (hka haU) (hkb hbU) htopAB hav hrAB)
      · have htopA : Nat.lor (Nat.lor (sep1 (bin false a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 a) = top := by
          simpa [h, haU, hbU, unionSepW, sep1_eq] using hcv1
        have hrA : r (g :: (a, τ a) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨v1, v2⟩ := huB1 hbU
        exact slow2Pair1_and hnsa hnsb (bor_l (hka haU)) (bor_r (band2 (Nat.beq_eq.mpr v1) (Nat.beq_eq.mpr v2))) (tryKeeps2_A (hka haU) htopA hav hrA)
      · have htopB : Nat.lor (Nat.lor (sep1 (bin false a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 b) = top := by
          simpa [h, haU, hbU, unionSepW, sep1_eq] using hcv1
        have hrB : r (g :: (b, τ b) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨u1, u2⟩ := huA1 haU
        exact slow2Pair1_and hnsa hnsb (bor_r (band2 (Nat.beq_eq.mpr u1) (Nat.beq_eq.mpr u2))) (bor_l (hkb hbU)) (tryKeeps2_B (hkb hbU) htopB hav hrB)
      · have htop : Nat.lor (sep1 (bin false a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b)) = top := by
          simpa [h, haU, hbU, unionSepW] using hcv1
        have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨u1, u2⟩ := huA1 haU; have ⟨v1, v2⟩ := huB1 hbU
        exact slow2Pair1_and hnsa hnsb (bor_r (band2 (Nat.beq_eq.mpr u1) (Nat.beq_eq.mpr u2))) (bor_r (band2 (Nat.beq_eq.mpr v1) (Nat.beq_eq.mpr v2))) (tryKeeps2_0 htop hav hr0)
lemma pair_or_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {τ : Sig → Tag} {v : List Wire}
    {r : List Wire → Bool}
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hrep : Represents v (insert a (insert b U)) τ) (hle : m ≤ k)
    (fresh : bin true a b ∉ insert a (insert b U))
    (hra : τ a ≠ .tSpec1 ∧ (τ a = .tSpec0 → a ∉ U))
    (hrb : τ b ≠ .tSpec1 ∧ (τ b = .tSpec0 → b ∉ U))
    (l : TRestricted m t (insert (bin true a b) U) (updOrTag τ a b))
    (ih : ∀ w : List Wire, Represents w (insert (bin true a b) U) (updOrTag τ a b) → r w = true) :
    let lim := k - t + 1
    let c0 := coverageW false v
    let c1 := coverageW true v
    (t = 0 →
      (v.length = lim + 1 → fastPair0 r v c0 (mkAct0 c0.2.1 (a, τ a)) (mkAct0 c0.2.1 (b, τ b)) = true) ∧
      (v.length = lim → slow1Pair0 r v c0 (mkAct0 c0.2.1 (a, τ a)) (mkAct0 c0.2.1 (b, τ b)) = true) ∧
      slow2Pair0 r v c0 (mkAct0 c0.2.1 (a, τ a)) (mkAct0 c0.2.1 (b, τ b)) = true) ∧
    (t ≠ 0 →
      (v.length = lim + 1 → fastPair1 r v c1 (mkAct1 c1.2.1 (a, τ a)) (mkAct1 c1.2.1 (b, τ b)) = true) ∧
      (v.length = lim → slow1Pair1 r v c1 (mkAct1 c1.2.1 (a, τ a)) (mkAct1 c1.2.1 (b, τ b)) = true) ∧
      slow2Pair1 r v c1 (mkAct1 c1.2.1 (a, τ a)) (mkAct1 c1.2.1 (b, τ b)) = true) := by
  obtain ⟨hndS, heS, htag⟩ := hrep
  have hval : ∀ x ∈ sigsOf v, Valid x := by
    intro x hx
    rcases Finset.mem_insert.mp (heS ▸ List.mem_toFinset.mpr hx) with rfl | hx1
    · exact ha.1
    rcases Finset.mem_insert.mp hx1 with rfl | hxU
    · exact hb.1
    · exact (live_proper l.live x (Finset.mem_insert_of_mem hxU)).1
  have ahS : a ∈ sigsOf v := List.mem_toFinset.mp (heS.symm ▸ Finset.mem_insert_self _ _)
  have bhS : b ∈ sigsOf v := List.mem_toFinset.mp (heS.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  let rest := droppedW [a, b] v
  let g : Wire := (bin true a b, .tNone)
  let wa : Wire := (a, if isDeg3Tag (τ a) then .tSpec0 else .tNone)
  let wb : Wire := (b, if isDeg3Tag (τ b) then .tSpec0 else .tNone)
  let h : List Wire := (if a ∈ U then [wa] else []) ++ (if b ∈ U then [wb] else [])
  have hSigsH : sigsOf h = keepOf U [a, b] := by
    by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U <;> simp [h, wa, wb, sigsOf, keepOf, haU, hbU]
  obtain ⟨hn, eq⟩ := edit_list (del := [a, b]) (U := U) hndS (by simp [hab]) (by simpa using heS)
  have hSigsHR : sigsOf (h ++ rest) = keepOf U [a, b] ++ dropped [a, b] (sigsOf v) := by
    change (h ++ rest).map Prod.fst = _
    rw [List.map_append, show h.map Prod.fst = keepOf U [a, b] from hSigsH,
      show rest.map Prod.fst = dropped [a, b] (sigsOf v) from sigsOf_droppedW [a, b] v]
  have nn : bin true a b ∉ sigsOf v := fun hm => fresh (heS ▸ List.mem_toFinset.mpr hm)
  have nz : bin true a b ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hnd : (sigsOf (g :: (h ++ rest))).Nodup := by
    change (bin true a b :: sigsOf (h ++ rest)).Nodup; rw [hSigsHR]
    exact List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm), hn⟩
  have e : (sigsOf (g :: (h ++ rest))).toFinset = insert (bin true a b) U := by
    change (bin true a b :: sigsOf (h ++ rest)).toFinset = _; rw [List.toFinset_cons, hSigsHR, eq]
  have htag' : ∀ w ∈ g :: (h ++ rest), w.2 = updOrTag τ a b w.1 := by
    intro w hw; rcases List.mem_cons.mp hw with rfl | hw'
    · simp [g, updOrTag]
    · rcases List.mem_append.mp hw' with hh | hr
      · rcases List.mem_append.mp hh with h1 | h2
        · by_cases haU : a ∈ U
          · simp only [haU, ite_true, List.mem_singleton] at h1; subst w
            have hneG : a ≠ bin true a b := fun eq' => fresh (eq' ▸ Finset.mem_insert_self _ _)
            have hna0 : τ a ≠ .tSpec0 := fun h0 => hra.2 h0 haU
            simp only [wa, updOrTag, hneG, ite_false]
            cases hta : τ a <;> simp_all [isDeg3Tag]
          · simp [haU] at h1
        · by_cases hbU : b ∈ U
          · simp only [hbU, ite_true, List.mem_singleton] at h2; subst w
            have hneG : b ≠ bin true a b := fun eq' =>
              fresh (eq' ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
            have hnb0 : τ b ≠ .tSpec0 := fun h0 => hrb.2 h0 hbU
            simp only [wb, updOrTag, hneG, hab.symm, false_and, ite_false]
            cases htb : τ b <;> simp_all [isDeg3Tag]
          · simp [hbU] at h2
      · have hwV := List.mem_of_mem_filter hr
        have hnot : w.1 ≠ a ∧ w.1 ≠ b := by
          have hf := (List.mem_filter.mp hr).2
          simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
            List.mem_cons, List.not_mem_nil, or_false, not_or] at hf
          exact hf
        have hneG : w.1 ≠ bin true a b := fun eq' => nn (eq' ▸ List.mem_map_of_mem hwV)
        simp [updOrTag, hneG, hnot.1, hnot.2, htag w hwV]
  have hr := ih _ ⟨hnd, e, htag'⟩
  obtain ⟨ht, hc⟩ := live_size l.live
  rw [← e, List.toFinset_card_of_nodup hnd] at hc
  simp only [sigsOf, List.map_cons, List.map_append, List.length_cons, List.length_append,
    List.length_map] at hc
  have hav : gateAvail (bin true a b) v = true :=
    gateAvail_eq_true nn (live_proper l.live _ (Finset.mem_insert_self _ _))
  have hnsa : isNotSpec1 (τ a) = true := by cases hta : τ a <;> simp [isNotSpec1]; exact hra.1 hta
  have hnsb : isNotSpec1 (τ b) = true := by cases htb : τ b <;> simp [isNotSpec1]; exact hrb.1 htb
  have hka : a ∈ U → isNotSpec0 (τ a) = true := fun hm => by
    cases hta : τ a <;> simp [isNotSpec0]; exact hra.2 hta hm
  have hkb : b ∈ U → isNotSpec0 (τ b) = true := fun hm => by
    cases htb : τ b <;> simp [isNotSpec0]; exact hrb.2 htb hm
  have hdrop : dropTwo a b v = rest := dropTwo_eq a b v
  have cv := live_cover l.live e
  simp only [sigsOf, List.map_cons, List.map_append, unionSep, union_append] at cv
  have hcv' : (sep (decide (0 < t)) (bin true a b) ||| unionSep (decide (0 < t)) (sigsOf rest)) |||
      unionSepW (decide (0 < t)) h = top := by
    rw [unionSepW_eq, ← cv]; unfold sigsOf; ac_rfl
  obtain ⟨hlen, hmask⟩ := two_rest (decide (0 < t)) hndS hval ahS bhS hab
  rw [sigsOf_length, ← sigsOf_droppedW, sigsOf_length] at hlen
  change v.length - 2 = rest.length at hlen
  rw [← sigsOf_droppedW] at hmask
  change takeTwo (coverage (decide (0 < t)) (sigsOf v)) (sep (decide (0 < t)) a) (sep (decide (0 < t)) b) =
    unionSep (decide (0 < t)) (sigsOf rest) at hmask
  have hdisjAB := two_rest_disj (decide (0 < t)) hndS hval ahS bhS hab
  have hdisjBA := two_rest_disj (decide (0 < t)) hndS hval bhS ahS hab.symm
  have hvc := validCov_coverage (decide (0 < t)) hval
  constructor
  · intro ht0; subst ht0
    have hdt0 : decide (0 < 0) = false := rfl
    rw [hdt0] at hcv' hmask hdisjAB hdisjBA hvc
    have hcv0 : Nat.lor (Nat.lor (sep0 (bin true a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b)))
        (unionSepW false h) = top := by simpa [hmask, sep0_eq] using hcv'
    have h0zero : ∀ x : Nat, Nat.land x 0 = 0 := fun x => Nat.and_zero x
    have huA0 : a ∉ U → Nat.land (Nat.land (coverage false (sigsOf v)).2.1 (sep0 a)) b.2 = 0 := fun hna => by
      by_cases hbU : b ∈ U
      · exact unique_or_0 hvc (by simpa [sep0_eq] using hdisjAB) (by simpa [h, wa, wb, hna, hbU, unionSepW, sep0_eq] using hcv0)
      · exact unique_or_0 hvc (h0zero _) (by simpa [h, hna, hbU, unionSepW] using hcv0)
    have huB0 : b ∉ U → Nat.land (Nat.land (coverage false (sigsOf v)).2.1 (sep0 b)) a.2 = 0 := fun hnb => by
      have hcomm : Nat.lor (Nat.lor (sep0 (bin true b a)) (takeTwo (coverage false (sigsOf v)) (sep0 b) (sep0 a)))
          (unionSepW false h) = top := by
        rw [bin_comm]; simpa [takeTwo, Nat.or_comm, Nat.and_comm] using hcv0
      by_cases haU : a ∈ U
      · exact unique_or_0 hvc (by simpa [sep0_eq] using hdisjBA) (by simpa [h, wa, wb, haU, hnb, unionSepW, sep0_eq] using hcomm)
      · exact unique_or_0 hvc (h0zero _) (by simpa [h, haU, hnb, unionSepW] using hcomm)
    refine ⟨?_, ?_, ?_⟩
    · intro hlv
      have hh0 : h.length = 0 := by omega
      have hna : a ∉ U := fun hm => by simp [h, hm] at hh0
      have hnb : b ∉ U := fun hm => by simp [h, hm] at hh0
      have htop : Nat.lor (sep0 (bin true a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b)) = top := by
        simpa [h, hna, hnb, unionSepW] using hcv0
      have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, hna, hnb] using hr
      rw [coverageW_eq]
      exact fastPair0_or hnsa hnsb (huA0 hna) (huB0 hnb) htop hav hr0
    · intro hlv
      have hh1 : h.length ≤ 1 := by omega
      rw [coverageW_eq]
      apply slow1Pair0_or hnsa hnsb
      by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U
      · simp [h, haU, hbU] at hh1
      · have htopA : Nat.lor (Nat.lor (sep0 (bin true a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 a) = top := by
          simpa [h, wa, haU, hbU, unionSepW, sep0_eq] using hcv0
        have hrA : r (g :: wa :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact tryKeeps1_A (hka haU) (Nat.beq_eq.mpr (huB0 hbU)) htopA hav hrA
      · have htopB : Nat.lor (Nat.lor (sep0 (bin true a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 b) = top := by
          simpa [h, wb, haU, hbU, unionSepW, sep0_eq] using hcv0
        have hrB : r (g :: wb :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact tryKeeps1_B (hkb hbU) (Nat.beq_eq.mpr (huA0 haU)) htopB hav hrB
      · have htop : Nat.lor (sep0 (bin true a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b)) = top := by
          simpa [h, haU, hbU, unionSepW] using hcv0
        have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact tryKeeps1_0 (Nat.beq_eq.mpr (huA0 haU)) (Nat.beq_eq.mpr (huB0 hbU)) htop hav hr0
    · rw [coverageW_eq]
      by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U
      · have htopAB : Nat.lor (Nat.lor (Nat.lor (sep0 (bin true a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 a)) (sep0 b) = top := by
          have : unionSepW false h = sep0 a ||| sep0 b := by simp [h, wa, wb, haU, hbU, unionSepW, sep0_eq]
          rw [this] at hcv0; exact (Nat.or_assoc _ _ _).trans hcv0
        have hrAB : r (g :: wa :: wb :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair0_or hnsa hnsb (bor_l (hka haU)) (bor_l (hkb hbU)) (tryKeeps2_AB (hka haU) (hkb hbU) htopAB hav hrAB)
      · have htopA : Nat.lor (Nat.lor (sep0 (bin true a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 a) = top := by
          simpa [h, wa, haU, hbU, unionSepW, sep0_eq] using hcv0
        have hrA : r (g :: wa :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair0_or hnsa hnsb (bor_l (hka haU)) (bor_r (Nat.beq_eq.mpr (huB0 hbU))) (tryKeeps2_A (hka haU) htopA hav hrA)
      · have htopB : Nat.lor (Nat.lor (sep0 (bin true a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 b) = top := by
          simpa [h, wb, haU, hbU, unionSepW, sep0_eq] using hcv0
        have hrB : r (g :: wb :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair0_or hnsa hnsb (bor_r (Nat.beq_eq.mpr (huA0 haU))) (bor_l (hkb hbU)) (tryKeeps2_B (hkb hbU) htopB hav hrB)
      · have htop : Nat.lor (sep0 (bin true a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b)) = top := by
          simpa [h, haU, hbU, unionSepW] using hcv0
        have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair0_or hnsa hnsb (bor_r (Nat.beq_eq.mpr (huA0 haU))) (bor_r (Nat.beq_eq.mpr (huB0 hbU))) (tryKeeps2_0 htop hav hr0)
  · intro ht0
    have hdt : decide (0 < t) = true := decide_eq_true (by omega)
    rw [hdt] at hcv' hmask hdisjAB hdisjBA hvc
    have hcv1 : Nat.lor (Nat.lor (sep1 (bin true a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b)))
        (unionSepW true h) = top := by simpa [hmask, sep1_eq] using hcv'
    have h0zero : ∀ x : Nat, Nat.land x 0 = 0 := fun x => Nat.and_zero x
    have huA1 : a ∉ U →
        Nat.land (Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 a)) a.1) b.2 = 0 ∧
        Nat.land (Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 a)) a.2) b.1 = 0 := fun hna => by
      by_cases hbU : b ∈ U
      · exact unique_or_1 hvc (by simpa [sep1_eq] using hdisjAB) (by simpa [h, wa, wb, hna, hbU, unionSepW, sep1_eq] using hcv1)
      · exact unique_or_1 hvc (h0zero _) (by simpa [h, hna, hbU, unionSepW] using hcv1)
    have huB1 : b ∉ U →
        Nat.land (Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 b)) b.1) a.2 = 0 ∧
        Nat.land (Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 b)) b.2) a.1 = 0 := fun hnb => by
      have hcomm : Nat.lor (Nat.lor (sep1 (bin true b a)) (takeTwo (coverage true (sigsOf v)) (sep1 b) (sep1 a)))
          (unionSepW true h) = top := by
        rw [bin_comm]; simpa [takeTwo, Nat.or_comm, Nat.and_comm] using hcv1
      by_cases haU : a ∈ U
      · exact unique_or_1 hvc (by simpa [sep1_eq] using hdisjBA) (by simpa [h, wa, wb, haU, hnb, unionSepW, sep1_eq] using hcomm)
      · exact unique_or_1 hvc (h0zero _) (by simpa [h, haU, hnb, unionSepW] using hcomm)
    refine ⟨?_, ?_, ?_⟩
    · intro hlv
      have hh0 : h.length = 0 := by omega
      have hna : a ∉ U := fun hm => by simp [h, hm] at hh0
      have hnb : b ∉ U := fun hm => by simp [h, hm] at hh0
      have htop : Nat.lor (sep1 (bin true a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b)) = top := by
        simpa [h, hna, hnb, unionSepW] using hcv1
      have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, hna, hnb] using hr
      have ⟨u1, u2⟩ := huA1 hna; have ⟨v1, v2⟩ := huB1 hnb
      rw [coverageW_eq]
      exact fastPair1_or hnsa hnsb u1 v1 u2 v2 htop hav hr0
    · intro hlv
      have hh1 : h.length ≤ 1 := by omega
      rw [coverageW_eq]
      apply slow1Pair1_or hnsa hnsb
      by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U
      · simp [h, haU, hbU] at hh1
      · have htopA : Nat.lor (Nat.lor (sep1 (bin true a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 a) = top := by
          simpa [h, wa, haU, hbU, unionSepW, sep1_eq] using hcv1
        have hrA : r (g :: wa :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨v1, v2⟩ := huB1 hbU
        exact tryKeeps1_A (hka haU) (band2 (Nat.beq_eq.mpr v1) (Nat.beq_eq.mpr v2)) htopA hav hrA
      · have htopB : Nat.lor (Nat.lor (sep1 (bin true a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 b) = top := by
          simpa [h, wb, haU, hbU, unionSepW, sep1_eq] using hcv1
        have hrB : r (g :: wb :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨u1, u2⟩ := huA1 haU
        exact tryKeeps1_B (hkb hbU) (band2 (Nat.beq_eq.mpr u1) (Nat.beq_eq.mpr u2)) htopB hav hrB
      · have htop : Nat.lor (sep1 (bin true a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b)) = top := by
          simpa [h, haU, hbU, unionSepW] using hcv1
        have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨u1, u2⟩ := huA1 haU; have ⟨v1, v2⟩ := huB1 hbU
        exact tryKeeps1_0 (band2 (Nat.beq_eq.mpr u1) (Nat.beq_eq.mpr u2)) (band2 (Nat.beq_eq.mpr v1) (Nat.beq_eq.mpr v2)) htop hav hr0
    · rw [coverageW_eq]
      by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U
      · have htopAB : Nat.lor (Nat.lor (Nat.lor (sep1 (bin true a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 a)) (sep1 b) = top := by
          have : unionSepW true h = sep1 a ||| sep1 b := by simp [h, wa, wb, haU, hbU, unionSepW, sep1_eq]
          rw [this] at hcv1; exact (Nat.or_assoc _ _ _).trans hcv1
        have hrAB : r (g :: wa :: wb :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair1_or hnsa hnsb (bor_l (hka haU)) (bor_l (hkb hbU)) (tryKeeps2_AB (hka haU) (hkb hbU) htopAB hav hrAB)
      · have htopA : Nat.lor (Nat.lor (sep1 (bin true a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 a) = top := by
          simpa [h, wa, haU, hbU, unionSepW, sep1_eq] using hcv1
        have hrA : r (g :: wa :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨v1, v2⟩ := huB1 hbU
        exact slow2Pair1_or hnsa hnsb (bor_l (hka haU)) (bor_r (band2 (Nat.beq_eq.mpr v1) (Nat.beq_eq.mpr v2))) (tryKeeps2_A (hka haU) htopA hav hrA)
      · have htopB : Nat.lor (Nat.lor (sep1 (bin true a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 b) = top := by
          simpa [h, wb, haU, hbU, unionSepW, sep1_eq] using hcv1
        have hrB : r (g :: wb :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨u1, u2⟩ := huA1 haU
        exact slow2Pair1_or hnsa hnsb (bor_r (band2 (Nat.beq_eq.mpr u1) (Nat.beq_eq.mpr u2))) (bor_l (hkb hbU)) (tryKeeps2_B (hkb hbU) htopB hav hrB)
      · have htop : Nat.lor (sep1 (bin true a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b)) = top := by
          simpa [h, haU, hbU, unionSepW] using hcv1
        have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨u1, u2⟩ := huA1 haU; have ⟨v1, v2⟩ := huB1 hbU
        exact slow2Pair1_or hnsa hnsb (bor_r (band2 (Nat.beq_eq.mpr u1) (Nat.beq_eq.mpr u2))) (bor_r (band2 (Nat.beq_eq.mpr v1) (Nat.beq_eq.mpr v2))) (tryKeeps2_0 htop hav hr0)
lemma trestricted_congr {k t S τ₁ τ₂} (h : TRestricted k t S τ₁)
    (he : ∀ x ∈ S, τ₁ x = τ₂ x) : TRestricted k t S τ₂ := by
  induction h generalizing τ₂ with
  | stop => exact TRestricted.stop
  | @unary k t U a τ₁ ha hf hr1 hr2 tail ih =>
    have hae := he a (Finset.mem_insert_self _ _)
    refine TRestricted.unary ha hf (hae ▸ hr1) (hae ▸ hr2) (ih ?_)
    intro x hx; unfold updUnaryTag
    rcases Finset.mem_insert.mp hx with rfl | hxU
    · simp [hae]
    · have hne : x ≠ neg a := fun e => hf (e ▸ Finset.mem_insert_of_mem hxU)
      simp [hne, he x (Finset.mem_insert_of_mem hxU)]
  | @binaryAnd k t U a b τ₁ ha hb hab hf hra hrb tail ih =>
    have hae := he a (Finset.mem_insert_self _ _)
    have hbe := he b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    refine TRestricted.binaryAnd ha hb hab hf (hae ▸ hra) (hbe ▸ hrb) (ih ?_)
    intro x hx; unfold updAndTag
    rcases Finset.mem_insert.mp hx with rfl | hxU
    · simp [hae, hbe]
    · have hne : x ≠ bin false a b := fun e => hf (e ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU))
      simp [hne, he x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU))]
  | @binaryOr k t U a b τ₁ ha hb hab hf hra hrb tail ih =>
    have hae := he a (Finset.mem_insert_self _ _)
    have hbe := he b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    refine TRestricted.binaryOr ha hb hab hf (hae ▸ hra) (hbe ▸ hrb) (ih ?_)
    intro x hx; unfold updOrTag
    rcases Finset.mem_insert.mp hx with rfl | hxU
    · simp
    · have hne : x ≠ bin true a b := fun e => hf (e ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU))
      simp [hne, hae, hbe, he x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU))]
lemma binary_dispatch {k t : Nat} {a b : Wire} {v : List Wire} {r : List Wire → Bool}
    (ha : a ∈ v) (hb : b ∈ v) (hne : a ≠ b)
    (h1 : let lim := k - t + 1; let c0 := coverageW false v; let c1 := coverageW true v
      (t = 0 →
        (v.length = lim + 1 → fastPair0 r v c0 (mkAct0 c0.2.1 a) (mkAct0 c0.2.1 b) = true) ∧
        (v.length = lim → slow1Pair0 r v c0 (mkAct0 c0.2.1 a) (mkAct0 c0.2.1 b) = true) ∧
        slow2Pair0 r v c0 (mkAct0 c0.2.1 a) (mkAct0 c0.2.1 b) = true) ∧
      (t ≠ 0 →
        (v.length = lim + 1 → fastPair1 r v c1 (mkAct1 c1.2.1 a) (mkAct1 c1.2.1 b) = true) ∧
        (v.length = lim → slow1Pair1 r v c1 (mkAct1 c1.2.1 a) (mkAct1 c1.2.1 b) = true) ∧
        slow2Pair1 r v c1 (mkAct1 c1.2.1 a) (mkAct1 c1.2.1 b) = true))
    (h2 : let lim := k - t + 1; let c0 := coverageW false v; let c1 := coverageW true v
      (t = 0 →
        (v.length = lim + 1 → fastPair0 r v c0 (mkAct0 c0.2.1 b) (mkAct0 c0.2.1 a) = true) ∧
        (v.length = lim → slow1Pair0 r v c0 (mkAct0 c0.2.1 b) (mkAct0 c0.2.1 a) = true) ∧
        slow2Pair0 r v c0 (mkAct0 c0.2.1 b) (mkAct0 c0.2.1 a) = true) ∧
      (t ≠ 0 →
        (v.length = lim + 1 → fastPair1 r v c1 (mkAct1 c1.2.1 b) (mkAct1 c1.2.1 a) = true) ∧
        (v.length = lim → slow1Pair1 r v c1 (mkAct1 c1.2.1 b) (mkAct1 c1.2.1 a) = true) ∧
        slow2Pair1 r v c1 (mkAct1 c1.2.1 b) (mkAct1 c1.2.1 a) = true)) :
    binaryMoves k t v.length r v = true := by
  unfold binaryMoves; dsimp only
  by_cases ht0 : t = 0
  · subst ht0
    simp only [Nat.beq_refl, ite_true, buildSeps0_eq, buildActs0_map]
    have hne0 : mkAct0 (coverageW false v).2.1 a ≠ mkAct0 (coverageW false v).2.1 b :=
      fun e => hne (congrArg WAct0.w e)
    have ⟨hf1, hs11, hs21⟩ := h1.1 rfl
    have ⟨hf2, hs12, hs22⟩ := h2.1 rfl
    by_cases hl1 : v.length = k - 0 + 1 + 1
    · simp only [hl1, Nat.beq_refl, ite_true, scanFast0_eq]
      exact scanPairs_complete _ (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) hne0 (hf1 hl1) (hf2 hl1)
    · have hb1 : Nat.beq v.length (k - 0 + 1 + 1) = false := nat_beq_false hl1
      simp only [hb1, Bool.false_eq_true, ite_false]
      by_cases hl2 : v.length = k - 0 + 1
      · simp only [hl2, Nat.beq_refl, ite_true, scanSlow10_eq]
        exact scanPairs_complete _ (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) hne0 (hs11 hl2) (hs12 hl2)
      · have hb2 : Nat.beq v.length (k - 0 + 1) = false := nat_beq_false hl2
        simp only [hb2, Bool.false_eq_true, ite_false, scanSlow20_eq]
        exact scanPairs_complete _ (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) hne0 hs21 hs22
  · have hbf : Nat.beq t 0 = false := nat_beq_false ht0
    simp only [hbf, Bool.false_eq_true, ite_false, buildSeps1_eq, buildActs1_map]
    have hne1 : mkAct1 (coverageW true v).2.1 a ≠ mkAct1 (coverageW true v).2.1 b :=
      fun e => hne (congrArg WAct1.w e)
    have ⟨hf1, hs11, hs21⟩ := h1.2 ht0
    have ⟨hf2, hs12, hs22⟩ := h2.2 ht0
    by_cases hl1 : v.length = k - t + 1 + 1
    · simp only [hl1, Nat.beq_refl, ite_true, scanFast1_eq]
      exact scanPairs_complete _ (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) hne1 (hf1 hl1) (hf2 hl1)
    · have hb1 : Nat.beq v.length (k - t + 1 + 1) = false := nat_beq_false hl1
      simp only [hb1, Bool.false_eq_true, ite_false]
      by_cases hl2 : v.length = k - t + 1
      · simp only [hl2, Nat.beq_refl, ite_true, scanSlow11_eq]
        exact scanPairs_complete _ (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) hne1 (hs11 hl2) (hs12 hl2)
      · have hb2 : Nat.beq v.length (k - t + 1) = false := nat_beq_false hl2
        simp only [hb2, Bool.false_eq_true, ite_false, scanSlow21_eq]
        exact scanPairs_complete _ (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) hne1 hs21 hs22
lemma binary_found_and {m t k : Nat} {U : Finset Sig} {a b : Sig} {τ : Sig → Tag} {v : List Wire}
    {r : List Wire → Bool}
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hrep : Represents v (insert a (insert b U)) τ) (hle : m ≤ k)
    (fresh : bin false a b ∉ insert a (insert b U))
    (hra : τ a ≠ .tSpec0 ∧ (τ a ≠ .tNone → a ∉ U))
    (hrb : τ b ≠ .tSpec0 ∧ (τ b ≠ .tNone → b ∉ U))
    (l : TRestricted m t (insert (bin false a b) U) (updAndTag τ a b))
    (ih : ∀ w : List Wire, Represents w (insert (bin false a b) U) (updAndTag τ a b) → r w = true) :
    binaryMoves k t v.length r v = true := by
  have ahS : a ∈ sigsOf v := List.mem_toFinset.mp (hrep.2.1.symm ▸ Finset.mem_insert_self _ _)
  have bhS : b ∈ sigsOf v := List.mem_toFinset.mp (hrep.2.1.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have ah : (a, τ a) ∈ v := (mem_sigsOf_iff hrep.2.2).mpr ahS
  have bh : (b, τ b) ∈ v := (mem_sigsOf_iff hrep.2.2).mpr bhS
  have h1 := pair_and_found ha hb hab hrep hle fresh hra hrb l ih
  have hrep' : Represents v (insert b (insert a U)) τ :=
    ⟨hrep.1, by rw [Finset.insert_comm b a]; exact hrep.2.1, hrep.2.2⟩
  have hf' : bin false b a ∉ insert b (insert a U) := by rwa [bin_comm false b a, Finset.insert_comm b a]
  have htagEq : ∀ x, updAndTag τ b a x = updAndTag τ a b x := by
    intro x; unfold updAndTag; rw [bin_comm false b a]; simp only [or_comm]
  have l' : TRestricted m t (insert (bin false b a) U) (updAndTag τ b a) := by
    rw [bin_comm false b a]; exact trestricted_congr l (fun x _ => (htagEq x).symm)
  have ih' : ∀ w : List Wire, Represents w (insert (bin false b a) U) (updAndTag τ b a) → r w = true := by
    intro w hw; apply ih w; rw [bin_comm false b a] at hw
    exact ⟨hw.1, hw.2.1, fun x hx => (hw.2.2 x hx).trans (htagEq x.1)⟩
  have h2 := pair_and_found hb ha hab.symm hrep' hle hf' hrb hra l' ih'
  exact binary_dispatch ah bh (fun e => hab (congrArg Prod.fst e)) h1 h2
lemma binary_found_or {m t k : Nat} {U : Finset Sig} {a b : Sig} {τ : Sig → Tag} {v : List Wire}
    {r : List Wire → Bool}
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hrep : Represents v (insert a (insert b U)) τ) (hle : m ≤ k)
    (fresh : bin true a b ∉ insert a (insert b U))
    (hra : τ a ≠ .tSpec1 ∧ (τ a = .tSpec0 → a ∉ U))
    (hrb : τ b ≠ .tSpec1 ∧ (τ b = .tSpec0 → b ∉ U))
    (l : TRestricted m t (insert (bin true a b) U) (updOrTag τ a b))
    (ih : ∀ w : List Wire, Represents w (insert (bin true a b) U) (updOrTag τ a b) → r w = true) :
    binaryMoves k t v.length r v = true := by
  have ahS : a ∈ sigsOf v := List.mem_toFinset.mp (hrep.2.1.symm ▸ Finset.mem_insert_self _ _)
  have bhS : b ∈ sigsOf v := List.mem_toFinset.mp (hrep.2.1.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have ah : (a, τ a) ∈ v := (mem_sigsOf_iff hrep.2.2).mpr ahS
  have bh : (b, τ b) ∈ v := (mem_sigsOf_iff hrep.2.2).mpr bhS
  have h1 := pair_or_found ha hb hab hrep hle fresh hra hrb l ih
  have hrep' : Represents v (insert b (insert a U)) τ :=
    ⟨hrep.1, by rw [Finset.insert_comm b a]; exact hrep.2.1, hrep.2.2⟩
  have hf' : bin true b a ∉ insert b (insert a U) := by rwa [bin_comm true b a, Finset.insert_comm b a]
  have htagEq : ∀ x, updOrTag τ b a x = updOrTag τ a b x := by
    intro x; unfold updOrTag; rw [bin_comm true b a]
    by_cases hg : x = bin true a b
    · simp [hg]
    · by_cases hxa : x = a <;> by_cases hxb : x = b <;> simp_all
  have l' : TRestricted m t (insert (bin true b a) U) (updOrTag τ b a) := by
    rw [bin_comm true b a]; exact trestricted_congr l (fun x _ => (htagEq x).symm)
  have ih' : ∀ w : List Wire, Represents w (insert (bin true b a) U) (updOrTag τ b a) → r w = true := by
    intro w hw; apply ih w; rw [bin_comm true b a] at hw
    exact ⟨hw.1, hw.2.1, fun x hx => (hw.2.2 x hx).trans (htagEq x.1)⟩
  have h2 := pair_or_found hb ha hab.symm hrep' hle hf' hrb hra l' ih'
  exact binary_dispatch ah bh (fun e => hab (congrArg Prod.fst e)) h1 h2
lemma reduced_step {m t S : Nat} {s : Finset Sig} {τ : Sig → Tag} {v : List Wire}
    {u b : List Wire → Bool}
    (h : TRestricted m t s τ) (hb : m ≤ S + 1) (hrep : Represents v s τ)
    (hu : ∀ w, ∀ s' τ', Represents w s' τ' → ∀ l ≤ S, TRestricted l (t - 1) s' τ' → u w = true)
    (hb' : ∀ w, ∀ s' τ', Represents w s' τ' → ∀ l ≤ S, TRestricted l t s' τ' → b w = true) :
    stepTest S t v u b = true := by
  have size := live_size h.live
  rw [← hrep.2.1, List.toFinset_card_of_nodup hrep.1, sigsOf_length] at size
  have h1 : Nat.blt (S + 1) t = false := Bool.eq_false_iff.mpr fun e => by rw [Nat.blt_eq] at e; omega
  have h2 : Nat.blt (S + 1 - t + 1) v.length = false := Bool.eq_false_iff.mpr fun e => by rw [Nat.blt_eq] at e; omega
  simp only [stepTest, h1, h2, Bool.or_self, Bool.false_eq_true, ite_false]
  cases h with
  | stop =>
    have p : (sigsOf v).Perm [target] :=
      List.perm_of_nodup_nodup_toFinset_eq hrep.1 (by simp) (by simp [hrep.2.1])
    have eq := List.perm_singleton.mp p
    cases v with
    | nil => simp [sigsOf] at eq
    | cons w rest =>
      simp only [sigsOf, List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at eq
      obtain ⟨hw, rfl⟩ := eq
      simp [hw, sigEq_iff]
  | @unary m t U a τ ha hf hr1 hr2 tail =>
    apply Bool.or_eq_true_iff.mpr; left
    apply Bool.or_eq_true_iff.mpr; right
    apply Bool.and_eq_true_iff.mpr
    exact ⟨by simp [Nat.blt_eq], unary_found ha hrep (by omega) hf hr1 hr2 tail (fun w hw => hu w _ _ hw m (by omega) tail)⟩
  | @binaryAnd m t U a b τ ha hb'p hab hf hra hrb tail =>
    apply Bool.or_eq_true_iff.mpr; right
    exact binary_found_and ha hb'p hab hrep (by omega) hf hra hrb tail (fun w hw => hb' w _ _ hw m (by omega) tail)
  | @binaryOr m t U a b τ ha hb'p hab hf hra hrb tail =>
    apply Bool.or_eq_true_iff.mpr; right
    exact binary_found_or ha hb'p hab hrep (by omega) hf hra hrb tail (fun w hw => hb' w _ _ hw m (by omega) tail)
lemma search_complete {m t : Nat} {S : Finset Sig} {τ : Sig → Tag} (h : TRestricted m t S τ)
    (k : Nat) (hk : m ≤ k) (v : List Wire) (hrep : Represents v S τ) : search k t v = true := by
  induction k generalizing m t S τ v with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    cases h
    have p : (sigsOf v).Perm [target] :=
      List.perm_of_nodup_nodup_toFinset_eq hrep.1 (by simp) (by simp [hrep.2.1])
    have eq := List.perm_singleton.mp p
    cases v with
    | nil => simp [sigsOf] at eq
    | cons w rest =>
      simp only [sigsOf, List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at eq
      obtain ⟨hw, rfl⟩ := eq
      simp [search, hw, sigEq_iff]
  | succ k ih =>
    rw [search]
    apply reduced_step h hk hrep <;>
      exact fun w s' τ' hw l hl hh => ih hh hl w hw
def Impossible (k t : Nat) (v : List Wire) : Prop :=
  ∀ m ≤ k, ∀ S τ, Represents v S τ → ¬ TRestricted m t S τ
lemma exclude_search {k t : Nat} {v : List Wire} (hc : search k t v = false) :
    Impossible k t v := by
  intro m hm S τ hrep h
  exact Bool.false_ne_true (hc.symm.trans (search_complete h k hm v hrep))
lemma exclude_step {k t : Nat} {v : List Wire} {u b : List Wire → Bool}
    (hu : ∀ w, u w = false → Impossible k (t - 1) w)
    (hb : ∀ w, b w = false → Impossible k t w)
    (hc : stepTest k t v u b = false) : Impossible (k + 1) t v := by
  intro m hm S τ hrep h
  have hu' : ∀ w s' τ', Represents w s' τ' → ∀ j ≤ k, TRestricted j (t - 1) s' τ' → u w = true := by
    intro w s' τ' hw j hj r
    cases e : u w
    · exact (hu _ e j hj s' τ' hw r).elim
    · rfl
  have hb' : ∀ w s' τ', Represents w s' τ' → ∀ j ≤ k, TRestricted j t s' τ' → b w = true := by
    intro w s' τ' hw j hj r
    cases e : b w
    · exact (hb _ e j hj s' τ' hw r).elim
    · rfl
  exact Bool.false_ne_true (hc.symm.trans (reduced_step h hm hrep hu' hb'))

def plainTag (_ : Sig) : Tag := .tNone

lemma plainRun {k t S} (h : Live k t S) : TRestricted k t S plainTag := by
  have un (a : Sig) : updUnaryTag plainTag a = plainTag := by
    funext x; simp [updUnaryTag,plainTag]
  have an (a b : Sig) : updAndTag plainTag a b = plainTag := by
    funext x; simp [updAndTag,plainTag]
  have dis (a b : Sig) : updOrTag plainTag a b = plainTag := by
    funext x; simp [updOrTag,plainTag]
  induction h with
  | stop => exact TRestricted.stop
  | unary ha fresh rest ih =>
    exact TRestricted.unary ha fresh (by simp [plainTag]) (by simp [plainTag]) (by rwa [un])
  | @binary k t U a b d ha hb ab fresh tail ih =>
    cases d
    · exact TRestricted.binaryAnd ha hb ab fresh (by simp [plainTag]) (by simp [plainTag]) (by rwa [an])
    · exact TRestricted.binaryOr ha hb ab fresh (by simp [plainTag]) (by simp [plainTag]) (by rwa [dis])

def wiresW : List Wire := signals.map fun a => (a, Tag.tNone)
lemma inputRep : Represents wiresW signals.toFinset plainTag := by
  refine ⟨?_,?_,?_⟩
  · change signals.Nodup; decide +kernel
  · rfl
  · intro w hw; obtain ⟨a,_,rfl⟩ := List.mem_map.mp hw; rfl

theorem conclude (cert : ∀ t ≤ 4, Impossible 13 t wiresW)
    (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C) (sz : C.size ≤ 13)
    (f : ∀ x : Fin 9 → Bool, C.eval (encoded x) = edgeF x) : False := by
  obtain ⟨k,t,hk,run,bound⟩ := extractedBank C h f
  exact cert t (by omega) k (hk.trans sz) signals.toFinset plainTag inputRep (plainRun run)

end Core

namespace Core
namespace SignedReadOnceKW
abbrev Row := Fin 544

/-- Each wire may label one rectangle in the positive by negative Karchmer–Wigderson matrix. -/
def Tiling (S : Finset Sig) : Prop := ∃ f : Row → Row → Sig,
  (∀ p n, f p n ∈ S ∧ bit true p (f p n) ≠ bit false n (f p n)) ∧
  ∀ p n p' n', f p n = f p' n' → f p n' = f p n

private def refineLabel (f : Row → Row → Sig) (g : Sig) (pick : Row → Row → Sig) (p n : Row) : Sig :=
  if f p n = g then pick p n else f p n

private theorem refine_rect {f pick : Row → Row → Sig} {g a b : Sig}
    (rect : ∀ p n p' n', f p n = f p' n' → f p n' = f p n)
    (unusedA : ∀ p n, f p n ≠ a) (unusedB : ∀ p n, f p n ≠ b)
    (inPair : ∀ p n, pick p n = a ∨ pick p n = b)
    (safe : ∀ p n p' n', f p n = g → f p' n' = g → f p n' = g → pick p n = pick p' n' → pick p n' = pick p n)
    (p n p' n' : Row) (same : refineLabel f g pick p n = refineLabel f g pick p' n') :
    refineLabel f g pick p n' = refineLabel f g pick p n := by
  let back := fun z : Sig => if z=a ∨ z=b then g else z
  have undo (i j : Row) : back (refineLabel f g pick i j) = f i j := by
    by_cases h : f i j = g
    · simpa [refineLabel,h,back] using (show (if pick i j=a ∨ pick i j=b then g else pick i j) = g by rw [ite_eq_left (inPair i j)])
    · simp [refineLabel,h,back,unusedA,unusedB]
  have old := (undo p n).symm.trans ((congrArg back same).trans (undo p' n'))
  have cross := rect p n p' n' old
  by_cases h : f p n = g
  · have lastOld : f p' n' = g := old.symm.trans h
    have mixed := cross.trans h
    simp only [refineLabel,ite_eq_left h,ite_eq_left lastOld,ite_eq_left mixed] at same ⊢
    exact safe _ _ _ _ h lastOld mixed same
  · simp [refineLabel,cross,h]

private def pickGate (d : Bool) (a b : Sig) (p n : Row) : Sig :=
  if bit true p (bin d a b) then
    if d then (if bit true p a then a else b) else (if bit false n a then b else a)
  else
    if d then (if bit false n a then a else b) else (if bit true p a then b else a)

private theorem pick_bits {a b : Sig} {d : Bool} {p n : Row}
    (diff : bit true p (bin d a b) ≠ bit false n (bin d a b)) :
    bit true p (pickGate d a b p n) ≠ bit false n (pickGate d a b p n) := by
  rw [bit_bin,bit_bin] at diff
  cases d <;> cases ap : bit true p a <;> cases bp : bit true p b <;>
    cases an : bit false n a <;> cases bn : bit false n b <;> simp_all [pickGate,bit_bin]

private theorem same_opposite {a b c : Bool} (ac : a ≠ c) (bc : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

private theorem split_gate {a b : Sig} {d : Bool} {U : Finset Sig} (an : a ∉ U) (bn : b ∉ U)
    (fresh : bin d a b ∉ insert a (insert b U)) (sol : Tiling (insert (bin d a b) U)) :
    Tiling (insert a (insert b U)) := by
  obtain ⟨f,leg,rect⟩ := sol
  let g := bin d a b
  let pick := pickGate d a b
  have ga : g ≠ a := fun e => fresh (Finset.mem_insert.mpr (Or.inl e))
  have gb : g ≠ b := fun e => fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl e)))
  have oldA (p n) : f p n ≠ a := by
    rcases Finset.mem_insert.mp (leg p n).1 with eq|mem
    · exact eq ▸ ga
    · exact fun eq => an (eq ▸ mem)
  have oldB (p n) : f p n ≠ b := by
    rcases Finset.mem_insert.mp (leg p n).1 with eq|mem
    · exact eq ▸ gb
    · exact fun eq => bn (eq ▸ mem)
  have hit (p n) : pick p n = a ∨ pick p n = b := by
    unfold pick pickGate
    split <;> split <;> split <;> simp
  refine ⟨refineLabel f g pick,?_,refine_rect rect oldA oldB hit ?_⟩
  · intro p n
    by_cases h : f p n = g
    · rw [refineLabel,ite_eq_left h]
      have sep := (leg p n).2
      rw [h] at sep
      exact ⟨by rcases hit p n with eq|eq <;> simp [eq],pick_bits sep⟩
    · rw [refineLabel,ite_eq_right h]
      exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ((Finset.mem_insert.mp (leg p n).1).resolve_left h)),(leg p n).2⟩
  · intro p n p' n' _ last cross eq
    have d1 := (leg p' n').2
    have d2 := (leg p n').2
    rw [last] at d1
    rw [cross] at d2
    have same := same_opposite d2 d1
    change bit true p (bin d a b) = bit true p' (bin d a b) at same
    cases d with
    | false =>
      cases h : bit true p (bin false a b) with
      | false => simp [pick,pickGate,h]
      | true => simpa [pick,pickGate,← same,h] using eq.symm
    | true =>
      cases h : bit true p (bin true a b) with
      | false => simpa [pick,pickGate,← same,h] using eq.symm
      | true => simp [pick,pickGate,h]

private theorem negate_gate {a : Sig} {U : Finset Sig} (ap : proper a) (an : a ∉ U)
    (fresh : neg a ∉ insert a U) (sol : Tiling (insert (neg a) U)) : Tiling (insert a U) := by
  obtain ⟨f,leg,rect⟩ := sol
  have ga : neg a ≠ a := fun e => fresh (Finset.mem_insert.mpr (Or.inl e))
  have oldA (p n) : f p n ≠ a := by
    rcases Finset.mem_insert.mp (leg p n).1 with eq|mem
    · exact eq ▸ ga
    · exact fun eq => an (eq ▸ mem)
  refine ⟨refineLabel f (neg a) (fun _ _ => a),?_,refine_rect (a:=a) (b:=a) rect oldA oldA (fun _ _ => Or.inl rfl) (fun _ _ _ _ _ _ _ _ => rfl)⟩
  intro p n
  by_cases h : f p n = neg a
  · rw [refineLabel,ite_eq_left h]
    have sep := (leg p n).2
    rw [h,bit_neg _ _ ap.1,bit_neg _ _ ap.1] at sep
    exact ⟨Finset.mem_insert_self _ _,fun e => sep (congrArg Bool.not e)⟩
  · rw [refineLabel,ite_eq_right h]
    exact ⟨Finset.mem_insert_of_mem ((Finset.mem_insert.mp (leg p n).1).resolve_left h),(leg p n).2⟩

/-- At the tight fan-in bound there is no fan-out, including at unary NOT gates. Splitting one
rectangle per gate yields one rectangle per distinct input, allowing either polarity. -/
theorem signed_tiling_of_live {k t : Nat} {S : Finset Sig} (run : Live k t S) (sat : S.card + t = k+1) : Tiling S := by
  induction run with
  | stop => exact ⟨fun _ _ => target,fun p n => ⟨Finset.mem_singleton_self _,by simp [bit,target,testBit_top,p.isLt]⟩,fun _ _ _ _ _ => rfl⟩
  | @unary k t U a va gf tail ih =>
    have gn : neg a ∉ U := fun h => gf (Finset.mem_insert_of_mem h)
    have cap := (live_size tail).2
    rw [Finset.card_insert_of_notMem gn] at cap
    have pre := Finset.card_insert_le a U
    have an : a ∉ U := by intro ha; rw [Finset.insert_eq_of_mem ha] at sat; omega
    apply negate_gate va an gf (ih ?_)
    rw [Finset.card_insert_of_notMem gn]; omega
  | @binary k t U a b d _ _ ab gf tail ih =>
    have gn : bin d a b ∉ U := fun h => gf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have cap := (live_size tail).2
    rw [Finset.card_insert_of_notMem gn] at cap
    have first := Finset.card_insert_le a (insert b U)
    have second := Finset.card_insert_le b U
    have bn : b ∉ U := by intro hb; rw [Finset.insert_eq_of_mem hb] at sat; have := Finset.card_insert_le a U; omega
    have an : a ∉ U := by intro ha; rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ha)] at sat; omega
    apply split_gate an bn gf (ih ?_)
    rw [Finset.card_insert_of_notMem gn]; omega

def privateCell (ws : List Sig) (p n : Row) (a : Sig) : Bool :=
  ws.all (fun x => decide (bit true p x = bit false n x ∨ x = a))

theorem no_four_nots : ¬ Live 13 4 signals.toFinset := by
  intro live
  obtain ⟨f,leg,rect⟩ := signed_tiling_of_live live (by decide +kernel)
  have forced {p n a} (h : privateCell signals p n a = true) : f p n = a :=
    (of_decide_eq_true ((List.all_eq_true.mp h) _ (List.mem_toFinset.mp (leg p n).1))).resolve_left (leg p n).2
  have A := (rect 404 16 34 32 ((forced (p:=404) (n:=16) (a:=raw2) (by decide +kernel)).trans
    (forced (p:=34) (n:=32) (a:=raw2) (by decide +kernel)).symm)).trans (forced (p:=404) (n:=16) (a:=raw2) (by decide +kernel))
  have B := (rect 404 8 31 32 ((forced (p:=404) (n:=8) (a:=raw3) (by decide +kernel)).trans
    (forced (p:=31) (n:=32) (a:=raw3) (by decide +kernel)).symm)).trans (forced (p:=404) (n:=8) (a:=raw3) (by decide +kernel))
  exact (by decide : raw2 ≠ raw3) (A.symm.trans B)
end SignedReadOnceKW
end Core
namespace Core.KWCertificate
open SignedReadOnceKW
abbrev Row := Fin 544

def equalCell (w : List Sig) (p n : Row) := w.all (fun a => decide (bit true p a = bit false n a))

private theorem different_in_live {k t S} (run : Live k t S) (p n : Row) :
    ∃ a ∈ S, bit true p a ≠ bit false n a := by
  induction run with
  | stop => exact ⟨target,Finset.mem_singleton_self _,by simp [bit,target,testBit_top,p.isLt]⟩
  | @unary k t U a va _ tail ih =>
    obtain ⟨x,hx,xn⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl|inU
    · exact ⟨a,Finset.mem_insert_self _ _,by rw [bit_neg _ _ va.1,bit_neg _ _ va.1] at xn; exact fun e => xn (congrArg Bool.not e)⟩
    · exact ⟨x,Finset.mem_insert_of_mem inU,xn⟩
  | @binary k t U a b d _ _ _ _ tail ih =>
    obtain ⟨x,hx,xn⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl|inU
    · by_cases ea : bit true p a = bit false n a
      · refine ⟨b,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),fun eb => xn ?_⟩
        simp [bit_bin,ea,eb]
      · exact ⟨a,Finset.mem_insert_self _ _,ea⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem inU),xn⟩

private theorem same_blocks {k t : Nat} {w : List Sig} {p n : Row} (h : equalCell w p n = true) : ¬ Live k t w.toFinset := by
  intro run
  obtain ⟨x,hx,diff⟩ := different_in_live run p n
  exact diff (of_decide_eq_true ((List.all_eq_true.mp h) x (List.mem_toFinset.mp hx)))

def pick (w : List Sig) (p n : Row) : Sig := (w.find? (fun a => decide (bit true p a ≠ bit false n a))).getD zero

def signCheck (w : List Sig) (p n q m : Row) :=
  let a := pick w p n
  privateCell w p n a && privateCell w q m a && decide (bit true p a ≠ bit true q a)

def crossCheck (w : List Sig) (p n pa na pb nb : Row) :=
  let a := pick w p na
  let b := pick w p nb
  decide (a ≠ b) && privateCell w p na a && privateCell w pa n a && privateCell w p nb b && privateCell w pb n b

private theorem forced {w : List Sig} {f : Row → Row → Sig}
    (leg : ∀ p n, f p n ∈ w.toFinset ∧ bit true p (f p n) ≠ bit false n (f p n))
    {p n : Row} {a : Sig} (h : privateCell w p n a = true) : f p n = a :=
  (of_decide_eq_true ((List.all_eq_true.mp h) _ (List.mem_toFinset.mp (leg p n).1))).resolve_left (leg p n).2

private theorem sign_blocks {w : List Sig} {p n q m : Row} (h : signCheck w p n q m = true) : ¬ Tiling w.toFinset := by
  rintro ⟨f,leg,rect⟩
  simp only [signCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  have e := (rect p n q m ((forced leg h.1.1).trans (forced leg h.1.2).symm)).trans (forced leg h.1.1)
  have d1 := (leg p m).2
  have d2 := (leg q m).2
  rw [e] at d1
  rw [forced leg h.1.2] at d2
  exact h.2 (by cases ha : bit true p (pick w p n) <;> cases hb : bit true q (pick w p n) <;> cases hc : bit false m (pick w p n) <;> simp_all)

private theorem cross_blocks {w : List Sig} {p n pa na pb nb : Row} (h : crossCheck w p n pa na pb nb = true) : ¬ Tiling w.toFinset := by
  rintro ⟨f,leg,rect⟩
  simp only [crossCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  have A := (rect p na pa n ((forced leg h.1.1.1.2).trans (forced leg h.1.1.2).symm)).trans (forced leg h.1.1.1.2)
  have B := (rect p nb pb n ((forced leg h.1.2).trans (forced leg h.2).symm)).trans (forced leg h.1.2)
  exact h.1.1.1.1 (A.symm.trans B)

/-- A certificate encodes up to six nine-bit row coordinates after a two-bit tag. The inputs can
be traversed in any order, since the unique distinguishing wires are recovered by the checker. -/
def row (code offset : Nat) : Row := Fin.ofNat 544 ((code >>> (2+9*offset)) &&& 511)

def certified (k t : Nat) (v : List Wire) (code : Nat) :=
  let w := sigsOf v
  let p := row code 0
  let n := row code 1
  match code &&& 3 with
  | 1 => equalCell w p n
  | 2 => decide (v.length+t=k+1) && signCheck w p n (row code 2) (row code 3)
  | 3 => decide (v.length+t=k+1) && crossCheck w p n (row code 2) (row code 3) (row code 4) (row code 5)
  | _ => false

theorem certified_sound {k t code : Nat} {v : List Wire} (yes : certified k t v code = true) : Impossible k t v := by
  intro m hm S τ rep h
  obtain ⟨nd,hs,_⟩ := rep
  subst S
  have run := h.live
  have card : (sigsOf v).toFinset.card = v.length := by rw [List.toFinset_card_of_nodup nd,sigsOf_length]
  have cap := (live_size run).2
  unfold certified at yes
  split at yes
  · exact same_blocks yes run
  · simp only [Bool.and_eq_true,decide_eq_true_eq] at yes
    exact sign_blocks yes.2 (signed_tiling_of_live run (by omega))
  · simp only [Bool.and_eq_true,decide_eq_true_eq] at yes
    exact cross_blocks yes.2 (signed_tiling_of_live run (by omega))
  · contradiction

def guided (hint : Nat → Nat → List Wire → Nat) : Nat → Nat → List Wire → Bool
  | 0,t,v => search 0 t v
  | k+1,t,v => if certified (k+1) t v (hint (k+1) t v) then false else
      stepTest k t v (guided hint k (t-1)) (guided hint k t)

theorem guided_sound (hint : Nat → Nat → List Wire → Nat) (k t : Nat) (v : List Wire)
    (no : guided hint k t v = false) : Impossible k t v := by
  induction k generalizing t v with
  | zero => exact exclude_search no
  | succ k ih =>
    unfold guided at no
    split at no
    · rename_i yes; exact certified_sound yes
    · exact exclude_step (fun w h => ih _ _ h) (fun w h => ih _ _ h) no
end Core.KWCertificate
namespace Core.KWMemo
open KWCertificate

theorem perm_impossible {k t : Nat} {v w : List Wire} (perm : v.Perm w) (ok : Impossible k t w) : Impossible k t v := by
  intro m hm S τ rep run
  apply ok m hm S τ _ run
  have hp : (sigsOf v).Perm (sigsOf w) := perm.map Prod.fst
  exact ⟨hp.nodup_iff.mp rep.1,by rw [← rep.2.1]; ext x; simp [hp.mem_iff],
    fun x hx => rep.2.2 x (perm.mem_iff.mpr hx)⟩

def eraseWire (a : Wire) : List Wire → Option (List Wire)
  | [] => none
  | b::w => if tagEq a.2 b.2 && sigEq a.1 b.1 then some w else (eraseWire a w).map (b :: ·)
private theorem eraseWire_perm {a : Wire} {w w' : List Wire} (n : eraseWire a w = some w') : w.Perm (a::w') := by
  induction w generalizing w' with
  | nil => simp [eraseWire] at n
  | cons b w ih =>
    unfold eraseWire at n
    split at n
    · rename_i e
      simp only [Bool.and_eq_true] at e
      have eq : a = b := Prod.ext (sigEq_iff.mp e.2) (tagEq_iff.mp e.1)
      cases n; subst b; exact List.Perm.refl _
    · cases e : eraseWire a w with
      | none => simp [e] at n
      | some z => simp [e] at n; subst w'; exact (List.Perm.cons b (ih e)).trans (List.Perm.swap a b z)

def permCheck : List Wire → List Wire → Bool
  | [],ws => ws.isEmpty
  | a::v,w => match eraseWire a w with | none => false | some w' => permCheck v w'
theorem permCheck_perm {v w : List Wire} (yes : permCheck v w = true) : v.Perm w := by
  induction v generalizing w with
  | nil => cases w <;> simp [permCheck] at *
  | cons a v ih =>
    unfold permCheck at yes
    cases e : eraseWire a w with
    | none => simp [e] at yes
    | some w' => simp only [e] at yes; exact (List.Perm.cons a (ih yes)).trans (eraseWire_perm e).symm

structure Node where
  k : Nat
  t : Nat
  w : List Wire

structure Table where
  count : Nat
  hint : Nat → Nat → List Wire → Nat
  node : Nat → Node

def childOK (tab : Table) (k t : Nat) (w : List Wire) : Bool :=
  let h := tab.hint k t w
  if h &&& 3 = 0 then
    let i := h / 4 - 1
    (0 < h && i < tab.count && (tab.node i).k = k && (tab.node i).t = t) && permCheck w (tab.node i).w
  else certified k t w h

def nodeOK (tab : Table) (i : Nat) : Bool :=
  let state := tab.node i
  match state.k with
  | 0 => !(search 0 state.t state.w)
  | k+1 => !stepTest k state.t state.w (fun w => !childOK tab k (state.t-1) w) (fun w => !childOK tab k state.t w)

private theorem child_sound (tab : Table) (k t : Nat) (w : List Wire)
    (prev : ∀ i < tab.count, (tab.node i).k = k → Impossible k (tab.node i).t (tab.node i).w)
    (ok : childOK tab k t w = true) : Impossible k t w := by
  by_cases select : (tab.hint k t w) &&& 3 = 0
  · simp only [childOK,ite_eq_left select,Bool.and_eq_true,decide_eq_true_eq] at ok
    have res := prev _ ok.1.1.1.2 ok.1.1.2
    rw [ok.1.2] at res
    exact perm_impossible (permCheck_perm ok.2) res
  · exact certified_sound (by simpa [childOK,select] using ok)

theorem checked_nodes (tab : Table) (valid : ∀ i < tab.count, nodeOK tab i = true) (i : Nat) (hi : i < tab.count) :
    Impossible (tab.node i).k (tab.node i).t (tab.node i).w := by
  generalize level : (tab.node i).k = k
  induction k generalizing i with
  | zero =>
    have h := valid i hi
    simp only [nodeOK,level,Bool.not_eq_true'] at h
    exact exclude_search h
  | succ k ih =>
    have h := valid i hi
    simp only [nodeOK,level,Bool.not_eq_true'] at h
    apply exclude_step _ _ h <;> intro w no <;> exact child_sound tab k _ w (fun i hi eq => ih i hi eq) (by simpa using no)

def span (p : Nat → Bool) : Nat → Nat → Bool
  | 0,_ => true
  | n+1,i => p i && span p n (i+1)

theorem span_ok {p : Nat → Bool} {len i : Nat} (h : span p len i = true) (j : Nat) (lo : i ≤ j) (hi : j < i+len) : p j = true := by
  induction len generalizing i with
  | zero => omega
  | succ k ih =>
    simp only [span,Bool.and_eq_true] at h
    obtain ⟨a,b⟩ := h
    by_cases e : i=j
    · exact e ▸ a
    · exact ih b (by omega) (by omega)
end Core.KWMemo

namespace Core.BulkKW
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
theorem no_tiling {w : List Sig} {base n i : Nat} (hi : i < n) (bound : base+4*n ≤ 544)
    (ok : (scan (masks base n) w).2.2.testBit i = false) : ¬ Tiling w.toFinset := by
  rintro ⟨label,leg,rect⟩
  let r₁ : Fin 544 := ⟨base+i,by omega⟩
  let r₂ : Fin 544 := ⟨base+n+i,by omega⟩
  let r₃ : Fin 544 := ⟨base+2*n+i,by omega⟩
  let r₄ : Fin 544 := ⟨base+3*n+i,by omega⟩
  have belongs (p n : Fin 544) : label p n ∈ w := List.mem_toFinset.mp (leg p n).1
  have sep (p n : Fin 544) := xor_true (leg p n).2
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

theorem excludes_sound {base n k t : Nat} {v : List Wire} (bound : base+4*n ≤ 544)
    (sat : v.length+t=k+1) (yes : excludes base n (sigsOf v) = true) : Impossible k t v := by
  intro m hm S τ rep run
  obtain ⟨nd,hs,_⟩ := rep
  subst S
  have card : (sigsOf v).toFinset.card = v.length := by rw [List.toFinset_card_of_nodup nd,sigsOf_length]
  have cap := (live_size run.live).2
  obtain ⟨i,hi,ok⟩ := missing_bit (of_decide_eq_true yes)
  exact no_tiling hi bound ok (signed_tiling_of_live run.live (by omega))

end Core.BulkKW

namespace Core.SingleShare

inductive Tree (α : Type)
  | leaf (a : α)
  | gate (isOr : Bool) (left right : Tree α)
  deriving Inhabited

namespace Tree

def value (read : α → Sig) : Tree α → Sig
  | .leaf a => read a
  | .gate d l r => bin d (l.value read) (r.value read)

def occurrences [DecidableEq α] (x : α) : Tree α → Nat
  | .leaf a => if x=a then 1 else 0
  | .gate _ l r => l.occurrences x + r.occurrences x

def expand [DecidableEq α] (d : Bool) (g a b : α) : Tree α → Tree α
  | .leaf x => if x=g then .gate d (.leaf a) (.leaf b) else .leaf x
  | .gate op x y => .gate op (expand d g a b x) (expand d g a b y)

theorem expand_value [DecidableEq α] (d : Bool) (g a b : α) (read : α → Sig)
    (eq : read g = bin d (read a) (read b)) (q : Tree α) :
    (q.expand d g a b).value read = q.value read := by
  induction q with
  | leaf x => by_cases h : x=g <;> simp [expand,value,h,eq]
  | gate op l r ihl ihr => simp [expand,value,ihl,ihr]

theorem expand_count [DecidableEq α] (d : Bool) (g a b x : α) (q : Tree α) :
    (q.expand d g a b).occurrences x =
    (if x=g then 0 else q.occurrences x) +
    (if x=a then q.occurrences g else 0) + (if x=b then q.occurrences g else 0) := by
  induction q with
  | leaf y =>
    by_cases yy : y=g
    · subst y
      simp [expand,occurrences]
    · simp [expand,occurrences,yy,Ne.symm yy]
      exact fun h xy => yy (xy.symm.trans h)
  | gate op l r ihl ihr =>
    simp only [expand,occurrences,ihl,ihr]
    split_ifs <;> omega

def hide [DecidableEq α] (shared : α) : Tree α → Tree (Option α)
  | .leaf x => .leaf (if x=shared then none else some x)
  | .gate op x y => .gate op (hide shared x) (hide shared y)

theorem hide_none [DecidableEq α] (shared : α) (e : Tree α) :
    (e.hide shared).occurrences none = e.occurrences shared := by
  induction e with
  | leaf x => by_cases h : x=shared <;> simp [hide,occurrences,h,Ne.symm]
  | gate op l r ihl ihr => simp [hide,occurrences,ihl,ihr]

theorem hide_some [DecidableEq α] (shared x : α) (e : Tree α) :
    (e.hide shared).occurrences (some x) = if x=shared then 0 else e.occurrences x := by
  induction e with
  | leaf y =>
    by_cases hy : y=shared
    · subst y
      by_cases hx : x=shared <;> simp [hide,occurrences,hx]
    · by_cases hx : x=shared
      · subst x
        simp [hide,occurrences,hy,Ne.symm hy]
      · simp [hide,occurrences,hy,hx]
  | gate op l r ihl ihr =>
    simp only [hide,occurrences,ihl,ihr]
    split_ifs <;> omega

def plug (x : Sig) : Option Sig → Sig
  | none => x
  | some a => a

theorem hide_value (shared : Sig) (e : Tree Sig) :
    (e.hide shared).value (plug shared) = e.value id := by
  induction e with
  | leaf y => by_cases h : y=shared <;> simp [hide,value,plug,h]
  | gate op l r ihl ihr => simp [hide,value,ihl,ihr]

end Tree

/-- A formula uses each input in S exactly once and uses no other input. -/
def Once (S : Finset Sig) : Prop := ∃ e : Tree Sig, e.value id = target ∧
  ∀ x, e.occurrences x = if x∈S then 1 else 0

/-- A single shared subtree. Its inputs and the ordinary outer leaves jointly
partition S. Only the outer placeholder occurs twice. -/
def Shared (S : Finset Sig) : Prop := ∃ inner : Tree Sig, ∃ outer : Tree (Option Sig),
  outer.value (Tree.plug (inner.value id)) = target ∧ outer.occurrences none = 2 ∧
  ∀ x, inner.occurrences x + outer.occurrences (some x) = if x∈S then 1 else 0

private theorem inline_count {U : Finset Sig} {g a b : Sig} (ab : a ≠ b)
    (gn : g ∉ insert a (insert b U)) (an : a ∉ U) (bn : b ∉ U) (x : Sig) :
    (if x=g then 0 else if x∈insert g U then 1 else 0) +
    (if x=a then 1 else 0) + (if x=b then 1 else 0) =
    (if x∈insert a (insert b U) then 1 else 0) := by
  have gu : g∉U := fun h => gn (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  have ga : g≠a := fun h => gn (Finset.mem_insert.mpr (Or.inl h))
  have gb : g≠b := fun h => gn (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl h)))
  by_cases hg : x=g <;> by_cases ha : x=a <;> by_cases hb : x=b <;> simp_all

private theorem inline_once {U : Finset Sig} {a b : Sig} (d : Bool) (ab : a≠b)
    (fresh : bin d a b ∉ insert a (insert b U)) (an : a∉U) (bn : b∉U)
    (h : Once (insert (bin d a b) U)) : Once (insert a (insert b U)) := by
  obtain ⟨e,ev,cnt⟩ := h
  let g := bin d a b
  refine ⟨e.expand d g a b,(Tree.expand_value d g a b id rfl e).trans ev,?_⟩
  intro x
  rw [Tree.expand_count,cnt,cnt]
  simpa [g] using inline_count ab fresh an bn x

private theorem inline_shared {U : Finset Sig} {a b : Sig} (d : Bool) (ab : a≠b)
    (fresh : bin d a b ∉ insert a (insert b U)) (an : a∉U) (bn : b∉U)
    (h : Shared (insert (bin d a b) U)) : Shared (insert a (insert b U)) := by
  obtain ⟨i,o,ev,twice,cnt⟩ := h
  let g := bin d a b
  let i' := i.expand d g a b
  let o' := o.expand d (some g) (some a) (some b)
  have ie : i'.value id = i.value id := Tree.expand_value d g a b id rfl i
  refine ⟨i',o',?_,?_,?_⟩
  · rw [ie]
    exact (Tree.expand_value d (some g) (some a) (some b) (Tree.plug (i.value id)) rfl o).trans ev
  · simpa [o',Tree.expand_count] using twice
  · intro x
    have total := cnt x
    have unit : i.occurrences g + o.occurrences (some g) = 1 := by simpa [g] using cnt g
    have step := inline_count ab fresh an bn x
    change (i.expand d g a b).occurrences x + (o.expand d (some g) (some a) (some b)).occurrences (some x) = _
    simp only [Tree.expand_count,Option.some.injEq]
    change i.occurrences x + o.occurrences (some x) = (if x∈insert g U then 1 else 0) at total
    change (if x=g then 0 else if x∈insert g U then 1 else 0) + _ + _ = _ at step
    split_ifs at * <;> omega

private theorem stop_once : Once {target} := by
  refine ⟨.leaf target,rfl,?_⟩
  intro x
  simp [Tree.occurrences]

/-- A saturated monotone liveness trace represents a read-once formula. -/
theorem once_of_live {k t : Nat} {S : Finset Sig} (run : Live k t S) (mono : t=0) (sat : S.card=k+1) :
    Once S := by
  induction run with
  | stop => exact stop_once
  | unary => omega
  | @binary k t U a b d _ _ ab fresh tail ih =>
    have gn : bin d a b∉U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have cap := (live_size tail).2
    rw [Finset.card_insert_of_notMem gn] at cap
    have ca := Finset.card_insert_le a (insert b U)
    have cb := Finset.card_insert_le b U
    have bn : b∉U := by intro mem; rw [Finset.insert_eq_of_mem mem] at sat; have := Finset.card_insert_le a U; omega
    have an : a∉U := by intro mem; rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem mem)] at sat; omega
    apply inline_once d ab fresh an bn (ih mono ?_)
    rw [Finset.card_insert_of_notMem gn]
    omega

private theorem sharing_step {U : Finset Sig} {a b r : Sig} (d : Bool) (ab : a≠b)
    (fresh : bin d a b ∉ insert a (insert b U)) (which : r=a ∨ r=b) (ur : r∈U)
    (unique : ∀ x ∈ U, x=a ∨ x=b → x=r)
    (tail : Once (insert (bin d a b) U)) : Shared (insert a (insert b U)) := by
  obtain ⟨q,vq,cq⟩ := tail
  let g := bin d a b
  let e := q.expand d g a b
  have vg : e.value id = target := (Tree.expand_value d g a b id rfl q).trans vq
  have gu : g∉U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  have ga : g≠a := fun h => fresh (Finset.mem_insert.mpr (Or.inl h))
  have gb : g≠b := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl h)))
  have count (x : Sig) : e.occurrences x = (if x∈insert a (insert b U) then 1 else 0) +
      (if x=r then 1 else 0) := by
    change (q.expand d g a b).occurrences x = _
    have unit : q.occurrences g=1 := by simpa [g] using cq g
    rw [Tree.expand_count,unit,cq]
    change (if x=g then 0 else if x∈insert g U then 1 else 0) + _ + _ = _
    clear unit cq vq vg
    rcases which with ra | rb
    · subst r
      have bn : b∉U := fun h => ab ((unique b h (Or.inr rfl)).symm)
      clear unique
      by_cases hx : x=g <;> by_cases ha : x=a <;> by_cases hb : x=b <;> simp_all
    · subst r
      have an : a∉U := fun h => ab (unique a h (Or.inl rfl))
      clear unique
      by_cases hx : x=g <;> by_cases ha : x=a <;> by_cases hb : x=b <;> simp_all
  refine ⟨.leaf r,e.hide r,(Tree.hide_value r e).trans vg,?_,?_⟩
  · rw [Tree.hide_none,count]
    simp [Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ur)]
  · intro x
    rw [Tree.hide_some,count]
    by_cases hx : x=r
    · subst x
      simp [Tree.occurrences,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ur)]
    · simp [Tree.occurrences,hx]

/-- Any monotone run within one gate of the read-once budget unfolds to a
read-once formula or to a read-once inner formula occurring exactly twice.
Every original active signal occurs exactly once across the inner formula
and the ordinary leaves of the outer formula. -/
theorem once_or_one_shared {k t : Nat} {S : Finset Sig} (run : Live k t S) (mono : t=0)
    (budget : k≤S.card) : Once S ∨ Shared S := by
  induction run with
  | stop => exact Or.inl stop_once
  | unary => omega
  | @binary k t U a b d _ _ ab fresh tail ih =>
    have gn : bin d a b ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have cap := (live_size tail).2
    rw [Finset.card_insert_of_notMem gn] at cap
    by_cases ha : a∈U
    · by_cases hb : b∈U
      · rw [Finset.insert_eq_of_mem hb,Finset.insert_eq_of_mem ha] at budget
        omega
      · rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ha),Finset.card_insert_of_notMem hb] at budget
        have inner := once_of_live tail mono (by rw [Finset.card_insert_of_notMem gn]; omega)
        exact Or.inr (sharing_step d ab fresh (Or.inl rfl) ha (by
          intro x hx h
          rcases h with h|h
          · exact h
          · exact (hb (h ▸ hx)).elim) inner)
    · by_cases hb : b∈U
      · rw [Finset.insert_eq_of_mem hb,Finset.card_insert_of_notMem ha] at budget
        have inner := once_of_live tail mono (by rw [Finset.card_insert_of_notMem gn]; omega)
        exact Or.inr (sharing_step d ab fresh (Or.inr rfl) hb (by
          intro x hx h
          rcases h with h|h
          · exact (ha (h ▸ hx)).elim
          · exact h) inner)
      · have an : a∉insert b U := by simp [ab,ha]
        rw [Finset.card_insert_of_notMem an,Finset.card_insert_of_notMem hb] at budget
        rcases ih mono (by rw [Finset.card_insert_of_notMem gn]; omega) with plain|marked
        · exact Or.inl (inline_once d ab fresh ha hb plain)
        · exact Or.inr (inline_shared d ab fresh ha hb marked)

end Core.SingleShare

namespace Core.SingleShare
namespace OuterSmall

def a : Tree (Fin 3) := .leaf 0
def b : Tree (Fin 3) := .leaf 1
def c : Tree (Fin 3) := .leaf 2

/-- The seventeen nonconstant read-once functions of up to three positive literals,
with a concrete formula for each. -/
def formulas : List (Tree (Fin 3)) := [a,b,c,
  .gate false a b,.gate false a c,.gate false b c,.gate true a b,.gate true a c,.gate true b c,
  .gate false a (.gate false b c),.gate true a (.gate true b c),
  .gate false a (.gate true b c),.gate false b (.gate true a c),.gate false c (.gate true a b),
  .gate true a (.gate false b c),.gate true b (.gate false a c),.gate true c (.gate false a b)]

def representative (i : Fin 17) := formulas.getD i.val a

def boolValue (r : α → Bool) : Tree α → Bool
  | .leaf x => r x
  | .gate d l t => if d then boolValue r l || boolValue r t else boolValue r l && boolValue r t

def assignment (x y z : Bool) (j : Fin 3) : Bool := if j=0 then x else if j=1 then y else z

theorem candidate_once : ∀ (i : Fin 17) (q : Fin 3), (representative i).occurrences q ≤ 1 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem merge_table : ∀ (i j : Fin 17) (op : Bool),
    (representative i).occurrences 0 + (representative j).occurrences 0 ≤ 2 →
    (representative i).occurrences 1 + (representative j).occurrences 1 ≤ 1 →
    (representative i).occurrences 2 + (representative j).occurrences 2 ≤ 1 →
    ∃ k : Fin 17,
      (∀ q : Fin 3, (representative k).occurrences q ≤ (representative i).occurrences q + (representative j).occurrences q) ∧
      ∀ x y z : Bool, boolValue (assignment x y z) (representative k) =
        boolValue (assignment x y z) (.gate op (representative i) (representative j)) := by decide +kernel

/-- Any monotone tree with one literal used at most twice and each of two other
literals used at most once has a read-once equivalent on the same or fewer leaves. -/
theorem shrink (e : Tree (Fin 3)) (h₀ : e.occurrences 0 ≤ 2) (h₁ : e.occurrences 1 ≤ 1)
    (h₂ : e.occurrences 2 ≤ 1) : ∃ k : Fin 17,
    (∀ q, (representative k).occurrences q ≤ e.occurrences q) ∧
    ∀ x y z, boolValue (assignment x y z) (representative k) = boolValue (assignment x y z) e := by
  induction e with
  | leaf v =>
    rcases (show v=0 ∨ v=1 ∨ v=2 by omega) with rfl|rfl|rfl
    · exact ⟨0,fun _ => Nat.le_refl _,fun _ _ _ => rfl⟩
    · exact ⟨1,fun _ => Nat.le_refl _,fun _ _ _ => rfl⟩
    · exact ⟨2,fun _ => Nat.le_refl _,fun _ _ _ => rfl⟩
  | gate op l r ihl ihr =>
    simp only [Tree.occurrences] at h₀ h₁ h₂ ⊢
    obtain ⟨i,ic,ie⟩ := ihl (by omega) (by omega) (by omega)
    obtain ⟨j,jc,je⟩ := ihr (by omega) (by omega) (by omega)
    obtain ⟨k,kc,ke⟩ := merge_table i j op ((Nat.add_le_add (ic 0) (jc 0)).trans h₀)
      ((Nat.add_le_add (ic 1) (jc 1)).trans h₁) ((Nat.add_le_add (ic 2) (jc 2)).trans h₂)
    refine ⟨k,fun q => (kc q).trans (Nat.add_le_add (ic q) (jc q)),?_⟩
    intro x y z
    rw [ke]
    simp only [boolValue,ie,je]

private theorem atBit (side : Bool) (i : Nat) (read : α → Sig) (e : Tree α) :
    (if side then (e.value read).1 else (e.value read).2).testBit i =
    boolValue (fun x => (if side then (read x).1 else (read x).2).testBit i) e := by
  induction e with
  | leaf => rfl
  | gate d x y ix iy =>
    cases side <;> cases d <;> simp_all [boolValue,Tree.value,bin,Nat.testBit_or,Nat.testBit_and]

private theorem as_assignment (r : Fin 3 → Bool) : assignment (r 0) (r 1) (r 2) = r := by
  funext j
  rcases (show j=0 ∨ j=1 ∨ j=2 by omega) with rfl|rfl|rfl <;> rfl

theorem same_as_signal {e f : Tree (Fin 3)}
    (same : ∀ x y z, boolValue (assignment x y z) e = boolValue (assignment x y z) f)
    (read : Fin 3 → Sig) : e.value read = f.value read := by
  have bit_eq (s : Bool) (i : Nat) :
      (if s then (e.value read).1 else (e.value read).2).testBit i =
      (if s then (f.value read).1 else (f.value read).2).testBit i := by
    rw [atBit,atBit]
    let r := fun x : Fin 3 => (if s then (read x).1 else (read x).2).testBit i
    have h := same (r 0) (r 1) (r 2)
    simpa only [as_assignment] using h
  exact Prod.ext (Nat.eq_of_testBit_eq (bit_eq true)) (Nat.eq_of_testBit_eq (bit_eq false))

end OuterSmall
end Core.SingleShare

namespace Core.SingleShare
open OuterSmall

private theorem value_at (r : α → Sig) (side : Bool) (p : Fin 544) (e : Tree α) :
    bit side p (e.value r) = boolValue (fun x => bit side p (r x)) e := by
  induction e with
  | leaf => rfl
  | gate d l h il ih =>
    rw [Tree.value,bit_bin,il,ih]
    rfl

private theorem bool_lift (d x y x' y' : Bool) (hx : x=true → x'=true) (hy : y=true → y'=true) :
    (if d then x || y else x && y)=true → (if d then x' || y' else x' && y')=true := by
  cases d <;> cases x <;> cases y <;> simp_all

private theorem mono_tree [DecidableEq α] {r s : α → Bool} (e : Tree α)
    (moves : ∀ x, 0<e.occurrences x → r x=true → s x=true) :
    boolValue r e=true → boolValue s e=true := by
  induction e with
  | leaf a => exact moves a (by simp [Tree.occurrences])
  | gate d l t il it =>
    exact bool_lift d _ _ _ _ (il (fun x hx => moves x (by simp only [Tree.occurrences]; omega)))
      (it (fun x hx => moves x (by simp only [Tree.occurrences]; omega)))

def group (S : Finset Sig) (inner : Tree Sig) : Finset Sig := S.filter (fun a => 0 < inner.occurrences a)

/-- A positive-to-negative comparison which every outer ordinary leaf respects
forces the shared signal to be true on the positive row and false on the negative row. -/
private theorem force_shared {S : Finset Sig} {i : Tree Sig} {o : Tree (Option Sig)}
    (ev : o.value (Tree.plug (i.value id))=target)
    (cnt : ∀ x, i.occurrences x + o.occurrences (some x) = if x∈S then 1 else 0)
    (p n : Fin 544)
    (outside : ∀ x∈S, x∉group S i → bit true p x=true → bit false n x=true) :
    bit true p (i.value id)=true ∧ bit false n (i.value id)=false := by
  let r := Tree.plug (i.value id)
  by_contra h
  have place : bit true p (i.value id)=true → bit false n (i.value id)=true := by
    cases a : bit true p (i.value id) <;> cases b : bit false n (i.value id) <;> simp_all
  have mov : ∀ x, 0<o.occurrences x → bit true p (r x)=true → bit false n (r x)=true := by
    intro x hx
    cases x with
    | none => exact place
    | some x =>
      have c := cnt x
      have sx : x∈S := by by_contra hn; simp [hn] at c; omega
      have cx : i.occurrences x=0 := by simp [sx] at c; omega
      apply outside x sx
      simp [group,cx]
  have endmap := mono_tree o mov
  rw [← value_at r true p,← value_at r false n] at endmap
  change bit true p (o.value (Tree.plug (i.value id)))=true → bit false n (o.value (Tree.plug (i.value id)))=true at endmap
  simp [ev,bit,target,testBit_top,p.isLt] at endmap

abbrev Respects (S : Finset Sig) (p n : Fin 544) := ∀ a∈S, bit true p a=true → bit false n a=true

/-- Rows forced by two independent outside comparisons must be separated by an
inside input. This is a necessary condition on any shared module. -/
theorem module_of_trees {S : Finset Sig} {i : Tree Sig} {o : Tree (Option Sig)}
    (ev : o.value (Tree.plug (i.value id))=target)
    (cnt : ∀ x, i.occurrences x + o.occurrences (some x) = if x∈S then 1 else 0) :
    ∀ (p n p' n' : Fin 544), Respects (S\group S i) p n' → Respects (S\group S i) p' n → ¬ Respects (group S i) p n := by
  intro p n p' n' hp hn inside
  have forced (r s : Fin 544) (out : Respects (S\group S i) r s) :=
    force_shared ev cnt r s (fun x hx hnx => out x (Finset.mem_sdiff.mpr ⟨hx,hnx⟩))
  have yes := (forced p n' hp).1
  have no := (forced p' n hn).2
  have chain := mono_tree i (r:=fun x => bit true p x) (s:=fun x => bit false n x) (fun x hx => by
    apply inside x
    have ct := cnt x
    have sx : x∈S := by by_contra h; simp [h] at ct; omega
    exact Finset.mem_filter.mpr ⟨sx,hx⟩)
  rw [value_at id true p] at yes
  rw [value_at id false n] at no
  have clash := chain yes
  change boolValue (fun x => bit false n x) i = false at no
  rw [no] at clash
  contradiction

theorem shared_module {S : Finset Sig} (h : Shared S) :
    ∃ A ⊆ S, ∀ (p n p' n' : Fin 544), Respects (S\A) p n' → Respects (S\A) p' n → ¬ Respects A p n := by
  obtain ⟨i,o,ev,_,cnt⟩ := h
  exact ⟨group S i,Finset.filter_subset _ _,module_of_trees ev cnt⟩

end Core.SingleShare

namespace Core.SingleShare

def graft (i : Tree Sig) : Tree (Option Sig) → Tree Sig
  | .leaf none => i
  | .leaf (some x) => .leaf x
  | .gate d l r => .gate d (graft i l) (graft i r)

theorem graft_value (i : Tree Sig) (o : Tree (Option Sig)) :
    (graft i o).value id = o.value (Tree.plug (i.value id)) := by
  induction o with
  | leaf x => cases x <;> rfl
  | gate d u v iu iv => simp [graft,Tree.value,iu,iv]

theorem graft_count (i : Tree Sig) (o : Tree (Option Sig)) (x : Sig) :
    (graft i o).occurrences x = o.occurrences none * i.occurrences x + o.occurrences (some x) := by
  induction o with
  | leaf x => cases x <;> simp [graft,Tree.occurrences]
  | gate d u v iu iv => simp [graft,Tree.occurrences,iu,iv,Nat.add_mul]; omega

abbrev Row := Fin 544

def leftAt (d : Bool) (l : Tree Sig) (p n : Row) :=
  if d then bit true p (l.value id) else !(bit false n (l.value id))

def follow (p n : Row) : Tree Sig → Sig
  | .leaf a => a
  | .gate d l r => if leftAt d l p n then follow p n l else follow p n r

theorem follow_present (p n : Row) (e : Tree Sig) : 0 < e.occurrences (follow p n e) := by
  induction e with
  | leaf a => simp [Tree.occurrences,follow]
  | gate d l r il ir =>
    rw [follow]
    split <;> simp only [Tree.occurrences] <;> omega

theorem follow_legal {p n : Row} (e : Tree Sig)
    (hp : bit true p (e.value id)=true) (hn : bit false n (e.value id)=false) :
    bit true p (follow p n e)=true ∧ bit false n (follow p n e)=false := by
  induction e with
  | leaf x => exact ⟨hp,hn⟩
  | gate d l r il ir =>
    simp only [Tree.value,bit_bin] at hp hn
    cases d
    · simp only [Bool.false_eq_true,ite_false] at hp hn
      by_cases h : bit false n (l.value id)=true
      · simpa [follow,leftAt,h] using ir (Bool.and_eq_true_iff.mp hp).2 (by simpa [h] using hn)
      · have hh : bit false n (l.value id)=false := Bool.eq_false_iff.mpr h
        simpa [follow,leftAt,hh] using il (Bool.and_eq_true_iff.mp hp).1 hh
    · simp only [ite_true] at hp hn
      by_cases h : bit true p (l.value id)=true
      · simpa [follow,leftAt,h] using il h (Bool.or_eq_false_iff.mp hn).1
      · have hh : bit true p (l.value id)=false := Bool.eq_false_iff.mpr h
        simpa [follow,leftAt,hh] using ir (by simpa [hh] using hp) (Bool.or_eq_false_iff.mp hn).2

private theorem split_mix (d : Bool) (l : Tree Sig) (p n p' n' : Row) (side : Bool)
    (a : leftAt d l p n=side) (b : leftAt d l p' n'=side) : leftAt d l p n'=side := by
  cases d
  · exact b
  · exact a

/-- Any label occurring at most once in the formula labels a rectangle of the protocol. -/
theorem follow_rectangle {e : Tree Sig} {x : Sig} (once : e.occurrences x ≤ 1)
    {p n p' n' : Row} (first : follow p n e=x) (last : follow p' n' e=x) : follow p n' e=x := by
  induction e with
  | leaf y => exact first
  | gate d l r il ir =>
    simp only [Tree.occurrences] at once
    cases h : leftAt d l p n <;> cases h' : leftAt d l p' n'
    · rw [follow,split_mix _ _ _ _ _ _ false h h']
      simp only [follow,h,h',Bool.false_eq_true,ite_false] at first last
      exact ir (by omega) first last
    · simp only [follow,h,h',Bool.false_eq_true,ite_false,ite_true] at first last
      have a := follow_present p n r
      have b := follow_present p' n' l
      rw [first] at a
      rw [last] at b
      omega
    · simp only [follow,h,h',Bool.false_eq_true,ite_false,ite_true] at first last
      have a := follow_present p n l
      have b := follow_present p' n' r
      rw [first] at a
      rw [last] at b
      omega
    · rw [follow,split_mix _ _ _ _ _ _ true h h']
      simp only [follow,h,h',ite_true] at first last
      exact il (by omega) first last

/-- Every ordinary leaf outside the shared inner module labels one rectangle,
even though the leaves inside that module can occur twice. -/
theorem partial_of_trees {S : Finset Sig} {i : Tree Sig} {o : Tree (Option Sig)}
    (ev : o.value (Tree.plug (i.value id))=target) (twice : o.occurrences none=2)
    (ct : ∀ x, i.occurrences x + o.occurrences (some x) = if x∈S then 1 else 0) :
    ∃ (f : Row → Row → Sig),
      (∀ p n, f p n ∈ S ∧ bit true p (f p n)=true ∧ bit false n (f p n)=false) ∧
      ∀ p n p' n', f p n ∉ group S i → f p n=f p' n' → f p n'=f p n := by
  let e := graft i o
  have value : e.value id=target := (graft_value i o).trans ev
  have parent (p n : Row) : follow p n e ∈ S := by
    have a := follow_present p n e
    change 0<(graft i o).occurrences _ at a
    rw [graft_count,twice] at a
    have b := ct (follow p n e)
    by_contra h
    simp [h] at b
    omega
  refine ⟨fun p n => follow p n e,?_,?_⟩
  · intro p n
    exact ⟨parent p n,follow_legal e (by simp [value,bit,target,testBit_top,p.isLt]) (by simp [value,bit,target])⟩
  · intro p n p' n' out same
    have absent : i.occurrences (follow p n e)=0 := by
      have mem := parent p n
      simp [group,mem] at out
      omega
    apply follow_rectangle (e:=e) (x:=follow p n e) _ rfl same.symm
    have hcnt := ct (follow p n e)
    rw [ite_eq_left (parent p n),absent] at hcnt
    simp [e,graft_count,absent] at hcnt ⊢
    omega

end Core.SingleShare

namespace Core.SingleShare
open OuterSmall

def Tree.relabel (f : α → β) : Tree α → Tree β
  | .leaf x => .leaf (f x)
  | .gate d l r => .gate d (l.relabel f) (r.relabel f)

private def name (a : Sig) : Option Sig → Fin 3
  | none => 0
  | some z => if z=a then 1 else 2

private def back (i a b : Sig) (q : Fin 3) : Sig := if q=0 then i else if q=1 then a else b

private def OccupiedBy (a b : Sig) (o : Tree (Option Sig)) : Prop :=
  ∀ x, 0<o.occurrences (some x) → x=a ∨ x=b

private theorem occupied_left {d a b} {l r : Tree (Option Sig)} (h : OccupiedBy a b (.gate d l r)) :
    OccupiedBy a b l := fun x hx => h x (by simp only [Tree.occurrences]; omega)

private theorem occupied_right {d a b} {l r : Tree (Option Sig)} (h : OccupiedBy a b (.gate d l r)) :
    OccupiedBy a b r := fun x hx => h x (by simp only [Tree.occurrences]; omega)

private theorem recount0 (o : Tree (Option Sig)) (a : Sig) :
    (o.relabel (name a)).occurrences 0 = o.occurrences none := by
  induction o with
  | leaf v =>
    cases v with
    | none => rfl
    | some v => by_cases h:v=a <;> simp [Tree.relabel,Tree.occurrences,name,h]
  | gate d l r il ir => simp [Tree.relabel,Tree.occurrences,il,ir]

private theorem recountOrdinary (o : Tree (Option Sig)) (a b z : Sig) (h : OccupiedBy a b o) :
    (o.relabel (name a)).occurrences 1 * (if z=a then 1 else 0) +
    (o.relabel (name a)).occurrences 2 * (if z=b then 1 else 0) = o.occurrences (some z) := by
  induction o with
  | leaf v =>
    cases v with
    | none => simp [Tree.relabel,Tree.occurrences,name]
    | some v =>
      have hit := h v (by simp [Tree.occurrences])
      by_cases va : v=a
      · subst v
        simp [Tree.relabel,Tree.occurrences,name]
      · have vb := hit.resolve_left va
        subst v
        simp [Tree.relabel,Tree.occurrences,name,va]
  | gate d l r il ir =>
    simp only [Tree.relabel,Tree.occurrences,Nat.add_mul]
    have u := il (occupied_left h)
    have v := ir (occupied_right h)
    omega

private theorem relabel_value (o : Tree (Option Sig)) (s a b : Sig) (h : OccupiedBy a b o) :
    (o.relabel (name a)).value (back s a b) = o.value (Tree.plug s) := by
  induction o with
  | leaf v =>
    cases v with
    | none => rfl
    | some v =>
      have alt := h v (by simp [Tree.occurrences])
      by_cases va : v=a
      · simp [Tree.value,Tree.relabel,name,back,Tree.plug,va]
      · have vb := alt.resolve_left va
        subst v
        simp [Tree.value,Tree.relabel,name,back,Tree.plug,va]
  | gate d l r il ir =>
    simp [Tree.relabel,Tree.value,il (occupied_left h),ir (occupied_right h)]

private def insertInner (i : Tree Sig) (a b : Sig) : Tree (Fin 3) → Tree Sig
  | .leaf q => if q=0 then i else if q=1 then .leaf a else .leaf b
  | .gate d l r => .gate d (insertInner i a b l) (insertInner i a b r)

private theorem insert_value (i : Tree Sig) (a b : Sig) (e : Tree (Fin 3)) :
    (insertInner i a b e).value id = e.value (back (i.value id) a b) := by
  induction e with
  | leaf q => by_cases q0 : q=0 <;> by_cases q1 : q=1 <;> simp [insertInner,Tree.value,back,q0,q1]
  | gate d l r il ir => simp [insertInner,Tree.value,il,ir]

private theorem insert_count (i : Tree Sig) (a b x : Sig) (e : Tree (Fin 3)) :
    (insertInner i a b e).occurrences x = e.occurrences 0 * i.occurrences x +
      e.occurrences 1 * (if x=a then 1 else 0) + e.occurrences 2 * (if x=b then 1 else 0) := by
  induction e with
  | leaf q =>
    rcases (show q=0 ∨ q=1 ∨ q=2 by omega) with rfl|rfl|rfl <;> simp [insertInner,Tree.occurrences]
  | gate d l r il ir => simp only [insertInner,Tree.occurrences,il,ir,Nat.add_mul]; omega

def AtMostOnce (S : Finset Sig) : Prop := ∃ e : Tree Sig, e.value id=target ∧
  ∀ x, e.occurrences x ≤ if x∈S then 1 else 0

/-- With at most two ordinary outer inputs, a duplicated module can be
replaced by one read-once formula on a subset of the original bank. -/
theorem collapse_two {S : Finset Sig} {i : Tree Sig} {o : Tree (Option Sig)}
    (ev : o.value (Tree.plug (i.value id))=target) (twice : o.occurrences none=2)
    (ct : ∀ x, i.occurrences x + o.occurrences (some x) = if x∈S then 1 else 0)
    {a b : Sig} (h : ∀ x, 0<o.occurrences (some x) → x=a ∨ x=b) : AtMostOnce S := by
  let e := o.relabel (name a)
  have zeroCount : e.occurrences 0≤2 := by rw [show e.occurrences 0=o.occurrences none from recount0 o a,twice]
  have capped (x : Sig) : o.occurrences (some x) ≤ 1 := by
    have c := ct x
    split_ifs at c <;> omega
  have e1 : e.occurrences 1≤1 := by
    have res := recountOrdinary o a b a h
    change e.occurrences 1 * _ + e.occurrences 2 * _ = _ at res
    simp only [ite_true,Nat.mul_one] at res
    have c := capped a
    omega
  have e2 : e.occurrences 2≤1 := by
    have res := recountOrdinary o a b b h
    change e.occurrences 1 * _ + e.occurrences 2 * _ = _ at res
    simp only [ite_true,Nat.mul_one] at res
    have c := capped b
    omega
  obtain ⟨j,noninc,sem⟩ := shrink e zeroCount e1 e2
  let f := representative j
  refine ⟨insertInner i a b f,?_,?_⟩
  · rw [insert_value]
    exact (same_as_signal sem _).trans ((relabel_value o (i.value id) a b h).trans ev)
  · intro x
    rw [insert_count]
    have fi : f.occurrences 0 * i.occurrences x ≤ i.occurrences x := by
      simpa using Nat.mul_le_mul_right (i.occurrences x) (candidate_once j 0)
    have fa := Nat.mul_le_mul_right (if x=a then 1 else 0) (noninc 1)
    have fb := Nat.mul_le_mul_right (if x=b then 1 else 0) (noninc 2)
    have re := recountOrdinary o a b x h
    change e.occurrences 1 * _ + e.occurrences 2 * _ = _ at re
    change f.occurrences 1 * _ ≤ _ at fa
    change f.occurrences 2 * _ ≤ _ at fb
    have all := ct x
    omega

end Core.SingleShare

namespace Core.SingleShare

/-- The signed rectangle constraint from the original search. -/
def SignedTiling (S : Finset Sig) : Prop := ∃ f : Row → Row → Sig,
  (∀ p n, f p n ∈ S ∧ bit true p (f p n) ≠ bit false n (f p n)) ∧
  ∀ p n p' n', f p n=f p' n' → f p n'=f p n

theorem once_tiles {S : Finset Sig} (h : AtMostOnce S) : SignedTiling S := by
  obtain ⟨e,val,cnt⟩ := h
  refine ⟨fun p n => follow p n e,?_,?_⟩
  · intro p n
    have leg := follow_legal (p:=p) (n:=n) e (by simp [val,bit,target,testBit_top,p.isLt]) (by simp [val,bit,target])
    refine ⟨?_,by rw [leg.1,leg.2]; decide⟩
    by_contra no
    have present := follow_present p n e
    have cap := cnt (follow p n e)
    simp [no] at cap
    omega
  · intro p n p' n' same
    have cap := cnt (follow p n e)
    apply follow_rectangle (e:=e) (x:=follow p n e) _ rfl same.symm
    split_ifs at cap <;> omega

private theorem two_cover (B : Finset Sig) (small : B.card≤2) :
    ∃ a b : Sig, ∀ z∈B, z=a ∨ z=b := by
  by_cases nonempty : B.Nonempty
  · obtain ⟨a,ha⟩ := nonempty
    by_cases other : ∃ b∈B, b≠a
    · obtain ⟨b,hb,ba⟩ := other
      refine ⟨a,b,?_⟩
      intro z hz
      by_contra! miss
      have sub : ({a,b,z} : Finset Sig) ⊆ B := by
        intro x hx
        have v : x=a ∨ x=b ∨ x=z := by simpa using hx
        rcases v with rfl|rfl|rfl <;> assumption
      have bound := Finset.card_le_card sub
      simp [Ne.symm ba,Ne.symm miss.1,Ne.symm miss.2] at bound
      omega
    · exact ⟨a,a,fun z hz => Or.inl (by by_contra ne; exact other ⟨z,hz,ne⟩)⟩
  · exact ⟨zero,zero,fun z hz => (nonempty ⟨z,hz⟩).elim⟩

def Private (S : Finset Sig) (p n : Row) (x : Sig) : Prop :=
  ∀ z∈S, bit true p z=true → bit false n z=false → z=x

def Crosses (S : Finset Sig) (a b : Sig) : Prop :=
  a≠b ∧ ∃ p n pa na pb nb : Row, Private S p na a ∧ Private S pa n a ∧
    Private S p nb b ∧ Private S pb n b

private theorem cover_crossings {S A : Finset Sig} {f : Row → Row → Sig}
    (legal : ∀ p n, f p n∈S ∧ bit true p (f p n)=true ∧ bit false n (f p n)=false)
    (rect : ∀ p n p' n', f p n∉A → f p n=f p' n' → f p n'=f p n)
    {a b : Sig} (edge : Crosses S a b) : a∈A ∨ b∈A := by
  obtain ⟨ab,p,n,pa,na,pb,nb,a₁,a₂,b₁,b₂⟩ := edge
  have force {x p n} (c : Private S p n x) : f p n=x := c _ (legal p n).1 (legal p n).2.1 (legal p n).2.2
  by_cases aa : a∈A
  · exact Or.inl aa
  · by_cases bb : b∈A
    · exact Or.inr bb
    · have ra := (rect p na pa n (by rwa [force a₁]) ((force a₁).trans (force a₂).symm)).trans (force a₁)
      have rb := (rect p nb pb n (by rwa [force b₁]) ((force b₁).trans (force b₂).symm)).trans (force b₁)
      exact (ab (ra.symm.trans rb)).elim

/-- A monotone trace with at most one extra binary gate and a rectangle
obstruction requires one inner module that leaves at least three ordinary
inputs, hits every forced rectangle crossing, and satisfies comparisons of
independently forced positive and negative rows. -/
theorem one_share_necessary {k : Nat} {S : Finset Sig} (run : Live k 0 S) (budget : k≤S.card)
    (obstruction : ¬SignedTiling S) :
    ∃ A ⊆ S, 3≤(S\A).card ∧
      (∀ a b, Crosses S a b → a∈A ∨ b∈A) ∧
      (∀ p n p' n' : Row, Respects (S\A) p n' → Respects (S\A) p' n → ¬Respects A p n) := by
  rcases once_or_one_shared run rfl budget with plain|shared
  · obtain ⟨e,ev,cnt⟩ := plain
    exact (obstruction (once_tiles ⟨e,ev,fun x => Nat.le_of_eq (cnt x)⟩)).elim
  · obtain ⟨i,o,ev,twice,ct⟩ := shared
    let A := group S i
    have roomy : 3≤(S\A).card := by
      by_contra small
      obtain ⟨a,b,cover⟩ := two_cover (S\A) (by omega)
      apply obstruction (once_tiles (collapse_two ev twice ct (a:=a) (b:=b) ?_))
      intro x hx
      have cnt := ct x
      have mem : x∈S := by by_contra no; simp [no] at cnt; omega
      have absent : i.occurrences x=0 := by simp [mem] at cnt; omega
      exact cover x (Finset.mem_sdiff.mpr ⟨mem,by simp [A,group,absent]⟩)
    obtain ⟨f,legal,rect⟩ := partial_of_trees ev twice ct
    exact ⟨A,Finset.filter_subset _ _,roomy,fun _ _ edge => cover_crossings legal rect edge,module_of_trees ev ct⟩

end Core.SingleShare

namespace Core.SingleShare.Cubes

/-- Bit i selects membership of the i-th wire in the proposed inner module. -/
def selector (A : Finset Sig) : List Sig → Nat
  | [] => 0
  | x::w => (if x∈A then 2^w.length else 0) + selector A w

theorem selector_lt (A : Finset Sig) (w : List Sig) : selector A w < 2^w.length := by
  induction w with
  | nil => simp [selector]
  | cons x w ih =>
    simp only [selector,List.length_cons,Nat.pow_succ]
    split_ifs <;> omega

/-- Concatenate two bit vectors with exactly span bits in the low half. -/
def join (span lo hi : Nat) := 2^span * hi + lo % (2^span)

private theorem join_at (span z lo hi : Nat) (side : Bool) (hz : z<span) :
    (join span lo hi).testBit ((if side then span else 0)+z) =
      if side then hi.testBit z else lo.testBit z := by
  unfold join
  rw [Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos _))]
  cases side <;> simp [hz,Nat.testBit_mod_two_pow]

/-- Each selected bit represents all subsets accepting the required wires and
rejecting the forbidden ones. A wire can be irrelevant to this condition. -/
def cube (need ban : Sig → Bool) : List Sig → Nat
  | [] => 1
  | x::w =>
    let sub := cube need ban w
    join (2^w.length) (if need x then 0 else sub) (if ban x then 0 else sub)

theorem cube_at (need ban : Sig → Bool) (w : List Sig) (A : Finset Sig) :
    (cube need ban w).testBit (selector A w) = true ↔
      (∀ x∈w, need x=true → x∈A) ∧ (∀ x∈w, ban x=true → x∉A) := by
  induction w with
  | nil => simp [cube,selector]
  | cons x w ih =>
    have ev := join_at (2^w.length) (selector A w)
      (if need x then 0 else cube need ban w) (if ban x then 0 else cube need ban w)
      (decide (x∈A)) (selector_lt A w)
    simp only [decide_eq_true_eq] at ev
    change (join (2^w.length) _ _).testBit ((if x∈A then 2^w.length else 0)+selector A w)=true ↔ _
    rw [ev]
    by_cases xin : x∈A <;> cases nr : need x <;> cases nf : ban x <;> simp [xin,nr,nf,ih]

/-- All assignments leaving at least q ordinary leaves outside the module. -/
def room : Nat → Nat → Nat
  | 0,q => if q=0 then 1 else 0
  | m+1,q => join (2^m) (room m (q-1)) (room m q)

theorem room_at (w : List Sig) (A : Finset Sig) (q : Nat) :
    (room w.length q).testBit (selector A w) = true ↔ q≤(w.filter (fun x => decide (x∉A))).length := by
  induction w generalizing q with
  | nil => by_cases h:q=0 <;> simp [room,selector,h]
  | cons x w ih =>
    have ev := join_at (2^w.length) (selector A w) (room w.length (q-1)) (room w.length q)
      (decide (x∈A)) (selector_lt A w)
    simp only [decide_eq_true_eq] at ev
    simp only [List.length_cons,room,selector]
    rw [ev]
    by_cases h:x∈A <;> simp [h,ih]

def forward (p n : Row) (x : Sig) := bit true p x && !(bit false n x)

/-- A single four-row implication forbids one cube of module memberships. -/
def rowCube (w : List Sig) (p n p' n' : Row) :=
  cube (fun x => forward p n' x || forward p' n x) (forward p n) w

theorem rowCube_sound {w : List Sig} {A : Finset Sig} (sub : A ⊆ w.toFinset)
    (p n p' n' : Row)
    (valid : Respects (w.toFinset\A) p n' → Respects (w.toFinset\A) p' n → ¬Respects A p n) :
    (rowCube w p n p' n').testBit (selector A w)=false := by
  apply Bool.eq_false_iff.mpr
  intro hit
  obtain ⟨inside,outside⟩ := (cube_at _ _ w A).mp hit
  apply valid
  · intro x hx pos
    obtain ⟨mem,no⟩ := Finset.mem_sdiff.mp hx
    cases h : bit false n' x
    · exact (no (inside x (List.mem_toFinset.mp mem) (by simp [forward,pos,h]))).elim
    · rfl
  · intro x hx pos
    obtain ⟨mem,no⟩ := Finset.mem_sdiff.mp hx
    cases h : bit false n x
    · exact (no (inside x (List.mem_toFinset.mp mem) (by simp [forward,pos,h]))).elim
    · rfl
  · intro x hx pos
    cases h : bit false n x
    · exact (outside x (List.mem_toFinset.mp (sub hx)) (by simp [forward,pos,h]) hx).elim
    · rfl

/-- A crossing certificate forbids every subset that omits both forced labels. -/
def edgeCube (w : List Sig) (a b : Sig) := cube (fun _ => false) (fun x => decide (x=a ∨ x=b)) w

theorem edgeCube_sound {w : List Sig} {A : Finset Sig} {a b : Sig} (ha : a∈w) (hb : b∈w)
    (covered : a∈A ∨ b∈A) : (edgeCube w a b).testBit (selector A w)=false := by
  apply Bool.eq_false_iff.mpr
  intro hit
  obtain ⟨_,outside⟩ := (cube_at _ _ w A).mp hit
  rcases covered with h|h
  · exact outside a ha (by simp) h
  · exact outside b hb (by simp) h

end Core.SingleShare.Cubes

namespace Core.SingleShare.Cubes

inductive Rule where
  | row (p n p' n' : Row)
  | cross (p n pa na pb nb : Row)

def pick (w : List Sig) (p n : Row) := (w.find? (forward p n)).getD zero

def privateCell (w : List Sig) (p n : Row) (a : Sig) := w.all (fun x => !(forward p n x) || decide (x=a))

private theorem privateCell_spec {w : List Sig} {p n : Row} {a : Sig} (ok : privateCell w p n a=true) :
    Private w.toFinset p n a := by
  intro x hx ptrue nfalse
  have v := List.all_eq_true.mp ok x (List.mem_toFinset.mp hx)
  simpa [forward,ptrue,nfalse] using v

def crossOK (w : List Sig) (p n pa na pb nb : Row) (a b : Sig) :=
  decide (a≠b) && decide (a∈w) && decide (b∈w) && privateCell w p na a &&
  privateCell w pa n a && privateCell w p nb b && privateCell w pb n b

private theorem crossOK_spec {w : List Sig} {p n pa na pb nb : Row} {a b : Sig}
    (ok : crossOK w p n pa na pb nb a b=true) : a∈w ∧ b∈w ∧ Crosses w.toFinset a b := by
  simp only [crossOK,Bool.and_eq_true,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨⟨⟨ab,ha⟩,hb⟩,a₁⟩,a₂⟩,b₁⟩,b₂⟩ := ok
  exact ⟨ha,hb,ab,p,n,pa,na,pb,nb,privateCell_spec a₁,privateCell_spec a₂,privateCell_spec b₁,privateCell_spec b₂⟩

def ruleMask (w : List Sig) : Rule → Nat
  | .row p n p' n' => rowCube w p n p' n'
  | .cross p n pa na pb nb =>
    let a := pick w p na
    let b := pick w p nb
    if crossOK w p n pa na pb nb a b then edgeCube w a b else 0

def unionMasks (w : List Sig) : List Rule → Nat
  | [] => 0
  | r::rs => ruleMask w r ||| unionMasks w rs

private theorem union_sound {w : List Sig} {A : Finset Sig} (sub : A ⊆ w.toFinset)
    (edges : ∀ a b, Crosses w.toFinset a b → a∈A ∨ b∈A)
    (rows : ∀ p n p' n', Respects (w.toFinset\A) p n' → Respects (w.toFinset\A) p' n → ¬Respects A p n)
    (rules : List Rule) : (unionMasks w rules).testBit (selector A w)=false := by
  induction rules with
  | nil => simp [unionMasks]
  | cons r rs ih =>
    simp only [unionMasks,Nat.testBit_or,ih,Bool.or_false]
    cases r with
    | row p n p' n' => exact rowCube_sound sub p n p' n' (rows _ _ _ _)
    | cross p n pa na pb nb =>
      by_cases ok : crossOK w p n pa na pb nb (pick w p na) (pick w p nb)=true
      · obtain ⟨ha,hb,e⟩ := crossOK_spec ok
        simpa [ruleMask,ok] using edgeCube_sound ha hb (edges _ _ e)
      · simp [ruleMask,ok]

def covered (w : List Sig) (rules : List Rule) :=
  let promising := room w.length 3
  decide (unionMasks w rules &&& promising=promising)

/-- A verified list of forbidden cubes covers every module with three ordinary
outer inputs. Each cube is checked independently against the current wires. -/
theorem covered_sound {w : List Sig} {rules : List Rule} {k : Nat}
    (budget : k≤w.toFinset.card) (obstruction : ¬SignedTiling w.toFinset)
    (check : covered w rules=true) : ¬Live k 0 w.toFinset := by
  intro run
  obtain ⟨A,sub,large,edges,rows⟩ := one_share_necessary run budget obstruction
  have eq : (w.filter (fun x => decide (x∉A))).toFinset = w.toFinset\A := by ext x; simp
  have len : (w.toFinset\A).card ≤ (w.filter (fun x => decide (x∉A))).length := by
    rw [←eq]
    exact List.toFinset_card_le _
  have here := (room_at w A 3).mpr (large.trans len)
  have miss := union_sound sub edges rows rules
  have good : unionMasks w rules &&& room w.length 3 = room w.length 3 := of_decide_eq_true check
  have atBit := congrArg (fun m : Nat => m.testBit (selector A w)) good
  simp [Nat.testBit_and,here,miss] at atBit

end Core.SingleShare.Cubes

namespace Core.Hybrid
open KWMemo SingleShare.Cubes

def moduleCheck (k t : Nat) (w : List Wire) (rules : List Rule) : Bool :=
  decide (t=0) && decide (k≤w.length) && BulkKW.excludes 467 19 (sigsOf w) && covered (sigsOf w) rules

theorem moduleCheck_sound {k t : Nat} {w : List Wire} {rules : List Rule}
    (ok : moduleCheck k t w rules=true) : Impossible k t w := by
  simp only [moduleCheck,Bool.and_eq_true,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨mono,budget⟩,blocked⟩,sweep⟩ := ok
  subst t
  intro m hm S τ rep run
  obtain ⟨nd,eq,_⟩ := rep
  subst S
  have card : (sigsOf w).toFinset.card = w.length := by rw [List.toFinset_card_of_nodup nd,sigsOf_length]
  obtain ⟨z,hz,conflict⟩ := BulkKW.missing_bit (of_decide_eq_true blocked)
  have no : ¬ SingleShare.SignedTiling (sigsOf w).toFinset := BulkKW.no_tiling hz (by decide) conflict
  exact covered_sound (by omega) no sweep run.live

def child (tab : Table) (rulesAt : Nat → List Rule) (k t : Nat) (w : List Wire) : Bool :=
  (decide (w.length+t=k+1) && BulkKW.excludes 467 19 (sigsOf w)) ||
    (let h := tab.hint k t w
     if h &&& 3=1 then moduleCheck k t w (rulesAt (h/4)) else childOK tab k t w)

private theorem child_sound (tab : Table) (rulesAt : Nat → List Rule) (k t : Nat) (w : List Wire)
    (prev : ∀ i < tab.count, (tab.node i).k=k → Impossible k (tab.node i).t (tab.node i).w)
    (ok : child tab rulesAt k t w=true) : Impossible k t w := by
  simp only [child,Bool.or_eq_true] at ok
  rcases ok with hit | hit
  · exact BulkKW.excludes_sound (by decide) (of_decide_eq_true (Bool.and_eq_true_iff.mp hit).1) (Bool.and_eq_true_iff.mp hit).2
  · by_cases moduleRow : (tab.hint k t w) &&& 3=1
    · exact moduleCheck_sound (by simpa [moduleRow] using hit)
    · have h : childOK tab k t w=true := by simpa [moduleRow] using hit
      by_cases normal : (tab.hint k t w) &&& 3=0
      · simp only [childOK,ite_eq_left normal,Bool.and_eq_true,decide_eq_true_eq] at h
        have res := prev _ h.1.1.1.2 h.1.1.2
        rw [h.1.2] at res
        exact perm_impossible (permCheck_perm h.2) res
      · exact KWCertificate.certified_sound (by simpa [childOK,normal] using h)

def node (tab : Table) (rulesAt : Nat → List Rule) (i : Nat) : Bool :=
  let s := tab.node i
  match s.k with
  | 0 => !search 0 s.t s.w
  | k+1 => !stepTest k s.t s.w (fun w => !child tab rulesAt k (s.t-1) w) (fun w => !child tab rulesAt k s.t w)

theorem all_nodes (tab : Table) (rulesAt : Nat → List Rule)
    (valid : ∀ i < tab.count, node tab rulesAt i=true) (i : Nat) (hi : i<tab.count) :
    Impossible (tab.node i).k (tab.node i).t (tab.node i).w := by
  generalize level : (tab.node i).k=k
  induction k generalizing i with
  | zero =>
    have h := valid i hi
    simp only [node,level,Bool.not_eq_true'] at h
    exact exclude_search h
  | succ k ih =>
    have h := valid i hi
    simp only [node,level,Bool.not_eq_true'] at h
    apply exclude_step _ _ h <;> intro w no <;> exact child_sound tab rulesAt k _ w (fun i hi eq => ih i hi eq) (by simpa using no)
end Core.Hybrid

namespace Core.HybridData
open KWMemo KWCertificate
def hash (salt : Nat) (v : List Wire) (k t : Nat) : Nat :=
  (v.foldl (fun s w =>
    let x := ((w.1.1 % 1048573)*(65537+salt) + (w.1.2 % 1048573)*131 + 317) % 1048573
    s + ((x*x % 1048573)*x % 1048573)) (75*k+263*t)) % 1048573
def shiftsData0_ : Nat → Nat
  | 0 => 0x1c0110000080001010200061000020002020cc0200011944002ca00000000000000060002010005
  | 1 => 0x4000c800000100040111a8500001840000460180e10800008001084200004708c030000401001
  | 2 => 0x40058402180060000108040000003002001801084603080010000008c309840000042800118024
  | 3 => 0x8020004c000c200800208402091040800718800000450300000081084a019401000000002300c21
  | 4 => 0xc21000101c00200201800008000084401040102803084000806000400008800000010000
  | 5 => 0x8000a00000041000e000001000002040008040080230004000000100000040208c200000000440
  | 6 => 0x8004098405000012800000e100481000a0000000800108401000620000028820000011084000803
  | 7 => 0x2200000000a1000061000508000000e100400011000000000c410146000021030000000021401
  | 8 => 0x420284e0000004082100c0200c0008041080206000750000080000000218462300031008009c20
  | 9 => 0x80610a00100400080c208c04000241a40000802000800004100006500e900022098c00040010000
  | 10 => 0x1003084811880008800010200082001820008200002058001280230800200902008010008110421
  | 11 => 0x1000000800000070000000881000260000800400000210002030c000800700000004a30084001800
  | 12 => 0x80040000100023004c00802000820000000084238000384200142009023298000000120002100e2
  | 13 => 0x200042208000000011004000c04100402802100020180020006002401000001044841846504a0
  | 14 => 0x1802010002080e110000190201004728065008430000008c00000e000006180e10004200c20
  | 15 => 0x28421084020842010062280211002100021000616840000000000010000100401480020044000800
  | 16 => 0x80002000000404100010840411800080e30000100c600840700000000402a000000033800100000
  | 17 => 0x802138403080006802010c2019000200013800030800000410000008000028004846002000
  | 18 => 0x1c00000011848108400018216804701004104020800000021300200004100420000020840100049
  | 19 => 0x18841100001000000001008000044308020000220000500000100030800010023100000804200065
  | 20 => 0x1c000082130422008800000700442000090000000001088400842001c010840c090000000000c00
  | 21 => 0x88000040100020000201840800002100c02002000c0330002004000068100000088c00b404
  | 22 => 0x5640006000000080600064108440000000180500022490600080110044188a5200400884000805
  | 23 => 0x884700c000002100820000600006500ca008d603040618421280610040010004000040480508845
  | 24 => 0x18805008c3000201044000c0018001300610004018001010210000210c0400000084002002518003
  | 25 => 0x84000002100030000238c000042000c40180200000300000108400002200000080a00080009823
  | 26 => 0xc201804000000000630800208003084630142000062080810840508020100380002008801
  | 27 => 0x100c20084a00082028c0009000018000002000001000030a8000000248000004031004009020
  | 28 => 0x8460080031000101420004001006001c01100030004008c80000404002100ea10804400400104e0
  | 29 => 0x8464008021940201c80004000008100081010022040202005100420800108000000000000000400
  | 30 => 0x290011080038804008001084100880010211000920401006e1088a50000508806131210842008806
  | 31 => 0x180000040100c0108c01100030182208001180c3004a008484000001840018000000001906208020
  | _ => 0
def shiftsData1_ : Nat → Nat
  | 0 => 0x820400400098208000080202904000820000800800302420000001804010023098010800110800
  | 1 => 0x8008c0021403000000000000000200001800008c800044000401024210002708820004e010000
  | 2 => 0x80000005080003880700c203000000000080000048301c61290200800808442080200002110022
  | 3 => 0x4042000020008031040200042000201800410040180000000000000580a110005000810006000044
  | 4 => 0x200000880b00c640090010c4008840284a1180000082230020080221000101000100200000008086
  | 5 => 0x440080081040100003000000000010403018605140108c00005e1a8c2010409000010040029020
  | 6 => 0x18010040210021005a010c8100040180000880000d4200400080000886400004000005040230000
  | 7 => 0x80240006100420000250052130040700000a0000040008001008a00000000000000000042508421
  | 8 => 0x900100400118002200408001000403000010060184240040000000008240840208400108e000465
  | 9 => 0x20010c100c4118c00030200808000000000000000100c83000003944019002208022800700800
  | 10 => 0x1401000400046308882084c02800100021008402000808000080a00008040402000630884301420
  | 11 => 0x21001010210000002c0000021080a10002210040004a0000071000100020000030080111c2300000
  | 12 => 0x10003000000280000c011040110020004221800000c0000021004800002100001118640000509024
  | 13 => 0x806508040000800004300001080400040310c00300000058000001010410b003000430084103c20
  | 14 => 0x8c820004000000080c03804100c2058402000640000810460180011042100c002800100000
  | 15 => 0x40100a10040100c00000020046000004000030082100002000030006008000014221080300064
  | 16 => 0xcc01840010001088001002368c0000009000201004212801100000088508001080010800078080
  | 17 => 0x18405088201000200400000200044008040100e110020100400100150c4000000008031802400020
  | 18 => 0x4000800100040000000002100800080001042100001380608040200cc028800000210000000800
  | 19 => 0x80200040310c00018600002309c000044208040000041000109c0300002008000802000c0208004
  | 20 => 0x20004c00002011804010004080200c24301c300081100c0008610002310c20084210040121c00
  | 21 => 0x100110020114a0000200080000883000a22040b1002708400180630006118020080200000008460
  | 22 => 0x49001180200082200002204000800128800108200186008000004050002518028000c70240000045
  | 23 => 0x1800530c01000200100000040000aa01400004400002010824100010882208020000000100003000
  | 24 => 0x6220001008810040000800018041000400c201000200400408200842008400014030806608000
  | 25 => 0x50420000c338c00004000000108080008200006208c0079c22000400000000c200142613c80080c0
  | 26 => 0x1880300103181a060000008010804220005000000040600401100010040200480389210040010c42
  | 27 => 0x40008021000203840000020008215000000004010c100020100003000b090010000008500
  | 28 => 0x800084003846518c00000610100008c442080009c40000000880000c000904a0002000c0228041
  | 29 => 0x203000008041000210000000020005631004001411200002000000000000000848100000
  | 30 => 0x3004100400204401062009402000600004200c2000420400010140208401180000802300c0610000
  | 31 => 0x62100a0000630040108c6100ca00000200001000413080001c070000000001204061800418002
  | _ => 0
def shiftsData (i : Nat) : Nat :=
  match i/32 with
  | 0 => shiftsData0_ (i % 32)
  | 1 => shiftsData1_ (i % 32)
  | _ => 0
def shifts (i : Nat) : Nat := (shiftsData (i/64) >>> (5*(i % 64))) &&& 31
def slotCodeData0_ : Nat → Nat
  | 0 => 0x6993f5d1303a8631911439eda80000000dd600043ab439dc0c556118001b0a000138b9600008d700000011bec2300021d400000000036e5510c270000000000c2300031d1eea00000000003de000419a4a50ea0000000000000000569a3599185e31a1b094000d62
  | 1 => 0xfd20001c692b0000f7346c80018ea00067c9c949dea2f648add95a6cec0000000000000470a6703fcb847c2ad90000d6f499000184a8da477a38ca0a10e74da1d430a00000021c000046a0003e750d083147a24d51b0a65615916c0000007d6000188afbd
  | 2 => 0x2190000cea0000001d1000058d14b0000b1b279a0ec8d892d00021d4c60cc85f026054e81d243ab08ddaadae71abb311c2000000231c6040000001db594cd6546f00014220000000000000b9746e0000000000000000000000000034a50eac5066632d55a6000
  | 3 => 0x23bc00000000000011aa87500035251b689a46bb13194077800000011ae8e575c29b11e000046831911ac00000032611b6b6343ca5740000000000001636e47000217db72e4543a8000fd62a7000308c5dc92e000000000000000021c90ea00063f0000000000
  | 4 => 0x408b0e197a0006dca2f16f84af68eadb0000c230001fd589475a000000000000061f80000000006c6b0940000bf00030f0000d5e6c20000000000000000000000000008f0000b5700000011b8cfa80d80000008e83930d7000000000000000008da0002960000000
  | 5 => 0x46aa6fdf02984442b08d88200040880018a6f4b0000000000eb916a9ff51e000000000010ea0007320001d1a000000363912c1f40000000000997000238507e0005f900010eae475330001846000442b0911b068946a8000fd600059f319146800000010edd38d28
  | 6 => 0x61180000008d800000007fe0003f58001e2e00061280f986400024a8000000000437aea000000046bbb10000000000000000000000000000008d56118001fe27ec44da1d400000046e2a200006a85b0a43c000c4a00000000000000000001fceda700037fd47a8d8
  | 7 => 0x578000000000062080000000004af0001c6c000000000194e0000002df18463c27e6308c0000000002e040000004cb000107e0001f7800184800006bb80500ca4b4f637c46200000000000000d0675a8000000000000241986e000000000000059b0000001ab2bac
  | 8 => 0x189c00061eb7158467fc7bec0c184a0000000000000875611baa000018b000000000000062d23fc000d4961e000197c0001e725a00004140000000000c2e0000001be0c2369c0000082d69611ac9584800047bb09400000001cb5d4000d4f40900011a806e
  | 9 => 0x29a80000000000000000000b801a0ab750ea00057c80000008d561724c800000074d27011c2000000375c00000000026e40000004738ae107ea5a61331acb6e38426a308c000c422ad80016cc0004838000000aa03f8902800000076d0001332c2300033591b6bc7
  | 10 => 0xa5c000000308c000000583b08d1e67d543a80000000001d4800151022a544405043a00000002907ec000000295800000000024591b600043aac45ada0002a2000000000004fb08cbaa00054400002ac4e675a852d3d8000000000136400044e8000000000
  | 11 => 0x4713a4d1ac51e0001198444c5e46a39d800034e000000000088500000011b887546a23dd854c9f0003a7d82ce490002a2147c00000000011b0afb0d28000f96ccf00030980000000002acce528d543ab72400000032438d400000000040240008755918000000000
  | 12 => 0x34248ea0006412c9130cfb00000000000b4b077800000000000035191c28dd00000017e800000011fc000c1a66024289ce0000000000ff400043a800000008e611a38890687500037955d400004109dc000e10542a99d1c28e165d80000006bf0002439846569
  | 13 => 0x25846b4c2351b3010000c5a0000000000000000000151092300000000008dc46aa3a858c8e37f124e4642f470000000fda000611999dcac87576f9805ace0002fb800000000000023549b4862577b08dce4c2b0001025482c23000308d93c000633000000092e
  | 14 => 0x55cac6c000980620000170e0005af3b507b6eab21e3a951de000000000000000000000000008e354400011aa8d30002094000c3a584ba180007f7506000184c0000b5b5551b20001288001aae6cf121a360000b2a7eb0000000caf0000001b86ce84f33c445088eb
  | 15 => 0x5208001136c231b3b0e0000000611800202000000000000008c74e10000000c241c9308c000c3e46a82b185298756030fddfe1070002c5c000000544000000000076f23580004bd000200000000047c0000ece0000000000000000000332d0eac2a00021d4d0e000
  | 16 => 0x537a3d80000004748720000d3000026a8000000479800000087576e8000000c230002c550b48780002a2184ac2300011bd2e2b0a611ad2800000000021d48220000000b800001b2442a2752ec0000003aa8000b970000000dc661200023700000004251a9917ac46
  | 17 => 0x77a37a4000000614a1d5876c2600023540000000000cbd8468e04218000000c4a46a39650ea00000021b46f4fe500022f00008d50001f7ce960000000000000ca3000147184600026ca35cfd8000011800190ec2300000000008750002edd21c0004fe374d1ea717
  | 18 => 0x4a6000122869c155b7fd8463a201821d40000000000000000c6e000000000000000029f554a0d0611b08c000c2a3f58001846dc800024540007ec0003775a680003c4244800000046b8000000b0362780011f6aa23cd23acfd82ed0003e6984600038f8000000000
  | 19 => 0x1aba0000003ad58640006118000000df047c80015100000b6000000000046a2e05854aa30f6b091a3cb1a00000000000000003924f50c380000000eb600041fbacc0000000000000000000000000152800000030b4000c2300031180009800000000000000
  | 20 => 0x18520005422ffc00000000025fc93ec23000310d21cd6e0000001d6a0005d23cbc8262760000000000000476255c9c27aa0001261884a1c00032a4000dcc00030940000005cd3bcc00000061180000000000003285384a8848821d5b72cc80000000000000
  | 21 => 0x24d91c000000000011b69ff659237d43a00000000000000000000000000c25413a9c91acfb62bb800107e000000000124cb1b00000000010046478178000000477b9511ae00000000013b6000000000000000058eb049254b1b7b1308d1c28e0
  | 22 => 0x50034600000006808000000000000000163600000000000000000ce800000095a652a37800000060c315c00000000000000000000001f6d7500000000000000ec46b1000000000061e24b000000079c20a18640000a50000000ad300000011acc2300021d4000c34
  | 23 => 0x611b18150c000276b04000000046b2e95a9a000000000000000058922000000000000000000408000000186200046e00000002b94b700011b2a425bf03a8000000000000000037f47f80000000006149564000cbb61280013ac0000898c500d6435
  | 24 => 0x5b0b83c000c860002d559b0e574d81390000c98000000000080c16f800044a000612b698000000000000000071c6118001846c6700031b538cab54cdaff91b292b3a88000000c68000000000090d41f8001d7c92a80880000003ba00000000000000000000000000
  | 25 => 0x611ab458580000000000000000000000162200062800000000000000f7800000031080000004840000000000ddc0003c44000000479000000038a4d5acc91d4c2346b8001c3ac330001fd800000000000000000005788000000c230002350000b110001e380008d8
  | 26 => 0x2cf9e49be600000032d192c0a1280aa2000000046a00000000000000001846000291970400022e0000000000000000000000000047400000000001d821d4dc0c2500000000008de11d80000000002d0000000000075c0000000bc1663b25800000001b80010ea000
  | 27 => 0x293400000000000000000006d619898480000002b78000000000000184a000649135c000b1b00021d51b48d419100012301c046db2a1924c233f623500009a2737a1d5846000000000000000061184c13640006273fd19421f900000000000000001fadffe7eb
  | 28 => 0x6120ab40000000000001d32b150002aa18468d40001b2d300a8800037cd848c4000000000005df4278001d3a2961ea30c000000070c00011b6000000245d05c0003f7000000000000034140000002288000000000638800000000000000000000000000000000000
  | 29 => 0x46b8001bcee2655aa1d4522ea97ea2d44954a3264ca1d50ea5aa611b0ad60e0006282bd51b28da68e80000000000003a100009051d5bec8a66a7000023ec00000000000000000000000000000988000236135cc2300000000000003c780017ac4c100031f18c6fe7
  | 30 => 0x5438001850b8f2b9b5d8000ea174800011fc0000e60facce20000002379286a1174b8afcb180000000001178a112238001428eb85758001c009793269d210eab1276fa1d400000046aa374efa0006ca01f1a2a5a84a00001864add38c80000000000000000000000
  | 31 => 0x362313d860ada74b8000fc4c230002a21bb4000000000000000000031e51b40002538001240ac820aa35db72e3246e21d5d9c2647368001894000000000000000000000000002170000000000000611c034000000000193131a0000000b6c0009f27cc2cce030e4c
  | _ => 0
def slotCodeData1_ : Nat → Nat
  | 0 => 0x61380000000000000001736b9a00000000000000001c0164000000000015dc48f4248bfd88696a475345186a00000035293f4c6441f8000000000612b0940009881523c5128600000000018ea00000000011b691d69a000186000000023980000000000001846980
  | 1 => 0x3fec000707616000000000032c8001d5a00000024c187e8d400000000000000000000000c6466310f91b00000000000000000000000000000000000000009b546a000022c00000000000000000002c3c000c2568103791b60000001f940003160000000000000
  | 2 => 0xb2187cedf00039b09968e04258001226638000308dd2c8e27348001a16328651a0f984600000039f494487500021d50ea0000003334000a3800000000008d748c800184a8dd7fa995c0000000000000000b28000391d4580000003a2800000042880000002fa
  | 3 => 0x86000172cbc76133164bce000000000000094a559a4d400000014913a943e8750000000000d18000308c00093943aa1d439ac46619000000000048da4795108d561432246a00005d30001476a97000235dd7a0000000001b30bff00000000000000000000c3a000
  | 4 => 0x27c0000a8900000000020006120001a84000000000107e00000000000000006240000000e4540500000000001b880000007ed186a1d6010c2c46b243591094c43a8001252022612800000000000000000008ae61500000000000000000000f1500034b51acc44
  | 5 => 0x612407800000000000000000000003cf91f82aa4dab1edab48d869d3228d7887500006b8000c5400032993008df75a9085f989e743a87f073a8750002fe4000000614a8c50a400000006b4000b1f47723551ac743542badc0000004c000000000000000000000000
  | 6 => 0x21d56ae000000000000000000023600000000002355846000000000191c000000366d71a8752383d0800000014fac18000909000000000000043a933800000000024e204ace1000000000000075a80018c4f187733bc990cf7e7e201118463b5000398d2388eb
  | 7 => 0x2d10bed1c08752b19ad46dec5c13eb0f9062fc173723618ba00043a80000000000002140788000507000000000000000000000000000000000ec800000018660007d1800000036900000010eadf95209fac00600076230b0000f5812023680003314b18000000000
  | 8 => 0x7d2b15800000000030bc00000000039880008d500030354d800000000000004411bb2a41336c2c46aa375be4ce3611b12c4e80002ba0001af698043a8175c8c0000001d500000200000001e3c00000030bc0000000002f100000000f921c51b902f46a312c000000
  | 9 => 0x613800000000058db65945e313611a5e186ac2346c3f41b34875706000000080436f94480000000000000000f0c21630b5864b127e5800000075c000000010e0002848000000afb5acba491bc3f77bf8fc188e2d44872a2184ec2347bb26924a7f00000000000002
  | 10 => 0x1f5221400000000031bc000f24537a1d56c42596dda51000000000000000000000000c2000038c34d000024a0000003d351d48d4000000000000046a00018700000000000000000691308d84e981226341812af9622c00000008c40000001846c230002350000c2a
  | 11 => 0x7280dd11ac5380000b9800000000000000000000000e0400000000011a0000ad475c800000000046a3b21d18c235ceb85c000c5b62a000000000000000010ea00063e27e584600400000011ba000000365dc76000000000000000061192240009c1715b0bc000ee8
  | 12 => 0x5de8000740c2346d0000ec40000000001d8e9057cc0000000000471b08d636536783a3500002dd00035f4c3c2a15ab800187c05b3ceace99f6acb5e18959d92c3000023587368f40000001f9acd3520a1d5860aa1554a49d0ea0004051941848ca130489f9562912
  | 13 => 0x24fc000fa44d100000000004c70000000c260002d01e8e0000002bf9846c2607400000008d700000000008d62f329f002ac2343aa9918460000002b61256d801a02844a1a4ab43a80001c400061880011b857f46b00013bc0003a83090000486
  | 14 => 0x21d4fe83d147000000009b75383234000dbd47300011c4c5b3c280000000000000001d008dd608be914c820c48cad5dd049804bf328420aa154113f340008db0000000000c230000000000000405800000000045300018460000000000a8ac23000308d81ec2a
  | 15 => 0x194c0004e8a3e59181475a18000001007000262c0007a2518000121c0000000001846000000000000000064ab3755d800076b9fac00af3a73eac54000000000000000084d000000000000015f2dd0000d5400020300007ec26500000000000000000000c23
  | 16 => 0x563bf98000000473a399af48da3d239d40000006209dc0000c2466c23a52a60ca185226400000046e1fad1d8000000376c00034600032502669802152361522eb3000000126a7eb0000001300c2321134dc0002e774b38a5462d6c50f80003ac0004700000000000
  | 17 => 0x151a76800000000030dcfd8dcf5920000b880006171f4d92836e000000037400000000013180000000001d468db1a400000a0b8b0000001bac0006130d651ca0000da000122ec343150000000f9805c2c1c2588d8481b9a52c4ae6048a4390ea433724395d07c000
  | 18 => 0xc4b0000000000c2a46c24b40009536220f692facac41680010ea00070230916360003f780000008d5680be003d6c3f3432361088ee44fc0000000000643000000000057f3a15bf2e113883bad398000000000121a8750000000a36c2300037999a0000
  | 19 => 0x11a000000087500021d51f8bb043a80000000000002438000a1a0000000000f1f0003e81846ee46e600000000060001a95b1400000000000000000000001e1a0000000c9c00037b566000184e8755ab800184600000000016ba01100012311a887579a3674000000
  | 20 => 0x149400046f21d5c8c0000000000000000000000032e0007f8235d0a000068d0d7d59c000000000185e00010d236568e00047200011c0c45079a2c0000000000144c00000000000000008755c300012120004720000b8a00042ebb8d2f0cec0001fb0000000
  | 21 => 0x6119108000674611b11ca4a000000000000000054e0000000b1b3f623f46c2000000000000058613cb08c000000000000000000000000000000000000000804a8852180002fa2134d8b3d80005f44db00010cc000000000185883e6118aec00089900037f0000000
  | 22 => 0x17f40007d4c050000d160002ee10fcc34611b1810aea806ee31598466ac000000000000000029180008d7080bf3456e92f0002715936000611a35997ca19000000000000000034cd846000476800090e00000000011a88f64e50c30000c230000dcdb0ea88
  | 23 => 0x23800000000001f75a36b11731a3657d487553e308d85a6fc4052a911c0543000000114a8f800000012360002073cb9cdee40000000000000000002780000000000000000000000000000000002628dd4c000046a1fb11fccce00028a4bc2c6146c00011b0000
  | 24 => 0x1858de248080000000000002414aa6a714c9800000000000021d55ba0000000001d9400000004699bc00054323603b0f520000000000000000000000000047e82d0000875000000000000000019d5846000471000000000037280000000000000000000fea
  | 25 => 0x1eaa8d96ba00005628d70002bbc000c306328000c6490a470a1d45c4d1140c80000007eb00000000000007d80000000fab00000000008ab5820000e8477e0003095b840005a080011a2000000000000098b00021d46486970002d7c93a0007e300012c4287
  | 26 => 0x46c0a9800000000000000008850000000000145692ac011b491978da555af800047b0c81334c260f3b08c000000385a360000000499befd8acc2a00000011b0c230000af5422e6080631642c49b10003b098460005fea33510a5e400000013580000000001ae0000
  | 27 => 0x4772365f58f7c46b8314000c235428f8d7b4fcd00030980000000002385846c2e276137939656a5dd30916f087d46c0000ec600019d2d618dc8d66130000a3000030000000000000140000000000402800000070246ab584b9400000021d80008d746a8000000c26
  | 28 => 0x518fb4000c74000000000000000000000000000000000000cc9611b864400d5f41fad6029a000000000000000000014010ea8e627bb0902ea42058da35520a0000000000d2000047c24651bc00043a8001fc600005f2360000ccf0003689396abf45a23a1008c29
  | 29 => 0x18d0ec584600000000000000000003ed585899e00000014f800000032d562a8df4dd800000083500023840000004710000b46c24611b7fd1ac0003082380fe4c236148b4c000c230000001fd20004842c1ddfcc2317800002100000002a84000000000324d442000
  | 30 => 0x68f800079adeb49d9dd51ca23273cb0900008343f58f99e0c000588b0b1906c23647aed12d0c2e6123234000c242d90001ad00000000c99eb000000000018d25ae00000014360000000001f20000393800000000000021d4be08db56e800201c0000002c9deca8d7
  | 31 => 0x25a0000001021544000000080477297810ea0000000000000000694185000000000000000009ac818b0f189ac236950d4df9a7837051fb536c7710318000000c8b0000000000000472a438000c2363aa47c00000000019e963c91b000308c3023d80000c3c000000
  | _ => 0
def slotCodeData2_ : Nat → Nat
  | 0 => 0x43a80000008b0000000000000074800000008e04c03d5c29c2456329c91ad8d3846cb08cd010211c180011c285161215f0a228e800027b9854e9a611aa091a80004758000000c2400006280000000000000000b114f8a9b1c260000000000a188d47cd86480006cc
  | 1 => 0x1846f62616308c00000000000010eac2462480010ea000000194400000034e80000004d000000000008da0000cfc00000051f80000000000002fbd626a6346c21d43dc0000000000186d83611a3655a08e462e3fe98462370000001b0c7f7
  | 2 => 0x1fac0008d500016d096ec7f00000000000000002374e6eb5e00000000008e16da9985d888584e10f400000000000001ecc91c61199740000000000000000c2500024b0fda73353c942da080002d9a9690ea8d4000000200cb7c00039ec8909e80000000000000
  | 3 => 0x75f8000e020000000000000c2900000000000006b9a46c0000000002a2000083f48015757300003c6bf1cede0000002264000d0d63e0109daef58611b0951b283f00000000000000002425b940004f000000003cb2498000000000527250800047e621a36c2bcc23
  | 4 => 0x4c00e1cfd68dd46e21d5906cc86130919b52ab300030f0fdcec064e1cc4c4e8d53e730a9d68c235bc8000000e9c72ca02800000000000000000000de800000000000030900000000001fb0000587000000000000000000011c60000000001364000
  | 5 => 0x574bbe8000cff0003e200000000000001eaa00041c000000097e00000018467d06a8931d1bc00000000011ac358740b70c000000000054d07f02400021ed8f2a3146bb2acba20000000000000b7300034340000a60c7b684000efb00031e9b9800000021d570e000
  | 6 => 0x309c0000004b6ac0800000046e800000000000023e8000c2376f000090200005c8000d0a0000000001a2cc230002c340008754f33f358468da000000122cb7100d198df02e541689c84000db80000000be4b1b000243584695800023ac000ce200028bd0aa000
  | 7 => 0x3e2c000a8861539290eac3000000001c0000611b098c060006111a88000c620000001a26eda047bf08000ba9000000161c00022f00000000007a9a09c8f88cd47a000030c0000003000000c4500023552905625c7236c99a2601bc00000000000001990000000
  | 8 => 0x7872381f420b169f239000065600027bd0ea00000017951b600053d00000010297353b18000000573a39d1be7ed000000185800000030cd856000000000000000000000011f06332c823f40008db0002a20000c140000001deeb7a00000017727817be235126cd9f
  | 9 => 0x8da4912fe00000000000000000000365000195600061380018460005b18000bbcbd9000093400029e6358000000000000000000000061c3e340000002220000000000000058c22e403749308c0008e00003eed1b20000000000000c800000000000000
  | 10 => 0x46b80019723f246c00000000000001bbc00017e00033352d0e8200027d8000b0500000000000004b60001a38c23000000000000000001558be8755cd0ced21e7357f080018bef790000001c5a00000000011ac8270001cb800000000000000000006fa2104000f50
  | 11 => 0x43a8000aaa1b00003b8584e0000000000fe000024e1cac000000766000184e0006322f740000004e2000000000046c3acc0008750afb9ec000000000000000000000018200000000002a291b400046bbca1b26c23588b111d0c000759a7340000000000000000000
  | 12 => 0x1ca15108d61f11fb18460006fc274d1aec2a7d4245d26855400020753641650000000000b7f00000015100002df238c0008d431e2ad9d36000000000000000080ca355364ad8594201584687561a405d3f65ff46c2351fce0000003329510fc7
  | 13 => 0x4af000000000000000002068d77e4800000000000028440006ff00000011a8307583800184e8757502be91bc7766dc800000000046c000137e0005a5236c0008e10fe80000000004048001dfac5a0000000160a8800030b40000000b9236427a3c10000000000000
  | 14 => 0x27c800072600000000000000000000001dfcc316118001846c240418b080008d737a23506a80007f7308d1bec2558da580fd800000000018580a84fb2ac5e348dd08dae1c00000056d800000000000038640000000000000000000
  | 15 => 0x1b31f472000046a80000000001cc00000000000000000000f5c62a270c4c4c2343aa975d12c4e1f9bc2e01cc23340b52400000046a8000000c3c20223518c08fc53f000110a8754d93349846d570e2ad05672c7a614293d1b28d7517a359858d896288a6d84e000
  | 16 => 0x4c612c800015700030f4000000494308d7c246d6b7a350000e871c12359a4c8e546c3bb91aaa4534f0000000b6333700000009340004060000e21475be0deb877954222551aa1527191fc9558d107f30000000000601a36c000ca83f5a358000c231f080011ae012
  | 17 => 0x44687a40008ae61817240000094bba0fc00000043a80011ae0006682679126ea26143e6963602e307bd051d687b000302d25279f7ffb21c00000058d80000000003f600002e2a8809ba0151b846560b8571a1a22856ca4d4fdec2c33f30b1a988d40002741ffe973
  | 18 => 0x617b08d5b68de6332f950eaf5c0000000000daa0003bfd1d46bd00024c4656a9900000000000000000002064eec784beed2100004420000000000000308c2ccf770002e9c402a410002755796c2372d1fada1e0007d3a3598460000000ac98460006d680012eaf91
  | 19 => 0x43a909c000ca53f5800151400046a0000000c900000000000875000000000091e000000000000000000000000000003dc8000bef0003891046000611bef93322a500000018520006e23154000af900030b0000fcd646308c608000000000000013a0000000000000
  | 20 => 0x184a0000003a2c07400000030ac00094448a125800000043aa3750ea00000020c8000000000000000000000030d18480003ef000000000068900004980003cb80000000006a0b0b4000000000000000000000000000008dd7e2a3600f64b011d0134000dd0
  | 21 => 0x33c80010eaab558da361036846000000000000000000013000004d681a5846c2c46fb0d90ea9123e4a6d96760003f6000205a000000000043e7eb0000000000000548b5a400000012e3b2201600042a3755ad6d300000000000a0d4a6000000000043a80004a6000
  | 22 => 0x46c8001854000000308cf0e84c0002b3d55cc4d45d3de91c600000000000000000de1b8400000000023050e60001cb8000000b0e000000185200000000000004ff00021d585631b71b308d0ac87546a2c8596c83d5440000000bf17f0be5d85c7ec0003090000000
  | 23 => 0x3d2800184696964940c4000000611b93800000046a800203e8f10002af400000000000014569b200000000000007c38000000000187000184700600030900008d86860001078c57000308c0000fe0002d8d85200011180000000000000001cd8c3a4870000000000
  | 24 => 0x4e12375848c725c913958124f14ca80010180000002ce90eaa9361680018460000000001818fda0002439554000000039c000000000000150400043a800202400006b2388000000000000000087500013a18843ec0000000000c9f6118001eae000770a374000000
  | 25 => 0x14d017a0006118000e8e00000000018460000002abc000c2b00037091b80000002e4400000046a93f40008e5000000000000000023e80000000002ad40009b800039e184658a46e171d37ca8861180000000003c8bff51c200000000000000000003064f4e000
  | 26 => 0x80f29b06fc875614834800058246fbe0993a2390000000f120000000000000000000109827800068c24240000000000000000c9c00014640000000002370000b110000000000c8300000000000000002e8c00000000023718867530922d858c48e500000010ea000
  | 27 => 0x61223a9c768d81c400000008753d621d400000000036050ea000000000150aff7000238000000000028e1ebec9300021d400092f6118000000000000079176a00075120914dabc543aa38186a7ed648000184c000000000162200000000011c0cb947cbbc1594c3f
  | 28 => 0x1864c230000000f5c000000000000089a43a800166200059eb465af00006e306e53fac5749928716728e000000000008e3701b08c3485830002b759d60000001a60000000000134dd74b4f49c0001a1cd670003c41ce000000031f800000000000000005ea
  | 29 => 0x49bb6d80008d400004280000002c037a00009b446a04fd84a8d96200001846000000000000000000000011da8e2000000192e0006143e6800067731b2a6c97c000000293984cc610000000de6ee21c88000000cfa611bf440000002841ce40000000000001eae83f
  | 30 => 0x61180000000006f000011d80006c922c80003f94ce235044ee94000000185c42346b23791aa00057e2d9dce8e8800000000000000000001e7301646d800000000078e800000000046b8000fec0001051e303108d700020b88dc4b9000000000000047230d5ed4000
  | 31 => 0x184a075000237986400046c23d5ac68f773330d9876c8161180000008d7000210dbfa9f30000000000c23000000000000061880000000000002d25f62b4a61cb6e49f40000001c500007be6118000000f744c031e5fb2c2647aa35dfe6d230cf800184662d
  | _ => 0
def slotCodeData3_ : Nat → Nat
  | 0 => 0x2f13651a48c39436236c000c236b90001f3cd7c0000000000000614b08c000c2361200010e0761000000000000031730990bc01b00030f8000d0c46b00000000002ac00000000003e0000000000000000000000000000df40000005b000000000000000000000c27
  | 1 => 0xf80000000000685a1d400022b49d37fc000a7300032a1bccc5d1e00000000c7b2bb26ac71c0864768001016000656b1b800102b0000000000000000000000000000000018460000003ff80000000001ae800087900030b000090e5f9a111846c812e32450fe2964
  | 2 => 0xfd688543a8000000000250000039600000000000005140003e6d1b25992d781e000000000016854de8430000001da49f300000014a20004cc1fbd16cc232cd3369c5687500000000007360000000000000806a7708c4c234fa22d525a497000307000062b
  | 3 => 0x6128001ee4e3e0000000000189611917cae4000000000187c000000068800102400000000008514e7308ca78b62629000000000000023650ea0003c5a371846f3f000235c00090e3f5b3500000004c2b1551d2c2c0001da40000005908000000b8c2ff308c000000
  | 4 => 0x64467c00056680018460000000001866f1e46b9c4d84a01643a8481856c270000159e1400047080015b800000027b188c000000235d84ee203599ec9e08a00440a36c00000000000000000001eb8000000ad04722ebc00000040fb45c560bab0003c050eafcd
  | 5 => 0x5410000000c37476800121c00000021d48c88b95fd8000c408750000000000000000000184c0000000000000000000000000012b00013a4f6c0000003095210000497a400000a3a000000000000000027f532e8750001b750ea00000019d800000055d1c24000d08
  | 6 => 0x308d6020dd000237c00000000025b19107d332319791bcc2045e405d1bc0003278000f8e00000000011b80000000000000000000191c0000006e0800184600004e800184627334b0000000c2745880011b20000a88000000b87624a36184654f0000000000875
  | 7 => 0x5ac308cc388de00000010bcc7e611a3a11c2f694c0235971200061c042d1b60000000001c0a00063980000000006bb8000000e374b20000000dd900000018460000002fdd9d2c2300000000008755a2800184877700000000000000000000000f9a79e80000009b2
  | 8 => 0x46a0000f1400002888193008db00000000000007a2af6800000046a00011babbb698800000074e00000000000000002754000b1b00020fc00000036b800092491b6a53a3400000046b8000632f0538d900477ea3b77500000000006250001ea6000
  | 9 => 0x36c800000000036e15100000590000000000611800000000000000011b6e780000001920212490800000091800000016ea000000354da420000000000000adb46b406000084546c80019dee83000000184e000000405400048800023500003570003f34502adc
  | 10 => 0xd62069d740004870001ade9930003011ad40000002600000d90000000000000000000018544bf000000153c7a90003f553fc8d459180005b8c404cc3e1170e7f60000cf51b4000611892cfdcc2543aabcd6ae0000a821d520902043a9a11640c280001fecf62d64
  | 11 => 0x201000000000000018fa00000000000001f171d245000073e00000011b60000002d6000000000023851be000000000000000000000000000000000000000000000033400000047380006940000001fb9b6e0000000b68d420000002eb9a4a00061a151cf6a7eb
  | 12 => 0x35591da00046a00010ea0000003afc00000000000000000000000001ec2aae43a80011c0a883fd19fc0007eb43a000000096d000308c0000004323488c7c56b47c28291ac0000000000000000000118c76c00000038c1390c23000000000000046a0000000000
  | 13 => 0x5cc000000613ad200000007cc00000000000001c380000000003c590ea00000007511ba0006138f297ee875000000000090243ab9a87868f10ac23ade6c8f150aa355f44dd700026c95246c9000314cbbaa2928d0ba80008e90423fd9ac60007b7b6b184aaaf
  | 14 => 0x3f6308c000c71000037c000000000275c000a88000000000000000000011dad0a1d68001924ce000000000007eb583800100e00000000006ac0007d139ac000e1e43a800000091b0000929f70f0f000288848e00041213d534ac88613a350000000000000107e000
  | 15 => 0x8221010b200000017ad76c00000000015620000000001846cc74ef2cd954493e015aacd2ee858019b0b48f068343a9fac0000000cd2e400000005c3b8c46c6eb10000001ace0004c0238069a92a0002ad584e0004749768000000702000000000043a8000ae2000
  | 16 => 0x623e84de20f2644b08d1a8000704ab78feab7f000000165e00046a39fd2b26ea565ab757aab152bd9a81cf8fa06242c3ddb0a88368290000061577fa1d4fe2c6a498913507aca162f365d3ba991250b2593924a65b421d5edc875474b0a91aa57800030b5394b8b
  | 17 => 0x8d85440001022c2c00000010ea00043aac480008d4611b08c8f694f48fa8602bac2300000004aa46746dab4cda48b0238b440fa800059821d56247fb43ab2057f890e48780000006fe46a23fdc52c8046dabc51ba000000300c000add46b0001846000
  | 18 => 0x15afca0000000000a8f000000185e8e200030b5d6a83f7e7b4754d60003eca36800000000005b851ed1a43a80000000000002055510000563bbcc0008db06a09c0830ae000000011aa23e000308c0005b8000000000041b000000000000000021d584c000
  | 19 => 0x48000015a28d5000000000000000000000008da033246800000000001dda52a8447f4078000c4600000011b483f5e5126dd6a8de48bb121f30dff2983a380003662de1310000fa537c80000000000000000000000000186d4648db6e1a3691c8c446de800035e000
  | 20 => 0x46c32a51a8c236922f09cf400068a0000c4c0000000001300d00637a6a5bf47c60000000b86ab570a0001874f9261680012364c8259a0c0fd680a4c01c59c26c27556b220000000766267d8d40000000f8000000031180000000000000000000000405a35c3d4c3d
  | 21 => 0x75b37751aa00046da02d1dc0000002a200000004a6800000025e000000000000061800000000005a7202584687500000010eaace0001c7893287a586b01d1aad950003ad4000000000000000000000000002320003fa38880000000002a38320000000074c3a2000
  | 22 => 0x11ac00000013d000000000026011d00000000000000c2309c000000000000000005f0c3100000000000004808000fd61a1374bd6ca4e0a562815f50ea00051100000000006c419a187e000000000000000000021d50ea9506133ad4000c6600017b1938a4e
  | 23 => 0x61180000000000000000000c23000000000000000000010ea0000001fb984ca08163b0b00009fc615036800000000019b0fdc000618b4f421ed8d00000000008e7000308c0000000000001ff2c2300000000000000003965ef000049600000000000b6b0a50eaf5e
  | 24 => 0x7f52b722800000002772c59c62c236e60000020000339b0a800000054f308c000ffc00000011cb00600033cc00000000000010ea00000000011cc7fa478a351956e1425721d50fcc406148000fda0000000000000c2343423557d87327d1bc003ae2b3
  | 25 => 0x1870002371a8000000021d4962e8c62bb7453e60006350001518967611b090d9c00067f00012741313fa2600000000000000000000046c000173c5a70002989932d2600007fc34e0006a38000000970471800000000000580000000000002370000000
  | 26 => 0x1ffcd820002a1000105a87548708818460005ff0000578a7a0000000000ad7629bb7584ca697ae344d1b6ed77cf98a1d9c10d2e7308c0000000000001edeedd611800203400000026a80007f080003d4000000000000000000000022dc0000000001540000916
  | 27 => 0x5f801f800028b7f7a35800000047aa3618e00000000cc139e00000036e4352d2400022897282a2611b6e58fcc270fa959c0000000000000000b7700000017dc6c200000000008a97f928d98467e1471be6d1cac2315d000000000000000000000000000000000000
  | 28 => 0x4d923818480e96a92df50ea04b61d80018c68da0000001b728d80003e9184600043a8f3003e000000000000000000029b0748ce01cf00012780006169aa9f545066e1bcc1e6400046d80019fe00000028c400000000015c000000018e28550504cc0002371e0e922
  | 29 => 0x17780004732360000f4a79b236dee200010c346400000046e000129200000000000008d8569000000000000000007d2f5c32a800000000043a80010429874288000000000000000000000000023b80000000232360000e656119a34000b574bf18614a48db
  | 30 => 0x6fc3264000000000026184632542980014d440d75e210d23a9f30003e19eb6a230001a8d0d41f30002378000e7c43f80000007c87b580018520000003b9400000000000003b400000000011b6c63000000000000055a24d9d8e0000000dc186cc0068e0000984000
  | 31 => 0x7913f0dd8a00000034b9bc675d429a0100000e100021d5e78edc7fea1d46168de6130000c1a8de0003694eb0c260000001902b988150ff51bc000000000000000040c00010ea000191a6ac0000004fa2371c7e00000022890527eb0000000000f9e00003b8000000
  | _ => 0
def slotCodeData4_ : Nat → Nat
  | 0 => 0xdd800175200068a0000fd80000003255200000753bd288fa05a61630dd884000470b20c00000062fa39486e03c5a40000000000318bb81940000000000000000046c000000061a7eeae19850c230002c30000bb7000315480ca716bfb0859342f476480019a4000
  | 1 => 0x30d1bae0000001720e5a0003832139212980691b54d026000613000000000006e22ac0004c90002ac4000000724235d4ea00000023d91e20000001b210ea7dc46ba3b91b80002ee32442990306d88f1400000067e265000000070d800001eabc0002f9d65e4f8
  | 2 => 0x26eb0b9a9ec5f00000002ee00000000018fe0005c10000000eaf5728001256a800002cd974cca800000000000006c13cdc0002693f600015460000000000000000298800184600000030b06ea000000000145a000000000000000055580011c0f9a
  | 3 => 0x32f0366000000000121a0003f5bdec000c5843a80018cceef0000000000c2354900000000000000000ab4f0225190b4000000000000100e000000000000000000031a51b0ffa611800000000000024b562487546eafd186e1c757921d4228c694998000000000
  | 4 => 0x5979429882eae13d82418243770000000000add42aa4cc0000000458000000c2300006112fe122585237c8aa000612a371eda00035d8000000f99000000122800025280000000000003d21f269070002a798ee00000000012747ec0153759f340005718000000f60
  | 5 => 0xe9401880000010096118001a42b4b00000000301ab00000012500007143094000d200002f70086f464753920518bb8000249c0009212911bf4000244234b0b11bc00000000011f6b1164db08c094a850000001f9a90e68aa05d930c244028ad520e992
  | 6 => 0x54321d51b0c1d613a39000100200721d54be5600002db9fa400000000000000006438000000c2354530951b28f3000000000003800000000008754a08000be6c7c000397800082f6f7239c7a4c1f46ebfa17ecc2309ca1d570e0005ae000000000033c0000000000
  | 7 => 0x7c20598dcadd00000000000000000001f1e00058f0ec800000000000000000000002b38000347000222c000a885440001e10bed0000000000cfe615af3d85c8053a0ab441e887500037fd1dafee00000000001fa000000000000000000010eaa0443ab08cb7a91f
  | 8 => 0x297800077c00030b0000000000000203c000000000041000000000011e28d76122ece05cc2568200016428bf5dfb1d80000000001e700006de69a2c2000000000021d40000005c3b2551ac00000030d80cae0b4cf8729a7653248b246c8ecc320003a1c000000
  | 9 => 0x46b2390204000000308c72c0530000000000000000216c00009300031815ba000000000127600034a8bd5a56bb17a63ff00000000000000000000662a4a9fd8d9100003fd33c0000002d35eb800000026d80008e17bbaa211ae31e00000011c00005ca8b90000000
  | 10 => 0x43aa8458460000248000c0c00000023600000000000000000cd100000000000005cfa1d5ec893c04080018460006ae0001a7473c1eea8810eaf3c46a36cc00048d361800000083e54408859e400000000000002970003fe000100500023800000000003c851b006c
  | 11 => 0x482b18425c44900002a4000000623a4f59a274f1b021f1ff600059000000000000002404000ec276894911fa0ae000000000000000027803b20006a13b8508af5c776bda10ea000012be3c000395752308d0ea87575019b42f2c2301320fd0ea81846ab139152bdb
  | 12 => 0x18aa000000308c000af854b236dbda000078b110d3600046a308c00000043abae40000000002354000c2c00036008248d85003b893600000003ad47320000000000000aa700000000000005970000000a883f90000000bb565787740009cf46c308d85837c
  | 13 => 0x10958529193f7aa616d0593356acad6a800000030e40008e447000000000004758000000000546ac6d8623d55d114559188db00015583cab1b000000132800049b96c5960d36784a48d9b803f4131fad8d2099000213c0ec00075a80000000006118000000000
  | 14 => 0x575000000041f427b0b01d68d916536100000000000001210c246118000000fa30000001b8826665592a1b748e500000018468fc00000000000000003f31b06c9100016500000006159ae5a8a30000000014628a146a324548ec3400032100001e84d92410738c25
  | 15 => 0x612000120e0007aa0000000cef8142c5531c6b146a2e211b2f23000000161e8d561205bc00000000000011f49bc611afd98465d4487240884880347b81817cc0000003de98e60000000000000d4b000018546c00000000000000000000001f2a00000026c0000000
  | 16 => 0x63f9c3c4c2000000235c0000000e82d81510b6b4728085c7adb42baa1d54ee94263123d09c4a8b0000f240000004beaf79d149a9214340c000000000000184600056f9c8c000f63425000000000000021d44d80000002360000f2b0002ed82ce21546cb09536c000
  | 17 => 0x6eb00000008d46770001622e43000235d4daf5163d8000000a5f24800000000005a4800000000076b2485bdc8e5611b9100008f9444a350cc0cbd46f0001602c2300024d185208c00010c000091c611800000000069035680002cb0000000000c236118000000a88
  | 18 => 0x4ca07050eac96000000000098046a80000000000000001a000003d580000008ad000000189c4d84798a700000000000001fde8db5698000c820002ed800121a00051891651bce344472e4d2b80004b1a9acdb894070abcec47e8d7215a2790ea0000000000c80f9e
  | 19 => 0x5b1b09586ac2f61424412740000000001f38000000244c000bc000000019bc8d40000000000000000000000080800000000000007ae00000000004eea1d4a940006be80015c88d446d00000008c946d80000000000001fadbf600045b39200008752880ccd7bca71
  | 20 => 0x1854e1f02e29240008dc491a0ad7a8f5c30fa3948f400000000000000000003de02aa00000000011aae2c46baac98465640000000000c24000235000000061180011aad9c6560000000a813980000000000000308d56efba55eb2cd8ca8df
  | 21 => 0xab100000000009b66118000000d290000f1deba9eb000236c00000000030a0000c2a3a6b08dcb07ec0002ac000000046d0000000000000000000000000000000000004c9150000087519a000000000000000019ba000000308c0000000000000000000
  | 22 => 0x1dbe000487409d8583f40000001f30000653a20ca727956f30c1400000000000000000003d800000000007251be9364000000000000000068280000008dc000000000096600015a00000007538000000000000000184600000000002f800000037f80008db
  | 23 => 0x74bbd285a0a440000000000c7000040a400097b56a0fc4000000000000000068e0000000000a883fc0000f00875000000000097900021d5842fa40002f39a56b076dca36d5100000000000000c39000000000096b00023680000007db8000a4c0000000001e58fd8
  | 24 => 0x2e0927a7940002fe50ea0000a2308deb8000000269c000b573f5b14d36025065523f050490362b80000008da305000000000000014b5d7c0000000000000000000000184c0000003abc0000007b800000000000002f1800000000028e00000000000000000000
  | 25 => 0x33bc00000056ea0fd84646b46ea1c0000c257cf8000fd80000660001e320b743a800144e0000000001d2ac2300026c80000005b68000a56e91703b2898508dc458309c000c2357b00000000800002d780000003a325800008db6fa232da2698046ca4c525a000
  | 26 => 0x46ebf780008d60003105846f783ddb0ad1c4fe26389c31940000612800184a8dd611800000000046c3de877c2b6000401000087547e308c000b1b0000000c1c8750000000000fc900000013860004740000000cb100000000000005e480000000000000000f84000
  | 27 => 0x613b08c254937000000000001e6f780002908e07ccaecdcd80003e7b22c76600000030a118c87500000011c000074a0000000c230000000000c2c00000000002c00003170000c25000000000000000000014f6000000000126800069b80018788d70883a85ef4c23
  | 28 => 0x7a50890000000637b08d8580000000000000b532cb80000000001758000000c3400034800008574d021d5e66c230003d715148ac62380011ac0000000000000b501f230f400000046a23556088754fb976400000080b8000000d3300021d426a8d619ca6c9368983
  | 29 => 0x1782e385913094d261990bdad1937ac9e0002944000000000000000009b0003091856294612270c000a8861cb95c000000000000000087546c0000000f547560000000f3a00023ac0000000002f7c00000000000012fa8d84689fad20e231
  | 30 => 0x434b0950ea000623b0c40000000001fb585000069fb90932e000000000063e0007f391755e6000000039000000000380000000000000000000ba700023a50cafed62eb35d2ec80159e3108178e8943aa825b94e1371926c91b87eb5fc0000000000
  | 31 => 0x2c9fb046c000162b0b4000d3661ca1a88949d900000000000000003b195a6000406308d07e00009680011b08ff7ee3d9d0eabe9194a3ed8460002618000000e1058cac6d1560000001fac0002c40001ee8000f9f000235874e8d55a52b743ec0000001fc8000000
  | _ => 0
def slotCodeData5_ : Nat → Nat
  | 0 => 0x72e8000000c230001910000ae9000000178200000034d51ccb114d909d532c83d608000202000046abd60000c2349280013660007a012d4772801000230d4ea0000000000df093c6993048438d365ec3090250b376580000000c89000235c422a0277021d4000000
  | 1 => 0x73b30c19cb02505037ed84ad85619236dcecc507d8bfb50e4c42681a6005faca446a37dd84600066fa9fc000000000308c292000000204400000000000000000002c0c0c11cc0000002360688b1b14e800178e000000000000000000000013340000000000000000
  | 2 => 0x2964000000466000130400000000017a600000000000000000000000fd88e146c23bc000000000002036c0000000001b26000000000000000000000000000002a582ccfd618264880000000006118001db2000000352000089a2b6aded87ebcd576b6e91c6a8e
  | 3 => 0x46eb95800000000000000008d5000245c00000061180011ac09247d0850000000000000000097276838bd0eacb64980001846b11508a099eb8000000000065a87579f80000000006e990e800000046c0001886c2300000000000006148000000711408abc0000f25
  | 4 => 0x3f5235000000036389a18468756d580000000000002950f728cf20f1ff925a87562b80018500000002eb40004504ea30e84b4a48000308c000a9f0002501c4effc1d7b08c00020f40c000184800000023e00009dd13d00000009cd3f8bf340000000000cb8000622
  | 5 => 0x6de252d202e83000000000000051790700000000000000000c2a000000000000062b08e11c4c38627b701846fae67980000000000002d60c58b2e00000006ba00061180000003060003734000c3b000000000000043aa20d74ac23557a434000000611c0045bc89c
  | 6 => 0x69e00012200000002438000c254c0360585000000000000005ee48590750ea68f46c00011600727ca23580000000000000d140b6000266c2e8000614800133a86e588aa21422dbb0000000c2e8752942b4cbf059240e28cd61a00061b8000000c2300028f0000000
  | 7 => 0x58d80000000006c6b7bd18e000447800000000000000000000005a50000ec000000000013d400061fb08c0006a90e3000135c8ef5d926b9d3600071c00000004ba00022ec00024800022cdec60000002c1c0000000000000000d3f0000000000000
  | 8 => 0x30a5d8800076180000000000001438000a0743a9fac00000048500000008b000029e8048c2300000018a600000000018faef25001119c2c3510448001846da0000250584a2e34912bd18b6ca20000001bcca884db953175400000000000000000001fd0000a53
  | 9 => 0x9f600061c05080000000000000000a8843a82ac000000000000000000000000000008af000000193a9f40000000000000613800165083a442b6540000000000000000000611800121c00000021d4000a170000001db87d75250001364ac606300004e4000
  | 10 => 0x61180000000005c3b6e58ee01c5a42a21866c5946a8000000fc654430f40008e85d031400000000bd00000000004720001848bc700023540000002003678000ccb614b094d8a00031f8000fee7650000001d4c0000000000000b273f6847c0000002818000000000
  | 11 => 0x31d8a20005031064000db958500000000004fe00018f4000000308c00003b70e238000000043aace8edcb2400000000009a343ab3c00008e280b00000000000002d35248ae07208001846c2c0df800000000050b141cff20007d780000000004db0000000000
  | 12 => 0xa02ca000000000038080000fc0003091846000000401dc4ca2681180000be00000000019fa8755ae308c0008756530da8000c7876696951bcb3300000000000000000000001014000000125800000000000000003ec330800000000000004bea8d0000000000000
  | 13 => 0x46a208de3283f7e232f82d4c262a48000000c5168428c599eeb272ac0a80004d104d00011ac0000000e24eac7eb000309d84cdd5748b3900000002dcb08c00000000000000000001c3309139800046a800016a521207864dd9ad1100021d40000004f68000000eb7
  | 14 => 0x46f82e97c4c2f02b9fb41b62cf63f30a91ae00000000000000006158001846c2c61c3bc999a9b23af304de9cc4b583a02dd6491a0000000000e7946a80000000000000000ddcfa7000308c0009b3548a36840a94673f13497e49e900031e4000cb75a1308c00022f
  | 15 => 0x37d532200043aa39c98a92064e8001fec8ec693821564834946d00000000000000000000c2e0000000000c257c4a3658e407f482b1b58460000003095510e1a46f8001b9e000611b1490ea55f0001ca9514cae4da800184600043ab161ab67a60764051d8afe3
  | 16 => 0xf100000008d800022655a05520001fac0000000000001268000000244585ac23105b47c058fe0329b9e9892c2946b370d80c7ee614308d0f0c2343a80000000004beb0a000052904b2cd9076a5c61c3e71eb8d7461621d5c68ee94fab410328b0c7ce80009e0000
  | 17 => 0x3c4cffa93700000000000000000000fe6d010000000d708de5b83b15ba852a4a123640008e046b8001062c2720299a51ae000488a641f36000000184d1b0d7058305d9f34e253f6937c00000073100000006ec00000019ea0007808eb0458000000000000056c
  | 18 => 0x7600000670000612a7d5286e7100030bc0008db000235400088546d21d51c4000000145e02246100000000003a50002c4400000000039c19800000000000000000507b0a19b200000000000000000003c11eb4de10000001014de20003280000c236128000000000
  | 19 => 0x70800000062300000000001b1236c0000003f58001a1000061180000008d71a5a321a9cab047335e8000c3507d80011b00000003215a6484700000011b2c230000001858605000000000098000000011d8d910e1b7d9c4ac850bf86a989e8e064cafad0827ad
  | 20 => 0x35f0000000ca746ca3850ea8db5628000000e8b1379fe121a067620a6691ac000000308c000000000000000000000000000000005e621d400000000029a000000000021211c80000000000000000000000000000000033f000077a00036658468d400036bd174f9e
  | 21 => 0x3600000000c2c2cb0001314ad5239b0a582a00046aa3d11e651d36dbe291c200000000000008d45f20000bf8000711000000000000000000000003e680011ae00046b0000000c7300000013249202db10fd5b800061f313d15200030b21a10808fa0000000000000
  | 22 => 0x17fe87500026211b600000028e08ee8d700030c80000000000000000c2300030dc87000000000019dc000000000131200043a8000fee0000001efd5baf000000a8059adcb5ae000000091f56817d8b9a00000000010ea89d0000000000b65747b08c00090a
  | 23 => 0x5ab3a91b42c6c3f58a68fdc000613a388000abc46d0d911babc860eb08d8aa974704078572c55e60925e8000000000000126000046d23540000000000000000b660000000000000000000128ad0e4950000000aa00003105052000000308c6a48dc4ee0000000000
  | 24 => 0xa271a00018d0c243710001e40c0146a00000008d565e80012f89fc612000155e00000000011da0000000000a82c6c44d00015bac900002a08000c8b00000000007e346c23792b60000003b1c000cfb474000000000027b0000000c245e0b0a9212c23
  | 25 => 0x47200010ea0000001b90000000000000000000000000001da000568000000077300034f800000071e800122400058ec03c000cb10002c7dcfca240000000000000464999984af2946b8001880c9f46b80000000001f38000000000527a188e980000000000000000
  | 26 => 0x46b31b53fccd514c00000000007a1a409fc887548321d400000000039a000000000000019eec2700000000008dd00023dc02e3361849698fe0d1c61c3130e8aec656480000007ec0000001eae8e100000000000000000001c98d4646c0ed0c86c2d
  | 27 => 0x43ab28800000000000000000000000000000aff0003bf0000caa0001810000000473ba0d1247b4000313800096a57c0000bf40000002ca518400000034b8000a6c069a0fc0000000000000000000000000000036b000000189e9b200036900000006aa8000000000
  | 28 => 0x21d59c0df146a308c0007fc00023600008d5000325dd8000043a800000000000021d5bc48dd71e3154000000000000000000000000000000000001fb13c4c293f6b14d8e67575440d3d5a4fa561faa4c0000000000000000c454432c551c47ec5838c0df72ad3
  | 29 => 0x56a00000000000002f08000e5f000071000000000024380007fa43aa1d51ac2d90000001a140000000000000000712ac4419e000000000000000058c308c0000000000000ebeee725c35b5202b1a06c00011bc0000b0000000000000000000000000002840000bc1
  | 30 => 0x180b94cfd803d61332d95100006580000000c6b5c3a36da0c00008f00000000001473f2c00000000030a9ae005247e1c34ca8c6761180018940003850000fe80004c009491bac232411fb1208000000393d5623d33f5afcd1aa44b00021d51a8d1016600000003d9
  | 31 => 0x45f2370b3089a00000000000003583ecd1b600061500011ba00015700005825d87619da1a828d515a000107e57e46dae29bc40000d000011d48e700000000002af000000000000046a8000000d4600000000009310002a1568a84f0000000000000000232963eeba
  | _ => 0
def slotCodeData6_ : Nat → Nat
  | 0 => 0x3d700007eb6e88000000c2314515e51b6a8546a2f918460194750001f3000075d2f0000038f75ab1fc000b4e0000000000000000308c000000567a47c6d000032700000008d400000016120000003290000f9e000101c000000000000000087548e8001e06000
  | 1 => 0x624a1d5eb200000021d51e2fbe1a6000000000000023617e28d800001c000019c00023600005ad5e50000000000683b278000eb538c0699846c23545b0a19ab017131bc2d22a00009a1a48000a1f3f6b6180009893d9a34c000c3a79c8000000000
  | 2 => 0x30651b6f8c698a35000000054188100002f700031400000004103980000000000000000000046ab45c000a11000308c000e04390000000087500036498f8ce146a9238fd6e7900014fc0000000000000d8c000000000000033500000009280006450000000000
  | 3 => 0x48980000007d1471404530e8ee18b80012326f71951b5586683f18eb0a11fc99931480016d4c290000000000000635800000031800000000000004d6a1d4b1cf5c46ba3a80000007bf00000005fd73b800136000000021d546a000416bcd5850c2c3cf3099136a1c
  | 4 => 0x18905e68ee403b1c107ef0102a00018480003f5800193800000000011ba00000000000000000000000000b150001fac000000000000000000043a8001204c2a1db8001f7490563b9358000000759a02c82c00041f800000000000000000006456b0000000098f
  | 5 => 0x18485c21b29add9e60006120000000f0d611800000000046f9fb10b865c0000001df0000585a36d84aa880002019846000611a3880000000002c90000000000086dd9800074bbef00000006d9800000094800000000008d708eb4151d254e4912b498fe000
  | 6 => 0x38a80000000006ea3790000cb061200008c0bc7612b1e00008752bd1d49846c630001a4400000000000001ccc2c3f430a98c2c4d61180000000000003ec00000000000000000000000237c0000000000001f440000000001670000000306400000080d2a68001020
  | 7 => 0x58a800000000057b97b5636b1b0000028fa4000000000000000000023dd1ec00061d2351a980006a22d04da20000003840000000611b08cc74c3f000308c0000003ba000000000044100010ea8e300020fce7400c4d9395400000046f24640000bb0000ea9c2a7eb
  | 8 => 0x29b8000ef96a3a36d204000612000000000000016540007f3634b42c000c2300000000000290002388000000227213dd3c8442e0308c0000006118001b0000064680009d6bee00000001ec0000000000000c3000000000008e35742498000ec603e9c74000000
  | 9 => 0x2485846000000000000000036d2c8130000075a000000000079e80000000000000001846e2d68896240009c2000260935000059a21d5e9a861766308c0009240000000000c08141b9d8000000000080c00000058db1a422ace50002350000cbc48c000000038b
  | 10 => 0xf076ec0000000d4161230acc4ac234fa1595c56000479000184600000006e000012761b0000000000000000098ca8800000011b21214a70908ff0c8e00000000000000000000000c2300027d45b00000000000000c237e612ed9c60003390000000000
  | 11 => 0x77a81140003dc4d8238c49e000000000000000000000019b6bed0003a3400000000000000000000001c6800000048e957107800000000015100003fc8001e10bed613a2310eaa2561180017801804b4b8d408e87520d20fdf90de9000000087aec447c2439622000
  | 12 => 0x41f80000000005ab99080000000000000000000000000000006443a8000000f9946a309527c67012ebbf0000000000155d1a87e646b80000008d800000000001db376b0a4000000000205d1aec05000000158600000000011b88d9763a3d90eac26242b564512a9d
  | 13 => 0x65fb4e47f6875612b141858f9946da548facc230000000000000000000000000031ab4405261be00000000000000000fe1846c2a00000005d83c861523542860000000000000f793a52a08b741fb70d23b125cbb90000000000f9e6162dd05208d449430a8fd8ecb
  | 14 => 0x2b32364000c23000025cc160000001ac907e00000000010eab720000838000d255f4308c00000043a8000000000103b30d846ab100000000008d4570b08c0000001a2804d1c6000477bb6c000c63000000000000000000019fa93d46ba9d8000e7f43a94e9050bc0
  | 15 => 0x4f1b1e5170b19797a02877a8260000000000cc454826bc00093900000000000000003dd50d2b833010000fdcad62c5b08dae2a6f0001fb0000d1e475a60153cdce000000111200000000009e49f543ab08d65a00000000000000006bd0000000865000308d46c000
  | 16 => 0x2364000000000000185c0000002ad4000000000210800000000000014e490f61623a400000000039ccbea5cb3cb2c419c426a5c3a3f5846000615a3b51b4a883f60001846e460000001848000000308c000ecc0000bc8000c2300000015a69262520000000000
  | 17 => 0x3447dc6e763330919f080e687ab8570e00052a0bf10f62c946fa970f04c4c4e92a640e8c4743a800085c90947991e593a23000000000000004c01fb07468e03350001e24fb23f7a0398662f9000261c27c00069630e0000c400000000000c230000000bd28d7
  | 18 => 0x76ca21da36dff65330a91c03e5614ab756dec355153140dac000000050400084561326c800000022b316106c0000003185ab00003d09fac6bc7086b30138000a31000000000090c00000000000002d600011aa0000000000000000514309c0000002a8bf68000bfa
  | 19 => 0x3951846000718175c00096046f28980008d50000000be200000000011b200000018ddbc69825d8800000096100030b81b268c1eb3dd8000c2514a800000088828b00019400000000000fd6c2c000000184ee4b4b28000000b122a6983093c00069e0000000c2f
  | 20 => 0x236400000079e3ca80000000000000000f5f7698000000cb76e4acfce8867b6bbc0500008d400000000008e33558000000ac842aaa2181cd3e49830e5cce00d00000000000002f7800000000000000012083cf5699f9c000c270002601a5a0006142674000454
  | 21 => 0x16d22860002d718680710000001852000716b2291a8332000235c000cc1611bcd00008750000000000c2907b80016b443658a2ff91ae0003f7a33c0008dd57f08a400079b000299c93400000023c51ac67d0003f0cb1a875611800101e0734c029e14f4875
  | 22 => 0x5ae12d91babb16400000000c2361908b4000feb4c3a5f000000000000018488753e6000000000036a30ad86436c0002c6c00085e0000000000ce70002f40000000000235920400032db185d4e0000000000e7a000673309d8865020443091d02e5a4050678000000
  | 23 => 0x73b308cdecc23471bb3d1a8734000000000000000000000000000000000000c23616ad11f8878400006a09230305190bf8180ad500000000008fb6120001abcad343a80000008010000000000c2368fa3580000000000000000000000000000002f56ca3fd510d73
  | 24 => 0x478000151892452800000000000000000000b0e000203000000062400000007fc16b3000f0c0f00000000ac287548309fc00000002429f11e40001329fac000bf90000001dc2000240000000000000021d51ca8d0530b0a1972ff300030e40000002d4a355aa08b3
  | 25 => 0x5d20000154000000237400000000000000008e046a0000000e546fd84a50ea7a30ee0000eaaef82d200000000001cf9fac000000083000000000000030b9b1e0005c28001f400000002bf51ac000000308c000000144000000000000030b0c7200000000002f0000
  | 26 => 0x12a0001848c240002dc80009bc0000000000f446118001510000000000014ec24590315c880d1e000000000051f00023600007eb00038a9a9c00000037dd2343853f58000000000000000000000061500011ba00043aab091bc0000000000000c24177800139e875
  | 27 => 0x1bcb7490eac2343aaa9940a2d200000019801540000001bc40000004048000c2300000003188e76350000000000612800077600061438cc00000000000000000006848000de0000000308d65a8d76253510a9098903500000000000001ebd07e0000002b25914000
  | 28 => 0x277c0000007d900011800002ce1759846e3e0e70d0984aaf6611b1c98526076df2600b98c6b17400d54d4c1000000011aa0000001fac000afa6128001afa0004010000700f6c00030b81c600081326c800000046bac6c000658611800185600000015bc000c25
  | 29 => 0x8a80000000420591505aa157108f9135b178ba09a00002544000e0e0f6194886480446e2380000000613b21000090b4edaa21de4000000320dc4f01a00016ac0000000000bc51c200000020359e8d99000000000000000000001ca7da69e8000000000
  | 30 => 0x6182b4d8f2014403b0a059d0220b210bd698e674d827f52920000002a2000000000000013428dd000000000000059300019927c181726c8fea000611ba9800000000000011fcdd0000000000000009180011aa8d4000000000000000000011e216961e240c000000
  | 31 => 0x19e00011e493f4d8a3808aeeaf0000000000000000000146ccc00003bc405a00000014dc8a4000000000184600000000000008cd00000007f8f5f51e2f25300c2300031e11b60000e4a2f40000000000000000c255b380007f4f265883a39878e777a44051402c29
  | _ => 0
def slotCodeData7_ : Nat → Nat
  | 0 => 0x3249ba06b6000541a35400000062a00014aa82d590248185869447081e8000c2846b284c0008df00023d91ae0003823140000764000000184600047e00016ecc240da8000cf80006c421d4000000765b970000e3f59626258e63a630cbb9a0140001271fb150ae12
  | 1 => 0x6c62b2d1c8ea074722658606ae803800000000000025bc00000046e00011a800000000015ba000000238800000000000000008d6000236ccb40006b0a28c00000000037b00000000001fd9684000366bec99a21b700000016fac236a00000000000000000177a000
  | 2 => 0x1c7241743abf451bcc23611a368a7a0000002e991548d671700011c000069e9f7d77c0003e1b0a000000000040b0fec00055d8000000833104a39c000ccc0003f0000094700000010ea000431bd7c0008d40002380d10e5c23908f558263d
  | 3 => 0x48ab08daec4fe00009e0fd6c5200022440d000044f8000000d620001ee00000001f400010eaae456e8000000c2362a37a984cf0a0002c1d0eed7f0000000000c204840001a4e00009780017eacb90002de52f4875528a36c000000000204c000c23345813cd4e337
  | 4 => 0x46c3c38000000000000000008a6cabe70222a390003218000c2300000001288db000000000000052623540000000003254000000000000000000000020fc000c2c000308d7189a421c8000000e334b59301896c666118d54000e516792390000000
  | 5 => 0x3060000000000000180003443380000000006952bdd84a95d611832d08a0004d90001b168b0120800184c00000023680000007a78000b768ed000000000000061c80000000000003d4d84a7036119fbd84668241cba24000fd34480000fd80000000000000000
  | 6 => 0x10ea8d500023b40000fa000000000000000000015a4e37000000000081400000000000006e514100000004748001b868d600000016c6e4d7e617ec000000000000203400073730b120c0000001a7c000000000000000000000000000000006013e9c000000
  | 7 => 0x46b36e40002e10001da800000000000000008e625e218184600000000011c80007dd0000f7a000558b099b8e82a00000000001360000000e7600075f2de442c000000000184e00000002bc00000046d00000000000000000000c23000308c0008d60000470000000
  | 8 => 0x56600018ee8de7bd38603ee865290000000081e00000012087eb5bf0000000eda5c3b3c5e380003f6000000095400000000000000000000000942206110db7676b3c9bf0583a0005d083e40009ec46a309c0000000000000000000802a3500007f40002371846d36
  | 9 => 0x499800000000077b0001c5e00051c80003308d600000018460000001fac00000075c3564000000000000121466b000308c2b4c5174d000000000007e9ad942400065c27dc0008ce435b2559450033db800124c000000000000000000000000000000000000000c97
  | 10 => 0xf000000000006cc8000550c2375f000000101d0002f11f280000002370000000000000186cc2400000000001320001dc800000000000011ac0000000001a2c000161a5f5022ae348f2f000000007620000000c9a0000001e62b120001d6400000000000000f2c2f
  | 11 => 0x432b0c000000027e308d85206d0002351b7ec2355a0000000a86000000000000000034b585486610f3884000c23000000150a14f6700000000c45654249c2e091b00023580002a90000001890c0a5a0a03c00000010117a00000006ccb1a0e809ec0801f14000c65
  | 12 => 0xe5000000046c2378c2209c3d0000000000046cb3b42b600000026e8000d98000238000000048d8001b22d892c4137112e82c00021d400000000000003be0005492d40ef600000000000008f81dc0001504ca3610b0900009bf3fc80017a41d5000314c000000
  | 13 => 0x18468e5000000000000000000017c600000000000000006f18001276d7e3f58a34000258093000000000061500000001e35a4000000000000000000000006d82a358466d956e8000000000792235101400061c8000f780000002b740001de0002381866000
  | 14 => 0x40830a800000000000000000000002394000dd85699ad0000cf900000011ae85710c8000000d7e46b2508fd68750000000000c230000cb11ce00000000018468755990565e180000000000df6a8743aa6bc000d5400000000000005ac00000008753eb80014dec25
  | 15 => 0x903559bcb991e000402bb64000000788345000000000023fcda68d8124b091e068993cc8000000c5e72c80000009ca18900017360000001ce00000000002ba0000bd74718001c1a26e684000000000044500018460000000798000000613295d8ec311
  | 16 => 0x4d880c80007ca64623bd13425b0000e84000a7c000308d846c6d5019d25846e7667118d1868875245b1d0000c233e20000000ec44e3b214000000000308c000000227ac158468754df917184c00000000000000004e92ee000000024533280000001ef8000000000
  | 17 => 0x3c0800000000040710ea3fe61d80011a87eb0000bd952a0000000834000ab23ea32100010130000000b60c2300030c184600043a80004f80000002c718ec00000021d4000000000338115600000037fc77826d42780011bc00047080015d2c5900000013c28e2
  | 18 => 0x31240000007eda1d400000046d80000000002e9b31800013b0003f34db0c2300024e499e0000001f9000087560f2b9d836000000095c000000000319c00000000031a48e8c23796aae18460002188000000c4900000011b4c4d43a800000058400000000000c9
  | 19 => 0x18468766ae904133600000030ac00000000030b11aec23619313ce440003730000d5efdf00000000008b000000000000000000000b7eb35000000193a0005889fe8500000691116881600058d800000094443ab0900008d500000000000004af800000096a
  | 20 => 0x58d90d1ba4ac44f280000000000001fad846c8275a8000000c36000000000000046c270800000000000000000007e0bc5d5100007b10001c669a60000001e6483f00000000000000000001200c436d1aa2400000000012b400000000000013428de486b5e5fc28d2
  | 21 => 0x46f386d62a0000000000e0ac2300023900000007738000000000614800000065f0000000000c2e00000005ca0000003a780000000000001ca400062c8000000000436114d45c8df2a330e8000000000000000000000000000def5e46f21c0b3ab5b0003aec184a88
  | 22 => 0x46d2a21846ca854896d4000000113310c00000000024380005f90000000000000611a6e40000000002c090ea4d500000000000000000001e4e0000002d9c0008f02c7b0990eac4c0000000000a1e000000036262f46f0000e7ee360cb24880008d500000012725d2
  | 23 => 0x308c000000000000184ef9843a80010eae0554816791c681d6a40000e5e8dd63d308d6a4c2375a99bc19cec100000011c8a770000000000000174a4900004db0003a7800000000001000000006eb80011ae0006903984a7601d43a8000ed8a880000000000000
  | 24 => 0xc230000db40000004ec2214000c2652ca251d3400000004480000007c08000000000000308c000e0600026ec00000047080002c28d5254be6800000000000010ea000000138c0000000002cac0000001fa8001920000000035400000000021d49c0000
  | 25 => 0x143c00053e00021d4000c2300000017382ac0000001e9ac820002c6df4c000000238000000057fa3540000000002669d9800000030940000000000000000146611800185200048600018b8c265ccb08d84664a00023500000007ec000151000000006390ea000
  | 26 => 0x6189d980009b000000000000c18198000ff600000030bd51000000000012000004703e1d1ec9384700000c76c4e56523555c20006dd80000000000000000000027000377d7a239a46d9f7c00095600000000000005a18001c7a0000003ed0190000
  | 27 => 0xb5c00000043a992dc465cf7191fb00008db54280000000003c82b7184619b0000000000f9d000000184e000000000000000077080000006f5000308c11a00071d237d8c86f24d900018460007580160000841000000114e000297a3691ac7d77cc1dfccca000
  | 28 => 0x1b900010eac2700000000000000fc20a125ec293f88eb933c00061180018a487546e279000000000000018e0267389000000000046aa1d598ac23000000106e0000000000000000000000184ad12396068dd308dc4d9042400000068380000000000003d2557c000
  | 29 => 0x1846315747a1d5a3800000030a50eae490001fbdbbc0005668000000f13000000000000065d1a6400087511a800000023300004600008e344eac4587800000024954a0eda00005a15c4ad3000000115efad00000012580005730f19930000691ade4000c23
  | 30 => 0x308d23ac0149d2c8c00018d611b08c000c24611a36d148a5b0c1b8a0000c3446a0000000000656161400000043ab4ad85e0006118001858f5f0313f380000002148a6584ac306bc80000000006169fac000de30002a2832a00000000000008d4612272986e8c5
  | 31 => 0x35200010ea00041d800000000058d8000000c2a00000000008d60000001d3ee5b0003c080000006ba8000000b63683b1540007e04ac2cd4fdc00000000000000006a1a3518a28db43a8000000f9f697bd580000000003099956000000000050a00046cbe38f30000
  | _ => 0
def slotCodeData (i : Nat) : Nat :=
  match i/32 with
  | 0 => slotCodeData0_ (i % 32)
  | 1 => slotCodeData1_ (i % 32)
  | 2 => slotCodeData2_ (i % 32)
  | 3 => slotCodeData3_ (i % 32)
  | 4 => slotCodeData4_ (i % 32)
  | 5 => slotCodeData5_ (i % 32)
  | 6 => slotCodeData6_ (i % 32)
  | 7 => slotCodeData7_ (i % 32)
  | _ => 0
def slotCode (i : Nat) : Nat := (slotCodeData (i/64) >>> (13*(i % 64))) &&& 8191
def recipeData : Nat → Nat
  | 0 => 0x48150401604015038160381503016030150500e0500d0480e0480d0400e0400d0380e0380d0300e0300d0280e0280d0500a050090480a048090400a040090380a038090300a030090280a028090180a0180904805040060400503806038050300603005028060280501806018050100601005050020500104002040010380203801030020300102802028010180201801010020100100802008010200602002
  | 1 => 0x2f01d2f01a2f0162f00e2f00a09029250251f8291f8151f8051a026148251c8252902629025190290f0250f002258252580d258012d8292d81a2d80d2d8050781e0781a078061e02a1e0261e01e1e01a1e0161e00a1e0061e002098062002520006200020c0291882605025050220502104822048210501e0501d0481e0481d0401e0401d0501a050190481a048190401a040190381a03819050160501504816
  | 2 => 0x2200a22006220020e02524829248051a8251a8010a8062102a210261702a17026170221701a170161700e17006170021f0221f01e1f01a1f00a1f0061f005080290802508015198291981a1980d198051b8251402a14026140221401e1401a1401614006140020a02920825208012302a230262301e2301a2300e2300a2300623002108221081e108161080e1080a10802068061d0061d0022f0222f0212f01e
  | 3 => 0xc81e0c81a0c8160c80e0c80a288292880d288051e8250e8021b02a1b0061b002070291d825138221381a1380e1380a06029060252a0262a006160262c8252c80118026128261281e2e8252e8192e8010b0292702a270262701e270162700e2700a2700627002058220581e0581a058160580e0580a260261c0261c0061c0021680511025130251301929825298010b8061581d2202a22026220222201a2200e
  | 4 => 0x770292f0f25f0292f8292f80d6c029738258b0296c8292d92d5e0296a80e6a8022584157015668253a8024d829318223181e3181a318163180a3a00e3a006558294e0252f0aa5782557816578062f11a2f13a7a80e5501a550023b00d3881a5880253825788292d84153029088220881e0881a0880e0880a088061502a150261501a2b8292b8050d8220d81e0d81a0d8160d80e0d8022402a10025120250c822
  | 5 => 0xb300db300ab3006b3005b30021f8fc08040b1825b3816b3806b3802b3801b00252592c2d96cb28251389c229142f1781f0f8178bc198ccb10290f0780c8642894406030af829af826af825af80eaf8020d0680502804824040200381c03018028140180c0100800804000005712d96016580225801a5800a2f0ba660298b8255f825730295e8252f1123582936025390292f0a2798294002a7f025258cd7f825
  | 6 => 0xbfdb1c6e11b5025b8025c8806bc029ba805572b83b1d8af8fa42a14399cc59acc562b07abd483418c802982c1481c0cc1802110882793caf029af025af016af00eaf00524924b0826b0805b0801b302ab3022b301ab3016b300e
  | _ => 0
def recipe (i : Nat) : Nat := (recipeData (i/64) >>> (20*(i % 64))) &&& 1048575
def value : Nat → Nat → Sig
  | 0,i => raw.getD i zero
  | fuel+1,i => if i < 9 then raw.getD i zero else
    let q := recipe (i-9)
    let a := value fuel ((q >>> 2) &&& 511)
    if q &&& 3 = 0 then neg a else
      bin (decide (q &&& 3 = 2)) a (value fuel (q >>> 11))
def retained (mask : Nat) : List Sig → List Wire
  | [] => []
  | a::w => let rest := retained (mask >>> 1) w; if mask &&& 1 = 0 then rest else (a,.tNone) :: rest
def extra : Nat → Nat → List Wire
  | 0,_ => []
  | n+1,z => (value 4 (z &&& 511),.tNone) :: extra n (z >>> 9)
def ns0_Data : Nat → Nat
  | 0 => 0x3ff7bffadffceffe37ff37ff8b
  | _ => 0
def ns0_ (i : Nat) : Nat := (ns0_Data (i/64) >>> (17*(i % 64))) &&& 131071
def ns1_Data : Nat → Nat
  | 0 => 0x399fe68bc7f9a9e7f82a63fb0a92dfc2a3f7f0a575fc2a76ff0accffc2a77ff0a9efea2a54fe8ad47fa2a657d8aa25ee2a696f8a935be2a476f8a59dbe2a6d3f8ace1fe2ab07f8aab9fe2aac7f8aaa9fe2aa87f8aa99fe2aa47f8aa89fe2aa07f8aa79fe2a9c7f8aa69fe2a967f8aa51fe2a907f8aa39fe2a8c7f8aa29fe2a867f8aa11fe2a827f8aa01fe2a7e7f8a9f1fe2a727f8a9b9fe2a5e7f8a971fe2a5a7f8a961fe2a527f8a941fe2a427f8a901fe2a3c7f8a819fe29587f8a3b1fe28e67f8a2f1fe2a76ff8aae9fc66ba7f09
  | 1 => 0x983fa6a54fe9a7abfa6ab37d9a995f66a897b9acebde6a0cf79ad05be6ab56f9a9a5be6a4d6f9a91dbe69676f9aadcfe6a6d3f9ad61fe6b567f9ad49fe6b4e7f9ad21fe6b427f9acf9fe6b387f9acd1fe6aec7f9aac1fe6aae7f9aab1fe6aaa7f9aaa1fe6aa67f9aa91fe6aa27f9aa81fe6a9e7f9aa71fe6a9a7f9aa59fe6a947f9aa41fe6a8e7f9aa31fe6a8a7f9aa19fe6a847f9aa09fe6a807f9a9f9fe6a7c7f9a9c9fe6a6e7f9a979fe6a5c7f9a969fe6a587f9a949fe6a507f9a909fe6a407f9a8f1fe6a067f9a561fe68ec7f9a
  | 2 => 0x395fe2ce37f8b35dfe2cc77f8b2fdfe2cbd7f8b2ddfe2ca37f8b19dfe2f1aff8bb93fe2edaff8b8bbfe2e28ff8b863fe2e06ff8b7f3fe2dceff8b66bfe2d88ff8b5fbfe2d7aff8b57bfe2d58ff8b53bfe2d38ff8b433fe2d02ff8b3b3fe2ce6ff8b363fe2cbcff8b25bfe2f31ff8bcbffe2f29ff8bc8ffe2f15ff8bc4ffe2f07ff8bbbffe2ee9ff8bb7ffe2ed1ff8bb37fe2e0bff8b57ffe2d5dff8b30ffe2e79fe1acdfec6a63fb1a82fec6b4b7f1aa4dfc6a4b7f1a8fdfc695d7f1a9dbfc6a7bfa9ad55fa6b4d7e9ad1dfa6b3cfe9a
  | 3 => 0x5a77e2d49df8b4d77e2d27df8b37f7e2cd5df8b8eefe2e25bf8b84efe2dbfbf8b65efe2d77bf8b52efe2d29bf8b819fe2d587f8b3b1fe2ce67f8bcadfe2f217f8bc0dfe2ef97f8bbcdfe2ed97f8b8b5fe2e077f8b815fe2e017f8b7d5fe2de77f8b78dfe2de17f8b775fe2ddb7f8b75dfe2dcd7f8b6cdfe2db17f8b68dfe2d997f8b615fe2d7d7f8b5e5fe2d6b7f8b59dfe2d657f8b575fe2d597f8b55dfe2d557f8b545fe2d4d7f8b4f5fe2d377f8b45dfe2d0f7f8b425fe2cfd7f8b3edfe2cf97f8b3ddfe2cf17f8b3b5fe2ce77f8b
  | 4 => 0x70ffa2daffe8b6affa2d9ffe8b63ffa2d81fe8b5bffa2d63fe8b50ffa2d2dfe8b477fa2d1bfe8b3bffa2cdbfe8b337fa2cc9fe8b317fa2e33fd8b827f62dc5fd8b6d7f62d91fd8b4bff62d21fd8b33ff62e35fb8b877ee2e0bfb8b71fee2db7fb8b64fee2d71fb8b4c7ee2d23fb8b87fde2e0df78b727de2db9f78b5cfde2d45f78b497de2cd1f78b59dbe2e37ef8b8afbe2e21ef8b83fbe2dd5ef8b6efbe2da5ef8b657be2d75ef8b59fbe2d47ef8b4cfbe2cddef8b34fbe2e39df8b88f7e2e11df8b7677e2dcbdf8b6f77e2d9ddf8b
  | 5 => 0xbfbfe6efaff9bbdbfe6eecff9bb93fe6ee0ff9bb6bfe6e2eff9b8a3fe6e18ff9b833fe6e06ff9b7f3fe6df6ff9b7abfe6dd0ff9b73bfe6d9aff9b623fe6d7eff9b5ebfe6d5eff9b563fe6d4eff9b4fbfe6d38ff9b433fe6d06ff9b40bfe6cecff9b3a3fe6ce6ff9b363fe6cc0ff9b2f3fe6c96ff9b0cbfe6d5d7f0bc77fc2f09ff0bbf7fc2e1bff0b7fffc2df9ff0b707fc2dadff0b637fc2d6dff0b577fc2d41ff0b4affc2d1fff0b467fc2ce9ff0b32ffc2cc3ff0bc97fa2f1ffe8bc37fa2efffe8b8c7fa2dfbfe8b7affa2de5fe8b
  | 6 => 0x85dfe6e157f9b81dfe6e057f9b80dfe6e017f9b7d5fe6df37f9b7c5fe6ded7f9b7a5fe6de77f9b78dfe6de17f9b775fe6ddb7f9b75dfe6dcd7f9b6cdfe6db17f9b6a5fe6da77f9b68dfe6d997f9b62dfe6d857f9b5f5fe6d797f9b5adfe6d677f9b595fe6d617f9b575fe6d597f9b55dfe6d557f9b54dfe6d517f9b535fe6d3d7f9b4ddfe6d177f9b43dfe6d097f9b3f5fe6cfb7f9b3e5fe6cf77f9b3c5fe6ced7f9b39dfe6ce57f9b38dfe6ce17f9b35dfe6cc77f9b2fdfe6cbd7f9b2ddfe6ca37f9b19dfe6c4f7f9bc6bfe6f00ff9b
  | 7 => 0x5cfde6d45f79b497de6cd1f79b59dbe6e37ef9b8afbe6e21ef9b83fbe6dd5ef9b6efbe6da5ef9b657be6d75ef9b59fbe6d47ef9b4cfbe6cddef9b34fbe6e39df9b88f7e6e11df9b7677e6dcbdf9b6f77e6d9ddf9b5a77e6d49df9b4d77e6d27df9b37f7e6cd5df9b8eefe6e25bf9b84efe6dbfbf9b65efe6d77bf9b52efe6d29bf9bbb1fe6e067f9b561fe6cec7f9b399fe6f2b7f9bc85fe6f197f9bc5dfe6f117f9bc3dfe6f0b7f9bc25fe6f037f9bbe5fe6ef57f9bbcdfe6ef17f9bbb5fe6eeb7f9bb9dfe6edf7f9bb65fe6e2d7f9b
  | 8 => 0xc97fa6f1ffe9bc37fa6efffe9bbc7fa6ee3fe9bb77fa6edbfe9bb5ffa6ed5fe9bb4ffa6e31fe9b89ffa6e03fe9b7effa6deffe9b7affa6de9fe9b797fa6dc3fe9b6bffa6dabfe9b67ffa6d8ffe9b61ffa6d81fe9b5bffa6d63fe9b54ffa6d43fe9b4b7fa6d1dfe9b46ffa6cfffe9b3c7fa6ceffe9b387fa6cdbfe9b337fa6cc9fe9b317fa6c4ffe9b8cff66e09fd9b717f66db5fd9b647f66d2ffd9b487f66ccffd9b8d7ee6e1dfb9b82fee6dc7fb9b6dfee6d93fb9b5c7ee6d31fb9b48fee6e0cf79b87fde6e0df79b727de6db9f79b
  | 9 => 0xf7fe303bff8c0e7fe3037ff8c0d7fe3033ff8c0c7fe302fff8c0b7fe302bff8c0a7fe3027ff8c097fe3023ff8c087fe301fff8c077fe301bff8c067fe3017ff8c82fecad5d7f2b7abfaae0cf7ab59dbeaeec7fab819fead587fab3b1feace67fab82fec6d5d7f1bcb7fc6f2bff1bc9ffc6f1dff1bc27fc6f05ff1bbf7fc6ee1ff1b86ffc6e0bff1b7fffc6df9ff1b77ffc6dd3ff1b707fc6dadff1b687fc6d8dff1b60ffc6d6dff1b57ffc6d5dff1b507fc6d3bff1b4affc6d1fff1b467fc6ce9ff1b32ffc6cc3ff1b0cffc6deafe9b
  | 10 => 0x2f7fe30bbff8c2e7fe30b7ff8c2d7fe30b3ff8c2c7fe30afff8c2b7fe30abff8c2a7fe30a7ff8c297fe30a3ff8c287fe309fff8c277fe309bff8c267fe3097ff8c257fe3093ff8c247fe308fff8c237fe308bff8c227fe3087ff8c217fe3083ff8c207fe307fff8c1f7fe307bff8c1e7fe3077ff8c1d7fe3073ff8c1c7fe306fff8c1b7fe306bff8c1a7fe3067ff8c197fe3063ff8c187fe305fff8c177fe305bff8c167fe3057ff8c157fe3053ff8c147fe304fff8c137fe304bff8c127fe3047ff8c117fe3043ff8c107fe303fff8c
  | 11 => 0x1affe7069ff9c19ffe7065ff9c18ffe7061ff9c17ffe705dff9c16ffe7059ff9c15ffe7055ff9c14ffe7051ff9c13ffe704dff9c12ffe7049ff9c11ffe7045ff9c10ffe7041ff9c0fffe703dff9c0effe7039ff9c0dffe7035ff9c0cffe7031ff9c0bffe702dff9c0affe7029ff9c09ffe7025ff9c08ffe7021ff9c07ffe701dff9c06ffe7019ff9c05ffe7021ff0c0f7fa3019fe8c2f1fe30bd7f8c2ddfe30a37f8c1f5fe30677f8c2f3fe3096ff8cb3ffe32cdff8cb2ffe32c9ff8cb1ffe32c5ff8cb0ffe32c1ff8cafffe32bdff8c
  | 12 => 0xb2efe70bc7f9cb35fe70bd7f9c2ddfe70a37f9c1f5fe70677f9c13dfe72ceff9c2f3fe7096ff9c0cbfe72cfff9cb37fe72cbff9cb27fe72c7ff9cb17fe72c3ff9cb07fe72bfff9caf7fe70bdff9c2effe70b9ff9c2dffe70b5ff9c2cffe70b1ff9c2bffe70adff9c2affe70a9ff9c29ffe70a5ff9c28ffe70a1ff9c27ffe709dff9c26ffe7099ff9c25ffe7095ff9c24ffe7091ff9c23ffe708dff9c22ffe7089ff9c21ffe7085ff9c20ffe7081ff9c1fffe707dff9c1effe7079ff9c1dffe7075ff9c1cffe7071ff9c1bffe706dff9c
  | 13 => 0x2f1fef2bdff2c0cffcb021ff2cafffab04ffeac0f7fab019feacb07f6b2c3fbacb17deb2c7efacb277eb2cbbfac2f1feb2cd7fac2f5feb0b77fac28dfeb07d7fac19dfeb04f7facb3bfeb0bcffac25bfeb032ffacaf7fc7033ff1c087fc72bffe9c13ffa703dfe9c067fa72c1fd9cb0fee72c5f79cb1fbe72c9df9c
  | _ => 0
def ns1_ (i : Nat) : Nat := (ns1_Data (i/64) >>> (26*(i % 64))) &&& 67108863
def ns2_Data : Nat → Nat
  | 0 => 0x9a978bf151c2f17e2a225e2fc5420bc5f8a76178bf14e52f17e29bc5e2fc5338bc5f8a5a178bf14a42f17e29345e2fc524cbc5f8a37978bf146a2f17e2a383eafc54d8bc3f8a8e9787f15122f0fe2a125e1fc537cbc3f8a659787f14bb2f0fe294a5e1fc5250bc3f8a8e8fa7f156f819fe2acd033fc5599587f8ab31d8ff15243b1fe28ec753fc5598e67f8a4318cff15a22f1fe2b305e3fc565cbc7f8ac8978ff15892f1fe2b065e3fc55dcbc7f8aba178ff15682f1fe2acc5e3fc5490967f8a5712cff14aa259fe28e24b3fc518c967f8a3b100ff150c1f1fe290c3e3fc51d87c7f8a258f8ff1476081fe2a3e1ebd0cca95c7e19989d8f6335c571dc66461eb54cc7c3d7a09952b8fc13313b1ec26b8ae3b84c8c3d6a89
  | 1 => 0x3887af514b358dba29661eb7452cc196e8ac9178fd15182f1fa29ea5e3f453c8bc7e8a70978fd14d52f1fa298e5e3f452dcbc7e8a50978fd14962f1fa28cc5e3f45188bc7e8a81878fd15663c5fa2b0c5bbf454c8bc7d8a8c978fb15042f1f629c45e3ec5368bc7d8a64178fb14972f1f629205e3ec519cbc7d8a8d178f7150e2f1ee2a0a5e3dc538cbc7b8a6d978f714c92f1ee29705e3dc5260bc7b8a48978f715332f1de2a1e5e3bc5418bc778a72178ef14dc2f1de29725e3bc5288bc778a49178ef14682f1de2968b3a7c54d0bc6f8a8d978df15152f1be2a205e37c541cbc6f8a75178df14dd2f1be29a45e37c5328bc6f8a5d178df14b32f1be29465e37c5264bc6f8a37178df14692f1be2a063937c5599676f8a
  | 2 => 0x9b1787f351d2f0fe6a245e1fcd424bc3f9a6f9787f34cb2f0fe69765e1fcd294bc3f9a4a1787f3522575f82962aebf052b8ef7e0a5707afc14ae065f82a54107f0561b09fe0a9892df61589087ec2966aeb7852d15d5f0a8e043be151d086fc2a58ae3f852bd5c7f0a3b1d0fe150d2f1fc29c05e3f85318bc7f0a5b178fe14ae2f1fc29405e3f85254bc7f0a47978fe148c2f1fc28e85e3f85194bc7f0a5712cfe1476081fc2accaebf854e95d7f0a572b6fe14ae25dfc295c48bf851d07d7f0a57082fe14ae08dfc28ec10bf8563708ff0a57ab5fe14753a3fc2a764b7f854e096ff0a9892dfe14ae25bfc28c24b7f851d080ff0a57845fe154c083fc2a76107f854ac20ff0a86041fe1486083fc28ec107f8512c20ff0a
  | 3 => 0xb11ccef35332f1de6a1e5e3bcd418bc779a72178ef34dc2f1de69725e3bcd288bc779a49178ef34682f1de6a0c5b3bcd4187c779a830ccef3476091de6ac8b3a7cd2d1674f9ab2ace5f350983abe6aed6337cd58e066f9ab3accdf3563561be6ac67637cd58ce66f9a9a178df351b2f1be6a2a5e37cd440bc6f9a83978df34ea2f1be69ba5e37cd348bc6f9a65178df34ba2f1be69665e37cd28cbc6f9a4c978df346e2f1be68d25e37cd40c726f9abb590bf35648197e6ac8ac2fcd590ec5f9ab21ccbf35352f17e6a385e2fcd444bc5f9a84178bf34ec2f17e69ca5e2fcd378bc5f9a67178bf34b42f17e69485e2fcd268bc5f9a49978bf346f2f17e68d45e2fcd5daca3f9ab2c0c7f3565560fe6aca761fcd594e63f9a
  | 4 => 0x47178fd346d2f1fa68cc5e3f4d190bc7e9a31178fd34f52d9fa69ea3e3f4d3d4667e9a81878fd3576061fa6a060c3f4d2b0187e9a3b030fd3473061fa6a0b047ccd5820cf59a83411eb356059db66a11046ecd5dac07d9ab040cfb3560561f66ac0763ecd580e67d9a99178fb35192f1f66a085e3ecd388bc7d9a6d178fb34c82f1f6692e5e3ecd240bc7d9a33978fb3561833ce6a0d0579cd585676b9a84c1577359cb09ee6aed613dcd586067b9ab0ab0f735613b1ee6ac2733dcd468bc7b9a87178f735052f1ee69c65e3dcd36cbc7b9a64978f734b82f1ee69305e3dcd244bc7b9ab12cecf35638339e6a0f0673cd5920cd79a84419af3565832de6a13065bcd5dac4779ab3418ef3562819de6ac4ac3bcd588ec779a
  | 5 => 0xb3ab8fe352c571fc695eae3f8d579587f1aaf1d8fe34763a1fc6abc733f8d578bc7f1a86978fe34ff2f1fc69c05e3f8d318bc7f1a5b178fe34ae2f1fc69405e3f8d254bc7f1a47978fe348c2f1fc68e85e3f8d194bc7f1a30978fe34ae259fc68ec103f8d581eafc9a823d5f934710f5ea6ac2f57d4d415eafa9aafc19ed35627abda6a0cf57b4d41818f69aafacedd34b358dba69661eb74d2cc196e9ab1bd5dd35077abba6ac8f56f4d421eade9ab2bd57d35097aafa6aed5f3f4d57e067e9ab33d4fd355f561fa6abe763f4d57ce67e9ac9178fd356e2f1fa6ad25e3f4d57cbc7e9a8c178fd34f52f1fa69e45e3f4d384bc7e9a6a978fd34cf2f1fa698e5e3f4d300bc7e9a5b978fd34b12f1fa69425e3f4d258bc7e9a
  | 6 => 0x25841ff164f17ffe2c7a24ffc58c441ff8b23873ff17047aff06a080cfe0d57e0bfa1a93c17f435057afe86a0a27fd0d6083dfa1a8287bf434af0f7e868c21efd0d5c421fa1a7b843f434b1087e868f010fd0d1b421fa1a82833f435077afb86a0e0cf70d57d5d7e1a912bafc34b1575f8695c77bf0d2b83d7e1a57032fc355e7abf86a54107f0d5820bf91a82c13f23508827746ac0aebe8d58a0bf31a83417e6356382fac6a0f05f58d5920bdb1a84417b6356582eec6a1305dd8d59a0b7b1ab0abaf635052ddec6acf057d8d414bcfb1a82975f6353125bec6a1106eb8d4260db71ab12baee355e833dc6a0c187b8d4260faf1aaf2cede3563575bc6966aeb78d5915d5f1a5a2babe3565574fc6aed5e3f8d57a067f1a
  | 7 => 0x2f070ff165e0d9fe2cbc1a3fc5978327f8b2f060ff165e0b9fe2cbc163fc59782a7f8b2f050ff165e099fe2cbc123fc5978227f8b2f040ff165e079fe2cbc0e3fc59781a7f8b2f030ff165e059fe2ecc5ebfc5a18bd7f8bb316eff176f28dfe2ecc51bfc59d8977f8b2f12eff165e245fe2ecc3ebfc5ab87d7f8b258faff16481f5fe2ecc33bfc5978637f8b2f0b6ff165e15dfe2cbc26bfc5978417f8b1f082ff163e0cdfe2c7c18bfc58f82d7f8b2f046ff163e08dfe2d5c10bfc5978217f8b2d842ff1651085fe2c6610bfc5e36ccff8bb3179ff16862f3fe2ecc4b7fc5d7896ff8b3b12dff167525bfe2cbc4b7fc592c80ff8b258f9ff164b18bfe2cbc2d7fc597856ff8b2f099ff16400cbfe2d5e107fc597820ff8b
  | 8 => 0x2f158ff165e2a9fe2cbc543fc5978a67f8b2f148ff1703289fe2cbc513fc5978a07f8b2f13cff165e271fe2cbc4d3fc5978987f8b3b12cff165e259fe2cb64b3fc5978947f8b2f124ff165e241fe2cbc473fc59788c7f8b2f114ff165e221fe2cbc433fc5978847f8b2f104ff165e201fe2cbc3f3fc59787c7f8b258f8ff165e1e9fe2cbc3c3fc5978767f8b2f0e8ff165e1c9fe2cbc383fc59786e7f8b2f0d8ff165e1a9fe2cbc343fc5ab0667f8b2f0ccff164b199fe2cbc323fc5978627f8b2f0c0ff165e179fe2cbc2e3fc59785a7f8b2f0b0ff165e159fe2cbc2a3fc5978527f8b2f0a0ff165e139fe2cbc263fc59784a7f8b2f090ff165e119fe2cbc223fc5978427f8b2f080ff165e0f9fe2cbc1e3fc59783a7f8b
  | 9 => 0x56843fe164b087fc2c9010ff8588021ff0b0c043fe1616087fc2c2210ff858e43dfa8b1487bf5161e087ea2d623ebf459e03d7e8b2f07afd165b0f5fa2ca21ebf458f83d7e8b1987afd165e065fa2cb60cbf45944197e8b1f032fd1633065fa2c960c7f45e1acdfe8bb309ffd17660f7fa2c4c1bff45d9819fe8b25849ef16b31f5be2ca239b7c59385bef8b5a0fabf17762f1fe2ece5e3fc5d98bc7f8bb2978ff17642f1fe2ec65e3fc5d88bc7f8bb0978ff17602f1fe2ebe5e3fc5d78bc7f8b45978ff168a2f1fe2d125e3fc5a20bc7f8b43978ff16862f1fe2d0a5e3fc5a10bc7f8b41178ff167a2f1fe2cf25e3fc598cbc7f8b2f174ff165e2e1fe2ce65b3fc5978b67f8b2f168ff165e2c9fe2cbc583fc5978ae7f8b
  | 10 => 0x2f0c4ff365e181fe6cbc2f3fcd9785c7f9b2f0b4ff365e161fe6cbc2b3fcd978547f9b2f0a4ff365e141fe6ece273fcd9784e7f9b2f098ff365e129fe6cbc243fcd978467f9b2f088ff365e109fe6cbc203fcd9783e7f9b2f078ff365e0e9fe6cbc1c3fcd978367f9b2f068ff37660c9fe6cbc193fcd96c327f9b1f064ff36330c9fe6cbc183fcd9782e7f9b2f058ff365e0a9fe6cbc143fcd978267f9b2f048ff365e089fe6cbc103fcd9781e7f9b2f038ff365e069fe6cbc0c3fcd978167f9b0f043f41677087f82c3c10ff0585019fe0b08033fc160e067f82c8210fd858dc21fb0b0f043f616ae1f5fc2d5c10bf8596c217f0b19842fe167425bfc2d5e107f8597820ff0b25841fe1784b37fc2ecc10ff85ab821ff0b
  | 11 => 0x43978ff36862f1fe6d0a5e3fcda10bc7f9b41178ff367a2f1fe6cf25e3fcd98cbc7f9b2f174ff365e2e1fe6ece5b3fcd9ccb67f9b2f16cff365e2d1fe6cbc593fcd978b07f9b2f15cff365e2b1fe6cbc553fcd978a87f9b2f14cff365e291fe6ece513fcdc0ca27f9b2f144ff365e281fe6cbc4f3fcd9789c7f9b2f134ff365e261fe6ecc4b3fcd9d8967f9b2f12cff365b259fe6cbc4a3fcd978927f9b2f120ff365e239fe6cbc463fcd9788a7f9b2f110ff365e219fe6cbc423fcd978827f9b2f100ff365e1f9fe6ece3e3fcd9787c7f9b258f8ff365e1e9fe6cbc3c3fcd978767f9b2f0e8ff365e1c9fe6cbc383fcd9786e7f9b2f0d8ff365e1a9fe6cbc343fcdd9c667f9b560ccff365e199fe6c96333fcd978647f9b
  | 12 => 0xb2d8f5f37632f1be6f0363b7cdd9ac76f9bb197adf37632ddbe6ec651b7cdd8c7d6f9b598fadf36511cdbe6ec633b7cdd8c4f6f9bb3d8ddf37632f3be6ec64b77cdd8c32ef9b83865df3765b267e6ec85e2fcdd9ac95f9bb217abf37642dd7e6ec851afcdd907d5f9b5a0fabf376419d7e6ec827afcdd9ec8df9bb2179bf376425b7e6ec8196fcdc2032df9bb29787f3779b2cfe6ecd659fcdd94bd3f9bb296e7f376528cfe6eca3e9fcdd94673f9bb289e7f3767b2afe6eca5e5fcdd9496bf9bb28657f37090cafe6ed9673fcde36cc7f9bb3d98ff37762f1fe6ece5e3fcdd98bc7f9bb2978ff37642f1fe6ec65e3fcdd88bc7f9bb0978ff37602f1fe6ebe5e3fcdd78bc7f9b45978ff368a2f1fe6d125e3fcda20bc7f9b
  | 13 => 0x7a865fd3767063fa6dea0c7f4d97818fe9b25831fd3619063fa6ec360fccdd8ac1f59bb1d83db3764b07766ecb60decdd80bc7d9bbe582fb3766b05f66ec05ebecdd80b77d9bb0146fb37601f5f66ec033becdd804f7d9bb3d81fb37602f3f66ec04b7ecdd8032fd9b82065fb3762b0fce6ec761f5cdd92c3db9bb2d877737612f1ee6f2161bdcdd9ac37b9bb097af737612ddee6ec251bdcdd847d7b9bb08cef7376113dee6c7c10bdcdd9ec2fb9bb0979f7376125bee6ec2197dcdc1432fb9bb1d8bcf3764b175e6ecb62dbcdd88bc779bb358aef37622f5de6ec45bbbcdd88a3779bb10faef376219dde6ec427bbcddcac4f79bb3d89ef37622f3de6ec44b7bcd92c94f79bb1065ef37060cbde6c96127bcdd92c7cf9b
  | 14 => 0xb0d7ff5376113fea6ec21efd4d9003dfa9b1c87bf536290f7ea6c3c10fd4dd8419fa9bb157fed376213fda6ec41efb4dd8819f69bb1d7fdd376313fba6ec61ef74dd8c19ee9bb257fbd376413f7a6ec81eef4dd9019de9bb2d7f7d376513efa6eca1edf4dd9419be9baf978fd365e061fa6f0d66bf4ddb2bf7e9bb357efd375f2f5fa6ebe5bbf4d9c0b77e9baf946fd370128dfa6ebe3ebf4dac47d7e9baf8cefd36a919dfa6ecc27bf4dd7c4f7e9b2f09efd37660f5fa6cf01ebf4d9783d7e9b2d87afd36510f5fa6c7c1ebf4d8cc3d7e9bb3032fd36f4065fa6cbc0cbf4d96c197e9b28832fd363e065fa6c660cbf4d89c197e9bbfd9dfd376dafbfa6ecf5f7f4dd7cbcfe9baf92dfd376713bfa6ece1e7f4dd7c32fe9b
  | 15 => 0xb0d7bf637610cfec6e0a19fd8dd8421fb1b20843f6363e087ec6c6e10fd8d87821fb1b0803ff63762af7dc6ec419fb8dc1833f71bb1043ee3763af7bc6ec619f78dc1c33ef1bb1843de3764af77c6ec819ef8dc2033df1bb2043be3765af6fc6eca19df8dc2433bf1bb28437e375e2f1fc6f0966bf8de56bd7f1bb357afe375e2f5fc6ebc5bbf8dd78a37f1baf0fafe36ae1f5fc6ebc33bf8dd784f7f1bb3066fe365b0cdfc6ecc10bf8dab8217f1b2d842fe363e085fc6c6610bf8ddfaceff1bc6d79fe3767af3fc6ebc5e7f8dd7896ff1b3a12dfe37670cbfc6ebc197f8d97832ff1b2e865fe36190c3fc6ece107f8dabc20ff1b2f041fe364b083fc6c320c7f8dd82bffc9bb009ff937600f7f26ec00cfe4de3ec3fa9b
  | 16 => 0x7821fa2baf178fe575f2f1faacbc0c3f55d80bc7dabb0978f757622f1deaec65e37d5d90bc5fabb29787f561e087e86f255eff0dd7ebdfe1baf09ffc375e0f7f86ebe19ff0dbd433fe1b13867fc361e0cff86ebe10ff0d9dc21fe1b13843fc361e087f86ebc0cff0d86419fe1b0a033fc3610067f86c1c0cff0dd82bdfd1bb0067fa37040cff46ec010fe8de3ac3fb1b
  | _ => 0
def ns2_ (i : Nat) : Nat := (ns2_Data (i/64) >>> (35*(i % 64))) &&& 34359738367
def ns3_Data : Nat → Nat
  | 0 => 0xb3078217a1a57078217a1a3c078217a1a2d878217a1a19878217a1ab387820fa1a5787820fa1ac9578bc7e1aafd78bc7e1aaf178187e1ab0578bc7d1ab0d78bc7b1ab1578bc771ab1d78bc6f1ab2578bc5f1ab2d78bc3f1ab057cbc7c9ab0178187c9a288e43d6a9ab0d7cbc7a9ab0978187a9ab157cbc769ab117818769ab1d7cbc6e9ab1978186e9ab257cbc5e9ab2178185e9ab2d7cbc3e9ab2978183e9ab0d80bc799ab1580bc759ab1d80bc6d9ab2580bc5d9ab2d80bc3d9ab1584bc739ab1d84bc6b9ab2584bc5b9ab2d84bc3b9ab1d88bc679ab2588bc579ab2d88bc379ab258cbc4f9ab2d8cbc2f9ab2d90bc1f9a57078217a0a2d878217a0a19878217a0ab307821fa0a5712c7c7f0a3a12c7c7f0a5712c207f0a3b12c207f0a2d92c207f0a2f120207f0a258cc207f0a2f044207f0a288e43d6a8a2f098367e8ab3178187e8a5992c7c6f8a2f1385a6f8a5a12c7c5f8a818e43c6a99818e43c6a89
  | 1 => 0xb007821f81ab107821f21ab187821ea1ab207821da1ab287821ba1a
  | _ => 0
def ns3_ (i : Nat) : Nat := (ns3_Data (i/64) >>> (44*(i % 64))) &&& 17592186044415
def nodeData (i : Nat) : Nat × Nat :=
  if i < 6 then (0,ns0_ (i-0))
  else if i < 876 then (1,ns1_ (i-6))
  else if i < 1933 then (2,ns2_ (i-876))
  else (3,ns3_ (i-1933))
def node (i : Nat) : Node :=
  let (n,z) := nodeData i
  ⟨z &&& 15,(z >>> 4) &&& 7,retained ((z >>> 7) &&& 1023) signals ++ extra n (z >>> 17)⟩
def hint (k t : Nat) (w : List Wire) : Nat :=
  let lane := (hash 7 w k t) % 4096
  let slot := ((hash 43 w k t)+shifts lane) % 16384
  let c := slotCode slot
  if c ≤ 2002 then 4*c else 4*(c-2003)+1
def table : Table := ⟨2002,hint,node⟩
end Core.HybridData

namespace Core.HybridData
open SingleShare.Cubes
def pointerData0_ : Nat → Nat
  | 0 => 0x6d00d681a6833f06620c9018b030805f40bb016f82d105860ad4153829a051a09fc139026504b0092c11e822f0442084c10281f703d2076c0e681c0036406900cb018802f405b00af0150028404d00930118021403f007700e001a4031005b00a80134023003f007000c401500230038005400700070000
  | 1 => 0xd821ad035386990d1819fc33906650cae192831e86300c46185430385f90bd817782e805c20b6816982cc058a0afa15c02b185560a9214f029785210a28141827c84ec09bc134026184b60952126c246847f08e2119022b0449087810bc211041508100fe81f683e007a60f181dc03aa073a0e401c18375
  | 2 => 0x142e28284fe89f013c627584e489bc135e26844ca098712f425b04af8951128824dc495091d1220240c47b08e811b6233445f88b211482258444887c10dc21844298846107220b040f081110061fd43f387da0f981ef83d807a30f2a1e203bd876e0ec01d4c3a307390e581c7c38887030dec1ba036d86ce
  | 3 => 0x1ad635746a78d411a68349868c8d0c19fe33c46720cd6199232f06578ca2192a322063d8c6e18c2314c6228c38185430746080c0317ea2fa05ed8bcd17802ecc5d28b9717122df05b78b6116a82d1859c8b2c163e2c485828af815d42b745680ac3156c2aa054d8a8e150029c85328a58149628f85188a24
  | 4 => 0x21ba434486190b5214e4264846908120e6419482b9049207640b480f901120063fd47f38fda1f983ef87d80fa21f283e187bc8f6b1eba3d407a10f341e4c3c607860efe1de03b8876b0ec81d743ab074f0e901d0439d07330e581c9438f07170e201c2438106fb0de81bb437306df0db01b4436506c30d78
  | 5 => 0x287a50c4a129419281a50049f993e727b64f349df93b3274e4e6c9c6937f26e24d949ab934b267e4cc49919315260e4be497612de25a24b0c95a92a725344a3093f127124c84958924123a24584878908120223e8479c8ec91cb237a46bc8d09193230a45dc8b4915b229a44fc8989123222a441c87c90eb
  | 6 => 0x2eec5da0bae17502e885ce0b95171d2e225c0cb7a96e72db65b3cb6196b72d525a70b4716822ce85998b2c164c2c7c58c0b1116142c0e57ecaf795e32bae572cadf95b32b4e5668ac6157f2ae2558caaa95492a7a54c4a9195152a1053eca7694e129a65314a5c94ad29425254a43947b28de518ca2b9449
  | 7 => 0x35886ae0d561a9e35246a10d3b9a6934b6693cd219a373456687cd099a0533ee67accef99d1338a66e4cd5999d33226610cbc196a32b86538ca01933324a645cc8498fb31da637cc6918c4316c62a0c4e1890310861e0c36186030a46110c1b982a30386038c0017f22fc85f58be417ba2f585e80bc91784
  | 8 => 0x3bd07768ee71dc23b6c76a8ecf1d923b0c75e8eb71d623aac7528e9f1d323a4c7468e861d0039e47390e6b1cca397c72c8e531c98391471f4e379c6138aa7124e1e9c31384a7064e059bff37e66f9cded9bcf37826ed4dd49b9d37226e14dbb9b6b36ba6d3cda09b33364e6c6cd879b0335ee6ba8d6f1ad2
  | 9 => 0x421a83fd078a0e341aa832505ea0b14146825d045a07f40e6819d02da04f408680d5014a01d40228014ffb9fe93fba7f40fe11fb63f507e70fc81f843eec7da0fae1f4e3e847cd8f951f1e3e247c10f7c1eec3dbc7b48f631eba3d5a7a84f4a9e883cf879c0f311e563c9478f8f191e263c347830f001df4
  | 10 => 0x489a90fd218a425482e90251fda3ee47c08f4d1e2a3b847548e711c7238046e48d991ac234c46808cd1193231a46188c0117a22e645b48b3116022b4454e8a65145a27d44e2898d12aa247447288b5110a215441287f50f7a1e343ae872d0dfa1b1434a86650c5a17f42e2858d0aba14b427e84cd092a119
  | 11 => 0x4f069dd53b3a75a4e989cf939827224e289c1d37ca6ec4dc09b5136426bc4d609a9134c268c4d0099c933226584c98990131a26284c38983930025f24bc897592e425ba4b5a96852caa5894afa95c52b2a5594a9a950529aa5274a32942d27ea4f149c6935d265a4bf4966929524ca48d490291d5234a45b
  | 12 => 0x559cab01559aaa5552eaa2d53eaa7154c6a955524aa3b545aa881509aa0753f4a7b14f029d25388a6e14d6299e5320a6094ba296652b0a5314a02933524ea46948628fe51e4a39946d28ce5180a2cd452a8985116a1fd438a86450b0a12941e28305044a055403a7f94fda9f813e927c64f749eb53cfa791
  | 13 => 0x5c1ab8056fa2de85bb4b7316e02db35b4ab65d6c4ad7d5ae2b5916ac2d4a5a78b4b96912d165a14b3f96792ce659b2b3316602cb4594cb2616462c7e58e0b19162c2c4a5878b0b96112c145810aff15f72be157aaaf255ddabad5742ae4d5c2ab7756d2ad715a82b425668ac9958d2b0e5604abd15742adc
  | 14 => 0x6272c4b5890b1156212c3f5877b0e161aac32585db0ad6140c251844307c60dcc18582ab0476074c0b581030146010bfe97f72fe25fa8bf217dd2fae5f42be557c4af7d5ee2bd957acaf4d5e82bcd5793af195e16bbfd779aee65db0bb2975eaeb15d46ba5d744ae7d5ce2b99572bae495c7ab8c5712ae19
  | 15 => 0x68ced16da27b443686ed0ada0fb413680acfdd9f5b3dd67a2cf159dbb3ab673ace3d9c0b37566d2cd719a833446670ccad98eb30f6604cbd5974b2dc65a0cb0995b32aa653cca49943327a64dcc981929b245646ec8a590db20f6406c7dd8f5b1df63a6c71d8ddb1ad633ec64d8c2b17762d2c5758a8b145
  | 16 => 0x6f1ede0dbbab7696ebadd45ba2b7396e5adc85b8ab7096dfadbc5b71b6d56d92daedb56b6a06d24da19b3d366e6cc0d949b2236376c52d875b07b6016be6d799aed35cc6b7cd6c1ad235986b18d601aba35686ab8d541aa135366a54d479a89350669f0d3b1a7034d4698ed2eda57b4a3692ed22da3fb473
  | 17 => 0x75e2eb8dd6abac77572eab5d4fba917508e9d9d343a5b749ce901d193a24742ce821cfd39ec73bce741ce139b4734ce661cc5397c72dce581ca93944726ce4a1c8d390c71fce3c1c7138d4718ce2e1c55389c711ce201c39386470b0e12dc1eb831704ae05dc05b7ff6fe6df95bec37cc6f80ded1bd4379c
  | 18 => 0x7ca0f909f1a3e277c38f839f003df27bcaf75dee4bdbd7b60f691ecb3d887af4f5b5eafbd517a86f4d5e93bd1a7a18f3f9e793ce479aef325e5ebcaf7946f25de44bc7d78def185e2b3c487876f0b5e0fbc117806efd9df43bda7798eef9dd83ba27728ee19dbc3b6a76b8ed41da13b34764cec61d853afd
  | 19 => 0x82ff05c60b24157829904fe098c123822d042207d40ec81bd034606340bb8161029604bc08c80fd01c20324056809700f601940268031002e0003ff57fd4ff71fe73fc27f6efeb1fcf3f917f0cfdedfb6bf607ea6fd21f9ebf317e46fc55f83befb7ddafb7df68bec67d70faadf4f3e907d04f9d1f34be5e
  | 20 => 0x8941124a242447688d1116a226443e8861108e20ac40787f30fb21f043d2878f0ee61d5c39d87210e0e1bb436886b50d321a0c33686570c8218ac30885f50bbe17242d885950afe15942a785390a46143427b84e1098e12c424b847b08be110c216841307f60f941e783b907460e241b9835d06820cac18a
  | 21 => 0x8fd71f823eac7c98f7b1eca3d2c79a8f1b1dfe3b8c7648ead1d2e39fc7348e511c6a38646ff8de31b8e36b46cb8d7b1aca35246968d1119f6337c6628ca9191e31cc62e8c43184e30445fa8bd9177a2e845c28b69169a2cc458a8afb15be2b0c5538a8b14de294c51c8a1d140227944e489ad132225dc4ad
  | 22 => 0x96112bea577cae495b32b2e5604ab595552a76547ca8494ed29a652eca51948d28e25154a1d9423280e4fac9ea93b9273e4e249b89355267a4c8498292ef25b24af4950928b24e6495c920922b242247ec8ef91c9236646748c09167229644d488f910321ce434485d90a1210a41bc829903d204640247f6
  | 23 => 0x9c0937da6f4cddc9ba3371a6dc4dad9b3f364a6c3cd7c9ae3359a6ac4d4a9a7934c66934d1b9a21341267ccceb99bb333e660ccb69957328264acc8998fd31ce6344c5d98a5311e61d4c2f984930666074c0397f12fb65f14bd797992f065db4bab97412e565c54b7f96e92d9a5ac4b4a967f2cc65924b16
  | 24 => 0xa21543fe87950e7a1b9434686350bba161429684d508fa10941de834d05ea0a7412281ed02fa049406680750009feb3f9e7eccfcc9f833eda7d44f9a9f1f3e067ba4f689eb53d3e7a24f399e5d3c8278acf0a9dfd3bce7744eda9d993b0675b4eab9d413a4a742ce7a9cdf399272bce499c7738b67104e12
  | 25 => 0xa85b508aa0bd40ca8034fda9f453dda79f4f069d9d3a5a72f4e269bf5373a6d14d769a95344a66d4ca298ed311a6074be2975d2dda5a14b0a95a52a6a5314a2a93ed270a4cb495e926523ea467489690bd209a3f947ba8f1d1d8a39746fe8da51a9a33d464e8c4517aa2db45828aa5149a27d44c2891d115
  | 26 => 0xaeb95d3aba0d733ae4d5c62b85d6fdade15b8ab6a56c6ad715ab6b515694ad0f59eab37d662aca9591eb1dd62dac41584ab02d5f7abd3577aae9d5c8ab7b56caad25597ab1355faab85565aaaf552aa9fd531aa4d546ea885504a9ed53aea6f54d3a99152f6a57d4a4a92d5222a3dd46da8bf5146a21d438
  | 27 => 0xb50d69eed385a65b4b1692ad1e5a2eb4476856d03d9f9b3d7677ace859c2b36b66aacce598eb30365dacb5d960b2a56512c9b5929b23d6442c81d8f5b1cf6372c68d8c4b17362bac51d898b11b620ac3bd869b0b76142c215837b0556076c07d801afe75fa2bed57ccaf7d5ecebd4579aaf195e06bb9d768
  | 28 => 0xbb457656ec45d7dbadf758aeaa5d46ba7174aae8e5d0eba0773e2e75dcddb99f730ae5a5ca6b933723ae415c77b8d97186e2a5c49b87d70cee145c1bb81b700adfbdbecb7c36f5ade5dbc0b76b6eaadcfdb91b7096ddedb4db5eb6a16d0ad9a5b26b6316c2ad7e5af1b5c96b5ad65dabdb5656a9ed4e5a91
  | 29 => 0xc10b81eb037e064c0b381370216037c0578083009e006bff77fc2ff2dfdabf9f7f12fdcdfadbf457e56fc3df7cbedd7d86fab5f4bbe7b7ccaf92df1abe1d7c0ef7c5eebbdbd7b4ef645ebdbd657a9ef4e5e91bd0d79eef36de62bcaf7932f20de36bc53787af09de08bbfb77c6ef35ddbbba17716edd5dad
  | 30 => 0xc6f38dbb1b1e356c6978d0319ae32ac63f8c53184e2fec5e78ba316ee2d2c58f8ae715762a3c52b8a2b13ee272c4c9895b124623cc463889710d620fc40387db0f5e1ddc3a5871f0de61b1c34d866f0c86185c2f585bf0b26157c29584ff09a6126c235843f08160f5c1d5837f068e0c3c17182af04f6090
  | 31 => 0xcccf9967327e645cc7798b730fe612cc1197f32f965e5cbb3973f2e0e5b4cb5596732c96588caf595c32b3655bca9b950f29ce52fca4b946f288e507c9f393b326f64d4c9959303259e4a9c93f9257245e47dc8e7919722be449c87790c72126417c8138ffb1f863e5c7af8f2b1de63b1c74d8e6f1c7e384
  | _ => 0
def pointerData1_ : Nat → Nat
  | 0 => 0xd263a48f48b690cd1ffa3c7473e8ddd1a7a31f45ee8afd143a257444687ed0e9a1ab4306853d093a0ef416e81fd023a01f3fee7f3cfd19f7b3ea67c7cf7b9ecf3d4e79ccf219e173bde771cecf9d773a9e746ce739cbf392e71ace1d9c0737be6edcdc79b67367e6c5cd759ac3351e699cd1f9a1733de671
  | 1 => 0x3557eaa6d53baa475426a7bd4dda99752e6a53d48fa8eb5186a26d439a84350169f8d3dda78b4eae9cbd37ba6cf4d4e99fd325a6234bde96ed2c3a55f4a4e93f
  | _ => 0
def pointerData (i : Nat) : Nat :=
  match i/32 with
  | 0 => pointerData0_ (i % 32)
  | 1 => pointerData1_ (i % 32)
  | _ => 0
def pointer (i : Nat) : Nat := (pointerData (i/64) >>> (15*(i % 64))) &&& 32767
def ruleIdData0_ : Nat → Nat
  | 0 => 0x5a09011822030058068014a4680951160f41702d04f08a0d81480f0140190e8b510a19c1d82b05409c1081702a03c058006842e85a8670760ac1502704205c0a80f016000840b50ce0ec1902b05409c1081702a03c05800
  | 1 => 0x220160b9680760e81902b0540840c01602a03c05800576684a892b1ca324550a90880d41102000a0060b2ba3d67a89612b212340550a91020440280138247c8b8660880e0168240440600b00d00a0048f89d12019822038
  | 2 => 0x860841001001601c028040060046f05e0740a41402402e0500780800a00800800688d0d5ea533da7b0bf96925a16c298430220060c2bc2fc428730d10ea1a0300590a604c020011a21d4340600ac150298510a010c1781e
  | 3 => 0x36018010002a639c6f89a0ec1bc220300520880b81400a0092b10b1be2fc4d07a0ec1101802904e05c0a0052a639c6f89a0ec1242203e0600a4138220280152aa543445486f8760880f018016028030050012402502c854
  | 4 => 0x83d075a325821234c6907a0b61181a8011d02ec4305209a0e4148210400580800f0100160e41b834d15602bf3004f89110911e1982d822832afcf79c2300488858ed1be2fc4786608e0855f2573dc4848408b0e01a423821
  | 5 => 0x2c0480500800e0182203c0720e0120230440600a00e01a014010010ea1a0300560a814c288500860bc1281e0220103c0770b20fc1b81d0200340600a012018028028429650f0e71941bc308550300380500800a00a1041f
  | 6 => 0x2aa28c3b85906e0a00e81001a0300500900a008900940b21542a0530860740800b00a0100180112a23c3484a0700dc1983105808c0680c00c000aa0a813c1f03d83104a0840a80f014018010003463fc4106c0c413425817
  | 7 => 0x740d81282102a04c07804004b08f81181b027c2283a05409c0b814016014002c13021842383b05e0ac1282102a04c078040043005e09511a1a83084605c0b01281502603c023471ec1101c8380480880c01401a01401001
  | 8 => 0x280140090017a2582003b0660a00f81b030058060020003644707906e0ac14818016020020030040040025b1662381b82b0520600580800800c010010010885409e0f61b41a0310420540780a00c0080025a1781c023846
  | 9 => 0x2d45983b0740c81582a0420600b00f016001a10b50ce0ec1902b05409c1081501e02c001081742d43383b0560a81382102a03c0580025c3dc658bd12c1882684b0800b40c01600e684a893e256424728de1922a822022
  | 10 => 0x12e1c42d05706c0b80d01301e01c0312a1641c43705a0ae1241b02e03404c0780700cd216225c4a470c9509812e1c42d05706c029619821a82804806f0d8110168270480880b8a00cc18c1802d0400780b00b00e01401801
  | 11 => 0x1a0300500900a008860780ee1902c83703a0400680c01401802802306264488780ee1641b81d0200340500600a7149505a09e1142103a06c0a81481a01e0180022043e710730ba11219c2d0310540880d00a00c7c4950b2
  | 12 => 0x42743c0770ec1641b81001a0300500900c014011560f01dc2c85306e0740800d0180280300512a1e03b85906e0b00e81001a0300500900c014978780ee1641e03703a0400680c014024030051d21e03b86e0b20dc0e810
  | 13 => 0xf01dc3205909c0dc0e80d00c0140125d2583043e0780ee1642701d01a024028020f01641b8320580800e81001a0300500900c015a51ea34820c3b85906e0400680c014024013493e44fc3b85906e0740800d01802804806
  | 14 => 0x500740800d0180280100084a6109f8940ee0dc1401d0200340600a0120092f09410e1c82a0200200340580700a01000c244ba434608800f81d41302002a034050098467cc918780ee1b42c84e03a03404806004b145207c
  | 15 => 0x6e0440800d018024fa1c61360dc1181d0200340600a012014012c62402503c87703a0400680b0080080080058a708770d517e2503b81d0220400680b003098ab8941061dc1b81d0200340600a0120089f8d91281dc33037
  | 16 => 0x380480680523e3404e89b1202043305d08208c0e01201ab18fa8d015426c3b85d0720740880d00a008e09171a23404d86008c0e40880d00a00c00a614c097cc216a16c26c4787905803402000696b1c8710117a2ec4d896
  | 17 => 0x2d38220430720e0120230300500700d00a00800c2769ad30b590f17e1481c00e01a018008001001f83c8690700dc198260460380680c00c000a006b0be0e01982804c08c0700d018028001c123e45c6809b1021982e841
  | 18 => 0x216198220380480580680700a005a7a622d63d85f8470880e012022028034009171ec2fc598440720e01202203005006805002690518440720e0120230440600a00e01a008008440720e0190240460880c01401c03403805
  | 19 => 0x620600a80600a00c01123206290400770da1a82c83703a040048061481e03b8760da1a82c83703a0400480600a008ac12216e23c3304a0860e01b8230440600680223e408550660880e01682402c0340380500298c8f917
  | 20 => 0x1000c010016a0464660790f01dc3986406e07406006004888d28e81761e03985906e0800e810018028028a911c1e42d84c06e0ac0c008006008008004422784687b0ea1a82a8460740941001502601c520760da1a832037
  | 21 => 0x3400c002644ae88ce418630a4848d0b410a0880c0026a0d29321f3348464660830ee1900e80c004d49a89c72a63bc738a80ec1101802d044080e39302342d03c0770b20740800a00c014011412203343983a0300380600a
  | 22 => 0xea1a0300560a814c2885005e094088045924903a8680c01582a0510a010c1782503c045641c90ea1a0300560a61442804305e09408804852724340600ac1442804305e0940880f00800a143546a6890978ea1341e43b027
  | 23 => 0xa214017825028014023444a6358340600ac150298500860bc128118570a9aa89d0d01802b0530a010c17825022010c38750d01802b0540a61442804305e078088042143c03a8680c01582a0530a21402182f04a011650ce
  | 24 => 0x5e094089cb2b42743a8680a814c2804305e0940880457a5fcac8750d0150298510a010c17825022894f71ca3103c05c0680c0150298500860bc020d619c274340600ac1542a0530a010c178250224c4688ce0d01802b053
  | 25 => 0x50b44c86108e0ec1782b04a0840a81301e011ab9811321842383b05e0ac1282102a03c022652ac1d4300560a814c288500860bc128110090b1ab187264248340600a814c2884305e011659892a61d4340600ac14c28843
  | 26 => 0xea1a0300560a814c288500860940880485cd65ab22530e4c8340600a814c2884303c6044c86108e0bc1582504206c0a01301e010013582b427c2983b05e0ac1202102a04c020013025683083b05e0ac1282102a04c07804
  | 27 => 0xfa1b4328580a61200c01300c00d661cc1422303e8650b01200c013018018018023d85fcb493125a3382d85308e0d81280a00a7b0bf9692624b42384306c0940a00f00800a1842f394620b612d1561a0300530a010c0218a
  | 28 => 0x3c0440800b00e00c00a672dc510a18ef1ac11c1f83b05a0ac078006ba998c61421802342304406c0940a813008d716698b2da56c929111982100c00c0100080035b6b4898e68840880e41c0240460880a00e0027305088c
  | 29 => 0x680cc0d806000b00ac88d0b01181e03606a0940d81502603c7c8e61842e04e8890f41942c04708c0d802002390638c318519a2d0428680800880c00e004d70fb15c24a3e05f06b0d00600600a0040013398d26415021823
  | 30 => 0xc001341a630c3e4730c21701e8308580a611c2300434c4cc7c8e61842e03e8610b011c2300400469cd30f91cc3085c0890f41842c04708c010012682663e4730b80fa1b03085808e118020026bc40c520700da16024040
  | 31 => 0x17e2243385a0920880f81e0340500515d1c03604f8450840e81502703405c05805000d7c6c09f0921081d02a04e0680b80b00a001672c21b027c228420740a81381a02e02c0280038a4a85785a0921081f03a06c0a40d00f
  | _ => 0
def ruleIdData1_ : Nat → Nat
  | 0 => 0x7a0ac040040060040018f2de3e4730c017e2f0448650c211c230042ba3604f86508a0e81702a02e0500700b00a0021894513e1942283a05c0a80a00e01601400065090114170280360600700c01402003003000710d40f1
  | 1 => 0x5004c078076c07385407b0bc0f41d02902803c02804004000d48c91821ec2f03d0740a40a00f00a0080009e0de1781d02904805c0a00f0100180100100048c6b0a813a1782903d0740a40a00f00400219c326bc4d09185e
  | 2 => 0xd88560a813a1b41a0280420540780a004001b08a813c1f03d8340620840a80f014018010000620840b01501c0300500800c01401802002001349d11e427c1e03102a02003005006004002d059e740e79aa13c1ec2f035
  | 3 => 0xf81ec3703104a0840a80f004001688ba1502783683c0680c41282102a03c030002a82783d83104a0840b01501e030030020002a04f07c0f61a41a03104a0840a80f00c008000cc1502784b07c0f60d01882102a03c03002
  | 4 => 0xea0c41482002a030050070007d8e91712e05785a09e0d20d010815004001b11541582a03e07b0500941081501e008001541502783e07b0620941081502603c030022a82a04f07c0f60c818825042054078060005505409e
  | 5 => 0x4c0800a013008004318370600b0108200280380580500800c008004d489ce99232062903681d02a038030010009a8e990309a0540700c014020030050060040015f26a3b44f09a0ea0c41602002a038030004ba3044f07b
  | 6 => 0x5209c0a0052a639c6f8af1341d82203005209c1101400a688738df1681d83784407c0c01101401c028012553443d86f8760880c01101401802801001868d8cd10df1681d8378440600880a00a004434618c011a1d41d030
  | 7 => 0x1e010011902861842383b0700ac1282101e0100100086ad90ea1460b60ec1c02b04208009802002b28768df0f41d823844060094108140080092a8f61be2683b06f0880c01101e0280140125638842c6f89a0f41d822030
  | 8 => 0x40008d1120f21bc1582903c060058080060080043669a6406987b0760e01582102603c0200232034c468760b611c1d8380560840980f0046407c8d30f616c1d8380680ac1081301e008c81431a611c1d83806c0ac10813
  | 9 => 0x2d45085b0ab0ee17c2802803e0700600a0040021c4375a69ad2c8b70f21bc1582201c0280119028850c6b0470760e81582504203c0100034a1e41d83a0640ac1502102e0580780b000b483c83b0740ac128210300580780b
  | 10 => 0x1480cc1401f0360600b00c004001128790d21902003305007c0d81802c0300300225c3e0518690660a00f81b030058060020004b8478690800f01981f0360600b00c00c0011290116c1e43b8690c81402401f03803003002
  | 11 => 0x700900b0140100140100132244c7008f0cc1542503806e0cc10807008000c89131c023c3304a0800e01982601c0100043c8770e9b29d13105c85b09b10a0f00300057c7dcc796f17e2f84486604406c0b00c0150e4970f8
  | 12 => 0x70090110160280080099222e1101e0390700901102102c050028012042a82203c0720e01202102c050040050029505f8aa0880e41c0240420580a00800a0048b90b17e1101c8380480840c016028014009522042a822039
  | 13 => 0x440500280187a7e0d5951212378648aa0fa1202203b044274220430720e0148240460880b81400a008009021541101c8380520900b8140100140100126c45c858bf0880e41c02904805c0a00800a005b3b6639645c22039
  | 14 => 0x282334510910de0e81700e01402001802000208360620be1342582202e05809010014020039942082f82985209a0f411810010018028030030f8f79a2300488810f61be29047866044030011d5326544959091ca32455044
  | 15 => 0x3f6690d019531656c5783e03c02000441880b515f1ac1cc1ec36834062018010003f44dc528a11181f03d04808e0d8078060047e4a392a24c34c5787a0b41241f02901e0280343f6d0654878d919a1281d01701001001000
  | 16 => 0x2b8494418690300300100088d115b636b6d49b12c18b2b649488820004001b4acd3ac680ca98b2b64440f017010008004446d2b34fb18b2b64440f0180160200100059c3c8788ad10c1142203a04e0880b81401110e212d5
  | 17 => 0x900b81682200f1296c2d7344648c296f19a2d04283e04e0896b26e3aa6b4c99382563946484404405002a6d304408578490880f81c82904e0900a00800ab0cc10490880f81e03905209c1202202e05002c4989111d141f6
  | 18 => 0x2c0300300223e2083606209a12c1401702c0480500800e3fc580820d81882684b02e0580900a0100187f8820dc1b03104d09605c0b01201402003941180208360610aa0fc0b816024028040078969bd152292003e87c8b3
  | 19 => 0x51309c8f71962704b06709a12c2002d04e05c039a631c508a08fb0aa1481f834030038040022e647c650700d61882684b05a0a00c00a00e0053818f25c3345b8a11181b01e0220300580611616e2945088c0fa1b024018
  | 20 => 0x1fe3cc758cd1442284284a0901001e02235c49c758b710a1882684b0901000c00e00c009119392344507b8bd14421425840076088011141ee2f45108f114214310400780ec1b82289ab64a410012c1882504006e0880c00c
  | 21 => 0x1121f43e04a09011c1e00689cd996da273ae4cc818a11181f43684800cb6d139d7266458528a11181f43684808e018011fa26e458528a11182243e87c09412023806004b6938a2b3405205789309a1242003e04e0780b927
  | 22 => 0x6000800690901001982803e06c0c0160180180100015828c1602802a0380680c014020018020020002f01f03c05c0b014016020028040060080080089e5800f81b0300580a00c01402001802002001381fa31e4585088c
  | 23 => 0x5a0800a00b00e01402003002001160a60c21602303606a0d01281b02603c020021ae3042e05a09e1142103a06c0a81481a01e0016089812e2203885709e0c80d017026028040060ce1702484207c09c0f81e03405c05808
  | 24 => 0x6008008001080c41601501c0340600a00e018028030020004106c0c412c1f82302e05809010014020038060ba1382082f0480740e0190240440680900e0184003104c0540700d0180280480600a00c008000cc18c26030
  | 25 => 0x620540700c01402003005006008008001320c40c01501c0340600a010018028030020005b88e0d61882904d0960e41a02201c020030022662dc2904d07e0e41a02301c020030030040047483c0620540700c01402003005
  | 26 => 0x2c02c040030040006908209a0e4120230420600b00f010018010010c60c0130210400500700b00e01402003002000af0da1660540700c01402003005006008008005b86283206109c0bc0e0190240440680700a0108d837
  | 27 => 0x40002003105c0540700c01401c03005006008008000ec1b81881501c0300500800c01401802002001391921f4334528a1118224240220180087c06b0800cc1902803e06c0c016018028010002241e41f02b04a0840f018
  | 28 => 0x620600a80e01a0300500800c00c0080035e4e86d0650bc16c2603b04c048068090060011612c0c21382082f03a0700c81201a0240380615c208358620be1482684b0300380400245a2783804706c0c41282102a03c05006
  | 29 => 0x1e0300500800c008009b034e618bf1241cc2e04907d0d01802984b08c6344a8940e61542a0430580440800b00800c00aba45c4b09591c1a02a8548810240440280125c310478690700dc1982c04604c0680c00c00074834
  | 30 => 0x20006d0a40ec1b41881501c02003005006008008001b21bc1b83102a0380600a010018028030040007283f0620b00a80e01802803005006008008002364404c8910620540700c01402003005006004460580680a00d813
  | 31 => 0x11c1e43b05b0980ac100030040040036d4e68bcb70830560380600a01000c010010003544a0770420800f01d0380440800b012009160700de11c1b03104a0901081501e018010003a648c818a40da0c40a80e01001801802
  | _ => 0
def ruleIdData2_ : Nat → Nat
  | 0 => 0x200280400700a4082203c0720e0120230440500700800a008008380460600a00e01a0300500800a00c01001000db8648910de07c0d81802c050050080060080009905007c0d81802c0500600a01000c01001000750a90de
  | 1 => 0x1d62284286209a12c250480800880c00e0043dc658c51602583104d0961282001702c04803b6f2b82945088c0fa1b0250480440600b00c004b796ea2b3485b4ad91119820c0600a0100080009d1202083603f04605c0b012
  | 2 => 0x9c1041781d0380640900d01201c031fc1ac3002e84e05e0700c8120220340480700a20c2e04f08a1081d02903405c0780a01001800370390638c31851682142103e04405c074505c0b7c5689811015c1901701402003127
  | 3 => 0x720700901101a01c02c528a28c06302b0300500700d018028018010009984207206a0c01302001c0340600a01200c00ae11282483f07404c0540800d0160100198a0e81902e84e0820bc0e81c0320480680700c6286485d
  | 4 => 0xb20ab8ce0d01802b0540a61442802f04a044022741c236c678c71721d42b8560a81442182a03c1c83504c06a0c0130210400380580900800c008ab0d617c1c03305808c0c00d0180280480800cd1cfa8d015426c4085d
  | 5 => 0x980f40f81400800c010010007245f0940fe150298430820740800b008008009181e82bc1f02704a07c0f01702802c040030005244e05c0b40d81702d04e0900d00f00e018000830921081f03a05209c1201a02e03c04006
  | 6 => 0x40040008007e0980a80e0180280480800c014018020022fc1f8310300540700c01402003005006004000d90f01641b81d0200380600a01201802802002dc4b08940b21502204304a0780800b00e014019ce1b41ec3805e
  | 7 => 0x1460dc1401501802804005006008008004ba7cc1882502a0300500800c014018020004685a0910de0c40a80e01402003005006008003721f00c40a80e01a0300500600a00c0100100114c6d0b30620540700c01402003003
  | 8 => 0xe01402003002001711d33625d08180e0180280400600a008008001bc2b0140250480840c01602a03c040020020009b0a40d20dc1881501802003005006008008001ae2a43e0760620540700700c014018020020006c8ac
  | 9 => 0x40011788303e06c0c01601802804003004004001101322440f81b0300580a00a01000c008002a42383c85b0560840b00b01001001802002000b70d90cc0dc1582801c03005008006008008005c67f4a50950cc0c01680b
  | 10 => 0xd21202003303e06c0c016018008000d91981901982803e06c0c016018020030020006c8778e217a2544983b05c0a80d8140060005181f0360600b01402602c04004006008008001c42f45a0a212c1bc2001f03605006003
  | 11 => 0x4808c0a00e010014009d82c444c5586b0be0e019826016024040043fc0c80f81b0300580a00c01402001802002000fb8a513a2304487c0c20941101b0280300116f1c01e42003b06607c0f01b0300580200200058066883
  | 12 => 0x3150a48cb18c2b44e0670960b41382401e020039fe35c3e8348480800cc0f81802c03003002000544959091ca324220390460880a00e010014009920881001e039070090118220280380280200242c810440800f01c838
  | 13 => 0x4b90b110d1342343586209a12c1c826044038031431ea1f43606209a1280b81602401c02119104204360620be12c0b8160240280400700d154fb96f1f4294460890c20ec1100c0043ec6e0c613e0fc1202303005007004
  | 14 => 0x142d4380470740d81902a04206c0a00f000b94fc9c424c42c6f8b50f4168210300427fc9f12f1e42e85a83104e054078080008c49c9271d62e85108a10a128240400780880727516e2945088e0d61341c83704406006006
  | 15 => 0x4ee658bb8dd1a62e45009c0921100f01300f1593b9241ea3745c8a0136144098040069dcec9761c6354688a013e15c2781a026dc13b1ee1b63405c8b81401d02304404c0780aa002ea3ec650c81862d44d0860ce0b013826
  | 16 => 0x4801c02b745ce3c8738ca1402403782d04e02001b735ce98ce08f21942803d06f04e02001c5a32e5bc890a00ca0ac0f00e01600c004598b115ce20df1401e822030028020029c32ec3a06e8d119e2ec5008810c15c28ae6
  | 17 => 0x640a00d01301e804bc16318627c400710ae0680980700c764b18981001c42b84f06c0680980f00cdd51015a1c63385e0980e21602b81a026ba1100bc1301c42c05708e0c81501a02603c0226d3044085006f0d811016827
  | 18 => 0xce15c2a82c03604c07b765d03f06409712a1c43385703604c07c5c4b82944c0710ae11c1901a02603c0345b4b89484c07a0ea1c42d05709e0d8032784005684c0720e21602b8470640680980f00c9e1001780e21602b847
  | 19 => 0x2e04c0500800c3a47289811020c3885709e0c80d0170260280435743a260440710ae13c0d017014020032e82e0260440710ae13c1901a02e04c0500800d17a2e89812a2203885709e0680b81301e020033761f82604b871
  | 20 => 0x140200337515a260440860e215c27817014020034606ee7686b8c11301c42d05709e0d81901a02717d0e92813025c440710ce15c2781a026028040981101d83885709e0c80d0170260280400625e2e84c0880e215c2781a
  | 21 => 0xe4ec950b21381c42d05706c0b80d01301e01c031b31a62c84e0970e215c1701e03404c07807008590590971101c42b84903405c0980f01001c031f01a43044c0880e215c0d01702602003ae95be2e84c0880e215c0d017
  | 22 => 0xd185009c4350664b189811013c0d017028971191aa33058c6a0c21702c84484300e880909081161c02383b0640a81081e036001bc1081f022c2e0570640a01081b02e04c050004423544687b0ea1c42302b04a0800a813
  | 23 => 0x560a81481a01f19231b796a6808d41351d413c210220069e93b1fb3e662cad8cc1220f80b8080011893b1f91b62703d8750b40a80d0070009d8fc9db29225c3184f0580a80d01301eba93ca012f058c9112110015c19013
  | 24 => 0xc0009a9291c61702784207a0e81b01a01e028030001a81702d04f0921141f03a0520680780a00c000ba93c0ec148278450740a40d00f014024030004f613c2404507a0a01381a01802003003000770bc8dc0a413c1e83b
  | 25 => 0x2c01702d04f08a0e81b02a052068078006f63842e05a09e1081d0360540a40f01a01e0009491b2201702d04f08a1081d0360540a40d00f6f435c278450740a40d01701e020030000f61702904f08a1081e83a0540a40d00f
  | 26 => 0xf61e83a84f0600a814814000d7c9a8d41341d42e04f0921141e83a034018001651c22302783d0500680780c014020030003501702d04f08a1081d0360540a40d01301e0009a85c09e1142103d0740d81501a01e001be2eb
  | 27 => 0x10c1d42e04f08a0a411017014020030d415c2b4430670b813c2282902e03c0500800c9f0ee92922638c700dc0ce13c1e8270005988988b0ce13c2283a05409c0b80b0007e4931021be1e82d04f08a1081802a0525289e095
  | 28 => 0x1620ec1c01301a01c020014fa5dc850fd1a62c44d84406604c0680700800633b7f5d89f4850b113604c0680700800c00c666fcdf5bd1ff3aa394708d70ce13c114651a42b8568860ce1702784505205c0780a010384570ad
  | 29 => 0x9c1041781d0380640901101a024cd18318a1742704105e0740e019024044068098d48d4e08ee05e0700c8120220400680a8d28d0da0f71e02f45889511012c0880d4066d0cb0b11141802881101a01c030058d09f519946
  | 30 => 0x380640900d01201cef1a30ba1382082f03a0700c81201a0240380633460c6285d09c1041781d038064068060ba1382083b05e0a00e81c0320500900d00e0013f2360ba1382083505e0740e019024034048061ac2744805d
  | 31 => 0x2e44d03204e05e0700c8120220400680700a011771231b43582e84e05e0700c8120220340480746e1742702f0580700c8120220340480700a0105805d09c1041e82f0580740e01902403404806700bb43705d09c1041781d
  | _ => 0
def ruleIdData3_ : Nat → Nat
  | 0 => 0x820740e0190240340480700c6283205d09c0700c8120220340480700a0104106c0ba1382082f05008c0e816024034038052583042e84e0820bc0e81c0320480880d01201ca204e0820bc1602403a0700c81201a02403806
  | 1 => 0x9c0b00c81101a018028018d6bbd1802b0300380680c01400c008005de7f44a8300300380680c01400c008007026283084e0760700c81202203403805008000d198a1601903084e0380640901101a01c028043141903084e
  | 2 => 0xf01642a0430540940800d01601c900b01281642a0430580400680b00a010018013846bc9d0ee1b41942f04c024034038033f46bcc18650bc16826036024034020034fe6a4960c10f813816019022034048051361f032061
  | 3 => 0xc01401801000514748a20620800a80e01a03005008006004000ac1462541401802a0380680c0140200180100077cbc8310300540700d01802804006006004620780ee1d02c8370200340600a0120180280231a5846a89f
  | 4 => 0x1d23a01881501c0340600a00e014018010004bc4006e04c0540700d0180280480600a00c0090c1d22001301501c0340600a012018028030023a44002002a0380680c0140240400600a00c0099b12a0d01881501c03405008
  | 5 => 0x1c0340600a012014018013365785183102a0380680c01401c03003002001c10b31001d01301501c0340600a012018018011880c4160150260380680c014018028030020014006e0620b00a80e01a0300500600a00c00800
  | 6 => 0x2a0380680c00a004001361481f0238360620540680600a00c010010005b4888d91000dc1301501a0300500900c01401a811ec3b84001501a0300500600a00c009e01460dc1402602a0380680c014024018018d839441815
  | 7 => 0x400600980d01802801801000e0cba0d71820d01882402a03806801000bc0b594413e0c41201501c0340300100052c9b0a41001f0130150260380680600a0040014b0d20c40a80e01a0300380600a004001e12964a04b083
  | 8 => 0xe816c2b0530560900680300252ca293612c18c1801401a0300380100096c390370600a01302001a030050090062443906f06a0c01302001c0340500900618c1802c0500981001401c0340600a006004000fe0c60c016028
  | 9 => 0x280380680c01402001801000a051d23918c0d41580e01a0300500901000c00a39306318488350560380680c014024040030031b9c20340560500700d018028018010011b57907e0e80e81a82b01c0340600a006bc541238
  | 10 => 0xbe0b01402301a0300500070ca053d9b118c27c36835056038068091b23145988e05a0ac0b00d01601c0200300200237a6b05a0ac0b00d01601c02003002001c2a3918c2101a82b01c0340600a012020018014603184802b
  | 11 => 0x22e3404d8660ba0700680700b1c4fa8d01361741c8230380480880d00e015c3a6a1a02a84d8900ba0e40e012022036381171a23404d839022034038050060045b09b0f21e0348640700dc1982c0460340600616c2ac4d86b
  | 12 => 0x1202101c0230280380680c014020018010000e01a8230400380680c01402404003002530898e20be1341c03301a02c048070091c91b90e1a02f45d89b1021981681c01a7d48f8d015426c3305d0380480680700ae20ce11f
  | 13 => 0x860e0168240460880b00d0031cd7a2362d624c220380440500700d0024087b0bf1541101c83804c0900a00d0100140090b0880e41c0240460600a00e01a02002802002e25a594b21c2582003806a0580700d01802400af3
  | 14 => 0x716bd97aa613086004081c0240340238a5765448e0da1922a82202202404406c765e8a0cd09852dc1f01c022028034009ed244408558aa0be0e41c01602403403c755e84a0220380460880a00e01a01400c7423e24033044
  | 15 => 0x2748870e81342543a84d0720600700d0031e9349b521c3ac5d88f10a1001d83701abe51da041682584404b06a034048050071e63c38c5f0bdd020ce0de1580981101a6c8760bd12a24c440500960b81501102003404c77
  | 16 => 0xa010002fb4785a03f85d09c0640880900e0140247e8fb1f14227d3922c44d80700a01000c7b5f49f8e91ca200308428230300380690d1942b84d07b0ea0981182001c034038050029f8650ae1341ec3a8350460600700d
  | 17 => 0x820740248147a6d8600bc0fe1a83085509c06409807008730db14d1fa3184e8900d81a82e84e08208c02c803dc460590920ea1c83502f02601c0247f478308468880aa1182201502602002afb4785a03285e02803c05807
  | 18 => 0x60017e9050fe1a82b03b0400740c807008002411d72681fc3503d03a064090100080017e2863c432c5e0b21161a81782e03604c0380450a3003505d09c0bc0e0190240440680900e011c6a3d36c4dc768c00f41a83084e
  | 19 => 0x2b42f04686a0c21542303605c0b01281502603c5206d0d40c41602602a0380380600a00c008001482003686a04c0540700c014024030050060049d1051b41a83285e0980ec03804006000eb86a0ca1781d82602402c02804
  | 20 => 0x1e0391d1b81481b435035056038048080060054120533a1a82603706a0ac04804006009410940d41581b83404807408809008008350630aa0c0108200280380580700800c0080036e624af8870d40b01202002202402001
  | 21 => 0x1c018028030020024338f40c78cce13d1ae3485482c02201642a882682a43285e0b60d40e01201000e422ec4666e45483b07004c03804006005c72c447c8c89088d0d41842303504a03e41b8e588a1d191520d41841a825
  | 22 => 0x1fa1fc3a05d09c0640880700a011c82f24808fce60fd13a1b0118170140164448747e8cd028ef0760e80980f00e0112990d1942b85489a04c08c1000e00a005171512564888e0c91562a85485f0440486b8a90f80c416015
  | 23 => 0x3063143985d09c1041781d038064090117186787e8f019e32c58873096128178079126787e8d119e2c4580730d817c2884b05e01ce39852b4340398540a214022043028005c8a3f3ae6e83f85b03a06409010016025c823f
  | 24 => 0xe019c9adc4fe9b5209201021e43981c02401cd610f19823c400730940980700c00c0014525e4104808e8ff11e2283984a08c01cb094b21c2ec498730a81401501102003c02801724a25038f30e61802c8560a814402001
  | 25 => 0xb4114210225a4a2cbd14727839c2284206c0a41100f3b86ecd417a1e238c6a0890b41142102a04406a4648b914bf95e28a508744bf01100e005cab945f4b912108f1141cc25026044038b10b70e61ac2904d0960e407008
  | 26 => 0x10e2041001d0380497b25538e340438810400780e81c024044021c72602d04006f04c0540700a00c01401a8b2f45985708910c1482284204e0880417a2cc3ec448860f21702684505205c050065186ecd417a2543e878889
  | 27 => 0x3b46f07e0ea1c23504b8465c090cde1983263f0750d81a83202304548890cde1983263f0750e11b03506404608a04d6fa713c86804986709a1142002a04e05ce399e31a2544986f0a81402182a02000da935138e54c738d0
  | 28 => 0x43e3f06e0d80ce16826845054001cb21f3783f0750d81902243d05a08a109140fc1d4320568a310c17022817014021bba8d412768de13c1f83a86c0d408a03e47a282523f0750c80b81482284207a0680180091d23546a09
  | 29 => 0x18e2e43a8570ac1502884303c0109c0db1a233c638750ae1582a05109210c1101e37a3a8708db0b81681f83b03403c020002d02b04f07b0680c8188280420540780c00c0017fa0a4002c45088c10e1d03000c00c00a482bf
  | 30 => 0xea1a0300560a21402182f03c044988750d01802b0540a61442802f04a0880f0041a21bc340600ac150298510a00bc08803922b6cb39441ac2484206405e0700900739066cc318523436c428420800f8110172764e06d8cf
  | 31 => 0xc0158298500860bc12811008e5d642453965682c0540a61402182f04a0740225a34e1602382f04a0840a81301e010014920d01802d8560a814c288500860bc128052ac3444f0680c01582a0530a21402182f044004b0924
  | _ => 0
def ruleIdData4_ : Nat → Nat
  | 0 => 0x1801e83083606a0bc1282101e0100106108e0e81b03505e0941081b02603c013983205081c02f0560941081301e010011812e25688206105e0ac1282103604c021810c21542382f0560941081b02603c013554ca43467068
  | 1 => 0x86e46e0be0b614c2602b0300500980300325e4b28f37243c5088c0941200c00c0052564a39a2483382f05d0ac0f40e80400324d039811862881a82b02603c02002002e65472713c8484610be09011c17804004e3502947
  | 2 => 0x18018012bd2fe5a4968750a814c2804303a0440216925a1fc3a85d0ac15029843082074088040032664c3432644b4508680c014c25048086e715e1b02fc3985c0aa1241f4340600a6e6ce51ba2fc3c46787f0d014c23013
  | 3 => 0x4bc420310580540700c014020028030040040039e3e03604f86508a0e81702a04e05c058050007c0690ce0b8168228420740d81502903403c0039d4d06c0c30e61701f42c05308e11811acc4007305088c10e1d00c010
  | 4 => 0x1269058941202101b81d0220400600a0123f8420660c60c01001401c03005007006004000871081c81b8200220400600a01201c029f32d64a04f8840620940a80c014018003803c22104181501c0300500800a00c01001
  | 5 => 0x240478840d2198250400700dc1982301801c000a31080e0190230280380600a01000c01001000e1940a7b36227c480840da0ac0a00e000e10630840560500700c014020018010008c07f0901081981580c01402001801
  | 6 => 0xe630520800da0c41301501c024040060060040049b73ec05802d55207ec6e04507a0a8002733165b4ad9252222100c00c014008002de5ba758d216d2b64446608410609806007000b796e96d2b64a0888bd12c2104180c
  | 7 => 0x2603c0225a2d21c03404708c0941081502603c020020007ac4a07f0d01502984103a0440800b008e85d0303522890ef1db33e2243905a03494d230ca15c2683d82304003803805002c093318c2843486008d08c0940a813
  | 8 => 0x4a06c0a01301e0100149c4cc1842c04606c0d01281b02603c011f62b8494798b81061a434018018008001310d0180288500860400580500800800ba25241a0238460780941081501e010000f91781a02384606409410815
  | 9 => 0x1e010013855289102c0360680940d81301e010012945269145e05808c0d81a02503604c07804004910d38a60f61601a83404a06c0a01301e010010a60b61602303606a0d01281e0360500980f0042984f05808c0d81a834
  | 10 => 0x748c111f0e71781842c04708c094078024884cc818ce14c1601a83404a0740d8130085bc908c21782e05308b0b01181a01b026010013a330e34c5309e0b01181b03506806c0980f00461caa0a60b01181b0350680940d813
  | 11 => 0x746c1580a9430e4942c04606c0d00980268c790690a60f41602303606a0d01280f0080096a1871f43085305808c0d81a01300800a4eba63c82983d05808c0d81a83404a03c0200274a7907308d0f41602383504a03c02002
  | 12 => 0x6e2830ae8f11c231c4a04103c0400580952a2982c0460780d81a8340640940d81301e0124f3a22e25a43b846078094108150260109b8f91cc3085c0890fa1942c05508e118020025183e87c8e61842844485809011c23002
  | 13 => 0x2c82443704207c09c0f81a02e03005008006001cc1711e23206188d08a0ac0d017026020ba1121e23842282b04e0780d0170160200180093ee9c890f40920f41582703402c018002243604f84504e0780d01702a02c02800
  | 14 => 0x7a09c0f01a016020018005d6590b004907c09c0f81e03405c05808006000a70490840f01381f03c0680b80b01000c0100060c2642484207c09c0f81e03405c058080060010691b2201242103e04e07c0f01a02e02c04003
  | 15 => 0x7c07c0d0030012854c1ff1741302484207809c0d008006002503a852e1302484207c09c0f81a02e0200180028a388498490841001902a03e06801802000a589d8af0840f81381f03c0680b80b01000c001e515e1242103e
  | 16 => 0xa690695826a1702483d0740d81201a01e0180020d3966cc2e03a06c0d01201a01e018004a2532a59370670981081f01f03405c04003000a5ce287b0b8168260490840f81e81f03400c0029941c6ccba93c0ec16c26042
  | 17 => 0x2925104e0900b80d81702d03403c004a32923244e0670b80b81681a01e01c0030748e5946b8c10f81242103e07a0d80d00f0005245e89c0840b8168270480680b80f01001c000cc1923042e05a0920f81d03605206807806
  | 18 => 0xe7c5189f08a1081d02a04e0680b80b000b094e0e31b027c2e04507409c0d0170160140029c4f84a47189f07a0e81381a016014003082ca5103684907c0f41b01a01e018003a938a5248a89c0ce0b81681a01e01c0029b
  | 19 => 0x1e0240385d09c1041f81d0380640900f01201c032221762543982a0520800e0190240440800b00ae80ed9180f61d42a83a04e0940b81300e740a49181a61701a82e02603c03804002574718d813e1702283a03405c05805
  | 20 => 0x2361942f03f02c0480580700a01001bab490798d790c0ca1781f81602402c02804006a20d797b2181942f03f02c0480580700a01001a0f35e4303285e07e05c0b01201602002804006ea8cd14c1d83902e84e05c0740c811
  | 21 => 0x8c0f0023ac53a23c470650500800580800e00c001291901942403d0560500700b01000c0030a1bc324608650820a40a81401e008001af2743683285e0b61301f82602402401ae15101942f03f0400580900b01001001b09
  | 22 => 0xa010018020020002f02803e05c0b00c01402003003004004004a674e2382f05507a0ac05808006004000be0bc14c2083b05604c0800b00800c00ca594854c980870fe1041081c02203c0130b52463c610b814c2243e865
  | 23 => 0x2c01782d81f03c05c0a00b01001401802002000f28760bc0f40f81702802c02804006008008001321781e03203e05c0a00b010014020030020008d9101321780f81702802c0400500800c0100145e1781d81f02e05805808
  | 24 => 0x1481c03685e03e05c04006006008008005307fcac85e0980f00a00800a00c008001b41d82f05b0980800f814006008008001bc1782d84c03e05c0a00800a010018020020006c8760bc1000f81702802c0280400600800800
  | 25 => 0x2ac4804a0590a810c1101001601c02804006004ab1201281642a0530a210c11010016010018015a0b3ce81cf1a61781a81301e01c0200175a3e46985e07e0b80a01301e01c020014203946b05e03e05c0a00500600800800
  | 26 => 0x2a03c010002aa4f42e8590ac0d01402103a02402802758554518590500800f01d02002c048074d2844e88f20f01641e01d0200180080094e844e89011e43b85f8780b2040030012402502c8550a810c0800b00e01401801
  | 27 => 0x1001802803004004003024620c40a80e0180280380600a00c00800952ebd861ac1320540700c01400c0080033a424618c013e23440046070054098042f64482302b04a0780a81301601c02803950eb8dd9531500f41481b
  | 28 => 0x2001249df2e02d02003102a0380500800a00c0100161a924ef9061680c40a80e01402003005006004b811b0dc0c40a80e01802804005006008008002e04404883102a0380500800c0140180200277ccb83102a0380600a
  | 29 => 0x620540700a010018028030040040010417414c1881501c0300500800c014018010003043703c0620540700c014020028030020014f0e90640c40a80e01802804005006008008003bc4181881501c0300500800c01401802
  | 30 => 0x1c03005005006004880b31322441881501c02804006006004001232363001881501c0300500800c00c010010003a06d0990640c40a80e01802804006006004000e90780c40a81301c0300500800c014018020023a46203c
  | 31 => 0x14020030030040040012f1ca0f01881501c030050050060040011b0ec0c40a80e01802803005006008008007609607c03102a0380600a00c01401802002000b80b40800c40a80e01401401802002001869df20c10018815
  | _ => 0
def ruleIdData5_ : Nat → Nat
  | 0 => 0x6008008002202b0518991220a00a80e014020018015da2b05183c02a0380600a01001401802002000af0b30620540980e018028040060060080095e1661b81901501c0300500800c00c01001000d24af1231800540700c
  | 1 => 0x3a4200370620540600a010018028030040040019b1322441b83102a0280400600a00c008009547844187602a0380600a006008008001662b0518760500540700c014020018020020008d8ac1460f01401501c03005008
  | 2 => 0x1662443783102a0380500800c00c0100100066c918b30de0c40a80e01802804006006008001701682443783102a0380500800a00c0100061a924b80b40de0c40a80e014020028030045785183702a0300500800c00c01001
  | 3 => 0x20006b8c10f80f01b03102a03802803002001d89e123425841815018020028030040008d09912c24437840062054030050060005e8ac12c1001b82802a03001802002000d896d2220c40a80e0180280400600a00c01000
  | 4 => 0x206290368370620540400600a00c010010012b2559031481b41401501c020018010002b0520a30ec1b41401501c02001802002000918f61481d83683102a03803005006008008003a640c6b8ac0f80a00a80e01001802803
  | 5 => 0x1982784b07008e0d81081501e018010001e41c02383c06c0c41282102a03c050060040003803104a0901081802c0540780a010018010004b41c02a84708c0e81282102a04c078021b22903b06d06e0c40a80600a00c01000
  | 6 => 0x780d01882402a03c00800396264380360680c41201501e018008003c02b0540760500901082002a03c04802002000af09e062094120210300580a80f0100180100013c1c03484706c0c41202102a03c03002002000c395e
  | 7 => 0x420540780600400256b0b53e4845e0a511a1842302502a04c0780245a5783084706c0941081501e0180100045a5103806108e0d81882504205407806004000af0c90e0184238360620941081501e018010005804f897870
  | 8 => 0x1201c02804002548580870c60841001102003405807008004002e23a65d0818e51ae1f01880e00c014008005c474cba0e501c0300500800c01401001000d85251e113a20c3683404205407802000c396889e0f61b41a031
  | 9 => 0x6004004af7648484c8300280380600a006004000720aa0d41802e04c0800700c016028048030023d83183004c0800a01302002c02804006004004ae5402381802d0560800980b00800c008870e40dc148210400440800b
  | 10 => 0xc60c0160210400500980e01601c020030022c0318300420800f01401c02c03804006004000fe0cc18c180260420800580700a010018010007f4a50950920c01482703c050058030002683185b0aa1301802104005007007
  | 11 => 0x600a41001e02802c0380500800c008007667089b0ee0e40d418026016014018015eea84180260280380580500800c0080042428c318300580981001401c02c020030020008f0f60e40d4180260400380580900a01001801
  | 12 => 0xc60c01682c04002c0380500800c0080029846c330630600b41000b00e01402003002000f391018a1983183004002c02804006004fe9e62940c01082002802c02003002000fe94a12a0c0148140160140200300200051863
  | 13 => 0x4c0800a00e00e014018010005483905b0980d4180260420800700900a00c00a2a17a18c1802d0400780580700a00c008003fa528628660600b40580500800c008003ce2f4330630600b41001e01601c02003002000a7866
  | 14 => 0x2603c038040003bc4d06307e0ec1802d0500600b00f00e004004b07645643304c0600b416005006004000da1601983185b0980c0168260400100180100053c6d0930cc18c2603005a08003804006004000b00c616c26030
  | 15 => 0x10014008001602343d8750aa0e8180250420800a01300e010af8c311a1d41d0300580941001402601000a4b1861ec3a85508c0e81802002601c008eb0f61d41d0300520800f01400e014003b41de3b43184707e0ec1802d
  | 16 => 0x1000c01000964db4330370560a00700c0140200180200200258b0c4f42641581401c030050030020011d10c18c0fc1b8350560600700c014020018013a82383b05b0ac14c2602b04004c0180153838c4f8380560500700b
  | 17 => 0x4000c39121661e4158250420780b00b01000c010001b81bc1582103c0600b01401600c010002b23e0470790560840b00b0060080080020c2fc470790b60ac10816016020020030020025996e2343904886f0560500700a
  | 18 => 0x1b80ac10818028038058040060080080027c4246f08e0f20ac1080b01001001802002001879451c41781582503e0780b81401600c010002242cc1582103c0600b00b01000c010002241e41902b0420780c01602602c04003
  | 19 => 0x2000b70a40da1981582801c02001802002001ac2ee4922403784c06c0ac0a00e006009411520ec16c2603505608410009006008009a127c378470790ec16c2602b0060080080061e5141581f02802c0400400600800800
  | 20 => 0x180280480237c2643b85003e0740e0110200300500900a00a5b3b776a9ccb69111061b4040030040025abb671ec41469df2e850c9f08e0f2004b714307e0ec1a02d0560a01200f0020025a3b52062903682b05003804003
  | 21 => 0x2e04c059402263fc5f06b0a60cc0d81702602c0216a21430c5b0790ee1400f81c0160100100038c404760b412c1400f811020024028020ee1902803203e0740e014020030050050040004f0910ee1d02801f03a07008810
  | 22 => 0x1320ec0f81b0300580600a01000c010010003102001f0360600b01401802804003004004002851320f00f81b0300580a00c01402001801000b04ba01f0360600b0140260300500800600800cb759c774898f10be1141501b
  | 23 => 0x3e0780d81802c0500580800a00c010001442582001f0360580a00c0060080080012c0940f81b0300580a00c01402001802002001428910de07c0d81802c0500500800a00c010001442640f81b02c0500600a01000c00800
  | 24 => 0x1000c002101ac0ec1702d0360600b008006004004b8770c457c0a80de07c0d8140060080007b0e01301a01f03605002003004004001451c42f44984005407c0d814006008002561c42fc510930de07c0d81401000c00025
  | 25 => 0x30058032983f04bc800690800f01981b02c0300009911e1a42003b06607c0d81802c030003b92f23e03583305007c0d81802c04c0600a0041ac1982803e06c0c0160180280480800c008004ba972edd842f35440940d814
  | 26 => 0x16008002231c42d0510690800ec1981f0360080018e19a244370690800cc0f81b03005806002000794348480800d01981b02c0300300200046c748690901001981f0360600b00c00c00800179132244348480800cc0f81b
  | 27 => 0xee8e90cd0e01201a03303e06c020020004b85e89311e0ec1982e05a06c0b0070080007c06b0be0ec1981f0360600700b010010010002801ac2f83303e06c0c01702c02c04004004000b60f80760cc1901f03c06c0c016
  | 28 => 0xe01b42404006607c0d81800c0080031132230c610a811e1f82d83b06607c0d802000c24eb13a1f03346183303e06c0b816008008000f819a30c478480760cc0f81b03005802002000ee86f0cd0b61202003303e06c0c002
  | 29 => 0x260100129f39e5b08408b08e0ec1902a04206c0015414a2303e06106c0940d81401e008002471ae2943e0360680940d81401e008001a90740901081b0300580a00f0100080007008e0e81b02504206c0a00f014008000a4
  | 30 => 0x5a0900d81600e0013f1d81160fc1702403605c0b012012020f68ab1160fc1701b02e0580900901001c0311c1762584908b0940fc1702d05406c0491c1762ac4585f07e0b81501b02402804a9f39e5b08408b08e0ec1081b
  | 31 => 0x6806c09806004001d6b092743e46988b07e0b80d81300e0108e0921161903084a07e0b80d81200e0108e0d61923045588b0b40fc1b02e0360480480760e91c908c11702944587c06806c01000976c497e2861c822c1f82e
  | _ => 0
def ruleIdData6_ : Nat → Nat
  | 0 => 0x660b00580900e01130a604be5a85b0b01362483f04a04c010003684c097cc88b61362483f04a05801c020007767dcb790614a2243e8610760880d80c610510908b814a22c36834036018010002a8484528a111822c3e048
  | 1 => 0x2804803805978d318999217e1101c8380480880a00e00a004800cd0dc1a4250400700dc19823018008000d70f80f01c023028038040050060040022a1320e01181401c0300500800a00c01001000598b11131561ac2f838
  | 2 => 0x4805004005002a0c220430780e41c0240460880a00e00a00800a5417e1101c83804808c1101401c020028015469a4810440780e41c024028038040015949a8550440720e01201401c014010012041101f83907009011816
  | 3 => 0x280080094d0880f01c8380520901182202e05007005002988d08aa0ec1101e03907009011014010014009021ec2cc550440720e0120140100080093622e42c5f8b30880e41c0240280200093622e4085f8aa0880f01c838
  | 4 => 0x2121ac2f8390460880738a4b0684a88da1922a82203c04405000cbe342544959091ca3245504404405000cbd5748b8d592c1bc340550810940ec0912223e42c5f86b0cc17c1c0240460380426226c45c858da0ec1101c024
  | 5 => 0x9a0e41482002003804005002a804106c07e0b01182002e0580901001402003314370650918700d81841e823024040044c03de600910ed1be1982383c044084021ef394598b11081561ec2f85205402403cbf506544a0122
  | 6 => 0x9605c0b01201484c8c8831041b03104b02e0580900a01001c030b61041b01f83305008c0b8160240280400700cb1cda8bd17624c440860540840881001330a60a7a1ee32c4b06e0c412c250160240400394b1d02ec43052
  | 7 => 0x1fc2b44e06c0961280b80a006a90d519d28e30c6007a0ac0a40200200251c931161da3005087a09c11c108040048b50f1371da1e83085a09c0d81a81200b30d1aa132023dc658960c41040b01200e464480820d81882f84d
  | 8 => 0x720d01400e01001801802002ef04e85209a0fc1e03906808c07006006008008530a41341f83c0720d01402301c020030030026505f09d0a41341e82300c01401802002c55529c122a32c5686f0ce0b413817006850b2938
  | 9 => 0x5a08c0c00a0060047b0a51422381c82203003002803004004af90d1341341f8390580981182001c018018012081482683f0720d01182101c0200300300214c2904d0720d01182102c03804006006008008b70c41482684b
  | 10 => 0x1041b02f83f06608c0b816024028570820a40fc1181801c0200280300400585aa754c3885a0960de07c0a003004001df3bd1f63706309d07e08c0700b0060047f0fb16614c2903f0680a0118080060047d8dc13a2403803f
  | 11 => 0x21e2bc2484207c09c0f81e02e020000eb10a14c2404007e0d019823030038031271d62143e8480800fc19823030038030021f62cc3585207e0d019828046038040020e01b01f83304808c0b81602403c0500800e0193a890
  | 12 => 0x14623c1400e0180200100035843c7b0cc11e1281880e01802003002000ec5159e1358468878cc17a2584180c010008001e135843c6c8cc12c23c4184a01c030040020006b0878760d617c1880e018028040060040018b195
  | 13 => 0x46a6b88a0f710a18824040030038011ae2c03e84b04808007c0c016018008001ae2803e83581f0300580600a0100180100055043c7d8830d61882904b06803804002988654878d911c1281d02d01001c0200035843c660ac
  | 14 => 0x4808c1081802c03c040060023a05d8860c41482683904003c07008002438608750a61482683f0720d00780e0100180099429a2b8268320520901181701e02002802002348570ad1142083384907c0a41382402e03c0436f
  | 15 => 0x132090118210300580a00f0023ec6e0c607e0ec168240460600b00f0026f4b98ca07e0b4140240460600b00f00e01400cc777ea8c650400480840c01601e00800cc698ae99311cb0e00d81a02401e01800aa92082b826839
  | 16 => 0x1a63003d04704203c020020027e4a39261801e83085a07c0a41280f008a98930ef1da3003d06108e0fc1680f009321820ed0f41d82382504203c05006004aa07d8b31060a0120230420600b00f01000800aaa22e3ec6e0bf
  | 17 => 0x257c4d07509a0fc1c82c04606007006003332659ee34c6007688b0c211c10804005329d2ba447c63ca38bf1782783d04701f325531541da1ec3d06106a09407805004f00a39261da1e83084704a0840780400451c930ed
  | 18 => 0x3005806008004f096a9fb31656c9d8f307c0780b80b000908ee95825c370668c607e08c0c00e0093358222133a3004f88d0f41841f825008aa8f30ca1342143d87507e08c0c00e002f05d9b4f1341ec3a83904205803806
  | 19 => 0x1ca378690c91541340300162e4ac690c91821c0238360460840100162ec41391de35a4ac690be1500f01b001212348648c109a0e41182103005804001498570a01250d60a00c016018028040020006186c8cd1420e81101f
  | 20 => 0x15e1101c82904e09011017028016671820921102183e0720a4138240280155588a0de1101c8240440500700800a0090294724c348600a80f41842d825042008b98d21942081f82d0460600b00700a0058b9f83bc4f895909
  | 21 => 0x99ec6155a6d4823d86c8cd094088040023762884506f0880f01c82e048088070085ac87cf41d535a4ac728c90880880a005304538450440800e4148270480880a0055066088588a0880f81c82904e0901101401001561982
  | 22 => 0x14014798d416e2b44505209a1241f03d04e02003003634a31392471f43345c0a51121f0110026324c8850a5142230448810f21dc060025aeaacac0b711e2384504a0800f01b8229a3341e2bc4786c61179ad3483941e022
  | 23 => 0x14a2844607d0d8134250480440600b00c0049d4a18f50d81882f84d04c0880b816024012698820d81882f84b02e0580900a01001de38d21062083603f04605c0b012014020038069a4f198da151202083604d07e05c0b012
  | 24 => 0xd617c2904d0960f411008004f20fd1ab1bc2945088c0fa1f02504808e088014d531e3884607d0d81282403c044060064d41962945088c0fa1b0250480440600b00c004eec830a51442844087d0d818425048044058061b0
  | 25 => 0x6808c0700800c00a6b1331061481f83906808c07008004004999030a41341f8390680a01180e01001801001636854998ba0a41341f83c0720d007006006004ca0be16e1b83585f0a41342583d020020030023285007f8be
  | 26 => 0x720d01100e0104807f8620be1482684b0720dc1a022010018010b70d61882904d0960e41a0320500380400621e2dc3706b0c41482684b0720d01400e010008bd89d0a41341f83906e0d01180600a0085b86b0a41341f839
  | 27 => 0x1000800aac43c588a98e719417c1101602402c043c91b8328618860aa1482682f052080070070026f4b98ca0e01ac3105f0960b41402203002803cd73964cc818a10e00e41a02301001800a4d2722f85b88e0d61482583c
  | 28 => 0x1962582684b094100039b02824e48b0f71962582001702c04803aa42de4dc930ed1cc2243d0470140180117b2e4480808a2114214408790780dc173ca2e449c808a211c228428810900f0173c75503ec4185207e0d01180e
  | 29 => 0x25c4503c86e0c413425840068038013cb15c2884105207e0c81180e01001400a9250c8590a1d21e63ac5b8a21141a41e2923a4474800eb1842e8510860d21180fcda9b33606606209605c0b01201001c031b228a4e47b8e2
  | 30 => 0x6009049988f0c41342583401c02003002360638a093922c4507b885080060070022724507b8a210a1342584a090100070022283dc518850c41342584a0901000c00e004450800f71322143104d0961282003703136d5427a
  | 31 => 0x1cd95269ee1d63885d0a210c214250400446389c9271d628c5108a10a12824040078088071271e63ac710b815e288450850941001e02279649c758ba14422842862090100070069bb371e0b004828c4b69111060d004002
  | _ => 0
def ruleIdData7_ : Nat → Nat
  | 0 => 0x2c030014de1ea1f43105b09a1280b81602403003ba148488d109c83222dc5a072094098113603265389d8f310a19c2484007c09c1101e02eb696ca2b294520498810c41000b012008f31ca2713225208006209a12c25026
  | 1 => 0x1081f81f82c0320440800d0180280480700c0142081e03a0700c8120220400680b01201c028043f44dc528a11181f43e04a09011c110025228e1141b834c410698c21502243e85b0907909b8a51422303e84d09412011018
  | 2 => 0x380440800b0120100100111c1e42d84c0560800700b01001001802002000860ab0c817c1982e03c06c0b0120160240380422a3c84e0670840b81682703c068058070060001f83b038064090110200340580900e01402000
  | 3 => 0xe010b509d0820f40e81c0320480881001a02c0480410e1c81602904007808810016024038050080045703504808c1081802c0500880f0100140100137c1902601c0320480881001a02c0480700a0105387f0e01040f01d
  | 4 => 0x320480881001a02c0480700a0109d06e0d21201981f0360600b816018018010002504042082c038064090110200340580900a010720ac0780a00a81301c030050080060080080042c67c990f51242043104a0820700c812
  | 5 => 0x16024028042f82982784908c1142103e07a0a80f01a02603d162011642703886e0ae1241701a02603c0380614621c3902a0520841001e0220400580900e015bf8ef1641a83185508e0c01781802603c0380437e4308281c
  | 6 => 0x1001d03503704c0540780d0180280300132e5543c0590500980800e01a0300500900c0058e1570820700c8120220400680b01201c028040b60d41301c0320480881001a02c0480700a0118619a3063140e0190240440800d
  | 7 => 0x1602403805008000f197b11a1780f81702804c0580800800c0100129e4283f82e05a0780e01102002c0480700a0105288c1161a42c0480680c80d8130180180100042e584778680c0158298510a010c17825022010a30d1
  | 8 => 0x37e4146d05b0380640881001a02c0480700a010df8ee0820700c8120220400680b00e01402000384670ac8ee038064090110200340580900e0148307e0ee0b00e8190220400680c0140240300530821c390660c60b410010
  | 9 => 0x980d416014024024038050060009a1071b41a82603d06a0980e819024040048043804605906a0bc0d41782e04a04c078070082083604e0820fc1402303a0580900d00e0182604106a0740e0190240400680b01201c02804
  | 10 => 0xa61401782502203c0220a1622844607d0c012014013018018013cd63a9f1072022523f0750d81a832022817001386702ad4c859c8c8cc12220c3204103a030014df4802a44106c04605c0b01201001c0300527a2a43285b
  | 11 => 0x6004000a70fe1040e81c0220400600a012018010490840f81381f03c0680b81301802c050030005806289c12619c1702d04e0780d00b00e00c002182502103981e0380640901102002c0480700a584920ce0d01802b054
  | 12 => 0x16a2684b8720b81301802c04c02c048034804dc930ed1802a43d0610b61682703f024010ff07e0d21201981f0360600b0130180180100063eab95088704c0780881001c02c048050080058f14f0bc0ec1702d02c02c03804
  | 13 => 0x840e81481a02e03c0500079ede49a9291d438c2e04f0840f41d01a006000f88cb164270440710ae0680b81301e020038061fc2804886e0ce1941882c0140180180079c38c6a8b51280c81502904807408810016024ba8c8
  | 14 => 0x160158e1280e80780e0190240440800d01601c028047540b41601e03a0700c8110200340580900a0108f08009e09c1301501c0340600a0120180180164025c2e05a09e1142103a0540a40d01301e0247186e0b816827845
  | 15 => 0x5a0a80f01c0320440800d0120148d84c0760780e0190240400680b00e014020002141300e0190280480800d01602403805008001500640b60700c8120220400680b00e01402000642abd1117d2603b84a81c0320440800d
  | 16 => 0x2003c0680600241c828da0d41942603504c0480680900e01001bd01fe24c4081c0320480881001a02403805009388d18d603c0700c8120220400680b01201c029a30981041f81d03806409011020034058090084a05d893
  | 17 => 0x22010009070d41943203504c0580a012016024028040061d0390350600981000e01a0300580a00800c00a5b10e1c8160280400400680c0140250c99b23c3104002602a0380680a012018018015e29388f0d11001d013015
  | 18 => 0xa61200327943e768de1161f83a86c0d41902182d045026858bd972124228408730961280b01200e2ac468810e61b02f85d0960880b01200f38de528a30c5408e90a11e228430730c011800a8940e540670730c015028850
  | 19 => 0x400272ce43e0624ae8c71721382082903c024e60a11181f43685809011c14018026030030027a44e03f8580ac150298430820bc1281d008620b60b812422c340600a814c288500860bc023d149c2c45088c0fa1d034060
  | 20 => 0x920f81381f03c0680b80b01200c004e63665902103e04e07c0f01a02e02c020030006cc8c03b05c0b41381a01601c020030020010615d18e2e45384908a1041f02a03c0400580934e2983085808c0d41a03204a06c0980f
  | 21 => 0x5a09c0d0070060013716422a3c82e03e04e07c0d01701000c002994dc5d49e0af0ec1302101f03405c04003000c185785c0840a81381f03c0680b80b01000c001791e81242103e07809c0f81e03405c05803000df053897
  | 22 => 0x1e0200311822a3c87789c05c0b41381a00e014018002300f81381f02e0500980b00800c008003662bc1f03a0520a01382403405c0780800c002743d3648a6c8d89c0ce0b81682703401c018009cec8d9114f1e42703382e
  | 23 => 0x14e1fc3a04107607c0f01d0380440800b0040005387f0820f01901e03a07008810016024022b033854c9802e038064090110200340580700a7183f07705c0740c81001a0300500900e018011db2ca460190270420680c013
  | 24 => 0xb20dc1401d0200380600a0120140100149e5184687b0bc0f41d02902804c0780400435c3e0700bc0a00f817006008008002f229c2f03503e05c0a00b01202002003004004e793d14e1fc2083c03a0440800b01201001001
  | 25 => 0xe41a8168200220400580900e014020017a87808689a0ea0a01302002a024009361582903e03605005401802002000f00ac0640a00a80e01802804808006008008003e63103c0740b20dc0e8100180280480600a008aa8d9
  | 26 => 0x1c02c04004006008008007683bc7209a0c60fc1802d02c03c038010004786d0720b61301a83004c08006809006004a60f40de18c180290400780a00b00e0140180016021c390370580800f0110200340580900a010c2087
  | 27 => 0xe010018010004285e8b61261401702d0380440800900e0140210116c1dc348640a00a00f81d038030050020006c8760951261401702d0540780881001201c029a50a01041902a03e07008810016024ea19d11c16c2602b
  | 28 => 0xc0080006b0760cc0f81b02e04c05808008008000ab14e0cc1701e03605c0b0120160240400400453c3583b0660b81681b02c04c0900b00e010000cd1881a42403306407c0d81802c0300300200024c1d82e05a06c0b014
  | 29 => 0x16e2282003e04434857082064090118210300580780800a00800b254e06d4a59482284385d88c0c403c06801174110200390700c81202304405007005002f55e4991200354610380660980200045a2903e04808e0cc0f81b
  | 30 => 0xc61702a8420600b0058030003e05e0b514a288468460640540980f2d02d45305808c0d41a0320360600980f010012754e93783205a8970aa1181601b02603c020a5142214250480800dc110180180096baab45488cac11a
  | 31 => 0x7ac3705a8a213e0ac1502703e02c000e316a27c4b88805609c1200b012015061a52d03545a8940ba13820832054084078094163545a8940640a81481e03a07008810016024640c316a234318420600b01301702603cba8b5
  | _ => 0
def ruleIdData8_ : Nat → Nat
  | 0 => 0x2602c0397a2ec5407d8d1172280430790ae019930d01722803a04f08c1101502603c05581ab14685d86e8a01102182904f07a0c8140062ec4906e8c1140220430520a213c1e80f00d3adeb92119c2d42103205407c0d800
  | 1 => 0x6004cd8b41402444006f04c0540700a0120180180146880ccb1771ba33c5008a10414403806354658bb9281ba304500860a41442480f00e0195898d24844c6e8b914027c15013016ac5281762483746a8b914027c1582a
  | 2 => 0xe215c2904f00c7685d89812e220388670ae13c0d00f3cc5285007a0ea0d81a83005408004b2754e798a50a006a0c01001e016024020030026a4500970e40c01300e018028048033626a4548a01000980a80e01802804806
  | 3 => 0x920d80d01301e019749f12f025c440710ae0680b81301e020038064582cc590971101c4370570920b80d01301e01dec21a1962cc5909c0e21b82b81a02603c03cec2b43a8670980e21602b81a026019941d915a26044086
  | 4 => 0x10ca8bc0981101c42b84903405c0980a01001c034ee3e22203886e0b415c1b02e03404c0780700c5e0590710b415c1b02e03404c0780700c0010093b16425c3886e0ae1241701e03404c078079daca4f89d91641c437057
  | 5 => 0x1e738cc1751301d83885806c0c80d81301e0200339633239c6f89812e1e8388670ae0d8190303e2664b20e71be2c84b8900e215c248360602604b8961101c4338570800c80d0139de7684c0971101c4338570640680980a
  | 6 => 0x10019c2b832026020032ea4f2780bc16324415c2003205004e794f17b2c0d732082ec5408e8f01ba2183c0064402f05308b0b01182003203606009b7821022c2e05a0760c815021036002782432f61d03884908c0980f015
  | 7 => 0x2603c024f73b24d4718db18e1502884f0860bded1881e03846d8cf0ae15027843054ac53b9dd24844c700dd1aa2e4150139ed3d67a1982c64cc6a0bc130160194f34a4664cc1631a82f04c0890b00c80d018630c58b1898
  | 8 => 0x3403c001dc1981702d04f08a1081d02a052068078060007702e04f08a1081d02903405c0980f0140180020c31231c5c84f08a1041502901e024b894619e15c278450840e81502903404c0717c1c22984b84f08c0f41b01a
  | 9 => 0x740a81481a026770278420820e81502903403c070003b87142d04f08a0e81b02903404c078060004d49485c09e0f41d01d03403c030001c21702d04f08a0ec1d02a0520780d00f0013e1bda4b2521702d04f0840e815029
  | 10 => 0x774898e11c03706c04f08a0a81381e02e001ee1011e23806a8b60f019027845054f6cc285a09e1202283806e030030007525947088b09e0e01b8170180180015f0ea13c1d0300580a81482002804cb887b09e1142103d
  | 11 => 0x5008c0680700c005962052ee4a0870b11361480780d002648570ad10c170278450520880b80a656c95259b52904505d88609e1241380f3b842c740ae15a2182e04f08a0a40b80f014021959dd2263c47006609e11415017
  | 12 => 0x7ba93cda0aa0700981200d00c0067d24f28c3f43a0650b61441a82601af757fa4f1fa3383a0650b60980880d4686d0cb1271e02c43004b01a01c03234368658bb8b11041802884b050034038069f280cbb9521622a84d860
  | 13 => 0x9c0ec1781c0320480680700a002802f30ba1381a82f05a0740e0190240440680965a1902e84e0820bc0e81c0320480880d00e0109f9051bc1742702f0500700c812022034048079ff3fa7ecfc65293d1da0436804406cfb
  | 14 => 0x240440800d01602402501564358270410760bc0e81c0320480880d0008489784e07a0bc1201d0380640901101a0240204e07a0bc1402403a0700c81201a024030005a64b06084e07a0bc1201c0320480880d0125809605d
  | 15 => 0x200340600a012018011732001dc160280400640a01001a030050007be23c3c0740580640800d014018028007bca20f19340b60700c8120220400680900e014f497e13a2042081c0320480880d0086282a84e0820740e019
  | 16 => 0xc015058ee18c2743f0190220400680c014024030057c0c64f50830fc0640881001a0300500900aec0e316a1d21f83b81d0320400680c014024011c627e1f81e02c03a0640881001a0300500900cbb43f0770ec14c0e819
  | 17 => 0x320440800d0180280480700c0147487e0dc0b0130190220400680c014024030055003a47407e0320440800d0180280480700c016812b325e3b83f02c0320440800d018028048057be4303f0740580640881001a03005009
  | 18 => 0x220400680b00865c828de1b40700c8120220400680b01201c020e80fc1a43202c0320440800d01801c030053e87acab0640580640881001a0300500700c015f08c61221f81602003a0640881001a0300500918828c3f02c
  | 19 => 0x60a8bc320410760740e0190240400680b0080015a09d0aa1040e81c0320480881001a02c0480463268c4e8740820700c8120220400680b012011581c23383b82081d0380640881001a02c038054043b83a04103a0700c812
  | 20 => 0x320440800d01602403805008c851117d12a0700c8120220400680b0120140250341e4308281c0320440800d01601c0280450a3b86281e038064090110200340580900a011c883d0760740e0190240440800d01602402000
  | 21 => 0x1201c029bf2b22ec1501c0320480881001a02c0480700b4152417d12a0700c8110200340580900e01402372560a009801c0320480881001a02c04805009411f12b03384c06281c0320440800d016014022af2fa3b84a81c
  | 22 => 0xc80700c8140240400680b00e014020002464306001e038064090110200340580900e011501562464300e0190240440800d01601c02804a0f4181681c0320480881001a02c0480700a011691531e80700c8120220400680b
  | 23 => 0x1a02c0480700a000b003b05a0b00e0190240400680b00e0140200037e4146283b0380640901001a02c038050080012419a2203144a83b0380640800d0160140200048a4283202d0380640901001a02c0480700a011f18c5
  | 24 => 0x240440800d00e014020bd12a24c1682a0380640881001a02572a361260b40e0190220400680900e014022af2603b04a82e0540640881001a02c0480700a5581901d0380640901001a02c0280437c580ab81e03806409010
  | 25 => 0xe018001590980ec1601c0320480881001a024028040014205804c038064090110200340480700a011ef1a30aa1300e0190240440800d01201c02804756ad0ac8830980740e0190240440800d0125f4700740c81300e019
  | 26 => 0x2203c069281863002d8350380640901001a025b52103d455c6b01c0320480881001a024038054d88406b0740820ec0e81c0320480881001a001362101ac2742083d03a0700c812022040068093ae6fc5206d0380640800d
  | 27 => 0x24f4548650b61301a82c0240440680900a00c0020f2383b8328170240440680b01001c028040069fcd894418c2404206d09c0740c81101a024df99f09c0700c81302203c06807008d9d972023823b82e84e0480700c812
  | 28 => 0x26dc8f10d0f01641202001a024030012aa1641b82c0500980800d018028048051b23103c0740b20dc1601001a0300500900c014400780b20980a81001c0340600a0120180180143266c8f0780b20740800e01a02804806
  | 29 => 0x2810488800dc0980a80e01a0300500900c00c00abb41e4784007402a0380680c01401801801a12a786208002a0380680c0140240400600600578a4e3c03443a02804c0540800d002844b58780b20dc1a02403a03404806
  | 30 => 0x6004002f94762444006e04c0540680a01200c620ac0580a00a81301c0340600a006004002193c04781401501c03405009006005c106e0620980a80e01a03005009006004002b31d02584006e04c0540700d01802804803
  | 31 => 0x520941001102003405807008005539e629421c0881001a02c048040025ac4f88006c0900a80e01a024030014942b04f8470500900a80e01a0040013623c2904007c04c0540680900c00c0094b1001a41301501c03406006
  | _ => 0
def ruleIdData9_ : Nat → Nat
  | 0 => 0x1aa3144a09303c0440800d0126109f8d51282381681c0200340580900e010000830c60c01300e01a030050030020008f0c40e40d41802601c0340600a01200c008e410e1dc390700c61742702d01a0240380010e1d03902a
  | 1 => 0x23c1f8348380660a01302301c034060060001ac1c03304c08c0700d018028048063ea3405509b0ba0e41601101a014008b61361f8348640700cc1302301c034060065548e4630c40e80d41580e01a03005009006004f38ec
  | 2 => 0x282278418820d81382082303a0580900d00f429dfab5546314480820d81380e81602403402a804762d04b0880960440800d0120157524a3ba56047847062038068060005348006908a1001e03806e0cc1180d01801800219
  | 3 => 0x2203c04b894786304002602c0540700c014024030030029090410e1d02cc4f84006a0380680129a434650ae1341d41302001c03400be068a688268390460380680b006006859b72be328570a91341741602304003402801
  | 4 => 0xee1a83184e02601c0250fa1c8f4db0e40fe1a83084e03205009807009434db0fd0fe1d03505d09c06402804a18f95f232f3002c84486a0b40bc023e465e788778bc1641e83505a05e05c078044786243f8450820a81481c
  | 5 => 0x7b21a82a84e08c0640980700af94f798024237c5906a0b410c17804466788778e41641a8318470600bc0980f00e0108c0ef1782c83505e06a0bc1701b02603c038042302c84406a0aa0d41782502603c039e236c2f059087
  | 6 => 0x400740c8120220240380427a41c8286a0ac0a01202003a0640880900e010a107e0da1a8160190220400480700c016891fc3344d08386a06a064090100160240280420e1a82082603a0700c8120220400580900a01288d10
  | 7 => 0xda1a83286406a0980a00900c014019070d41943204c0580500900500800ce790720a3e4350650980d40900900e0140200321841c350650980f41b03502402c040040066dc8690720a1a81e8260320440480420e1a82b026
  | 8 => 0x240440800b01201c028040e41a82d84c06a0c016026040038048040060050d9971b21e03686a0b20980800900c01400a063f878c9a1070d40d40900900e0140224545c818fe1e326841c35064024044048050087aca107e
  | 9 => 0xfc1941a831058024030050060009e8a90e01942d84c0760500900700a00c0013d152194140160240300500700c00c000d71521f83e02c0320440800900e0180295927a2a42602c03204808810012014968a90ba1380e019
  | 10 => 0x56c2c0318520600800f01401e00400513568901171ea356378550a90240191f9e31522003a03704c0540780c014018008d71522003e02e04c0540700c01402403003002818fe1e327a4d05485b06a048048057cc35c5488f
  | 11 => 0x320440800c0140168bd163885f8780d10e61181c811002f6d44a072a03c0398600a814024004514a110411d1fe2484507308c09800d15a288cccf0d11962c43986c0d617c2582f00eb2ce19931c236c688c717219c2b02a
  | 12 => 0x5470c68c51281cc2a0220220400580700800c00d1b7c44c04a8730540700c81202204005805a34c709407303c0700c8120220400580700a0128cd185ca8d83981c0320480881001601c028047ce888e18e818e2ec3f073
  | 13 => 0x4fa0ca97d2ce55c8c8730940700900732a59c8c8920e61902503b03c070090070080028e9952ce55c8c8931241cc2501c0240240380438c59c8c8cc1241f8398640940b00e80c00c0083986e0a41342583906e0d00e810
  | 14 => 0x2b81cc3584b04c0380600a01201a8fb7d3564b06f0d01021cc0901100a3405d8861021cc3605d07605809005a3c470878ab0e617c130120160240210d1341cc3706b09a12c1c82601c00c720730d61482684b0720d007003
  | 15 => 0x558664738b20aa11c17801a4948e913ea7d0becbe9682323d403d217d2e717f2e12a04e84908a10a05e902162f65c8808ba124228398160248dc65895124234450810e6128168162c4434650ae1341cc3585f096098073c3
  | 16 => 0xb81342280f014018dd9a82f43c44485a08a10c2102a0354a293acb5165e8708db18e1582102a6686e4968fd0d817c2581701402003d26668ccd9920625a3f40b80800e01598b2f512664738b20b41541b02f00349598b30
  | 17 => 0x9210e96bec3265987e0670a4114150270014b19a9db1f83204b82703605c07805a574a946a093783f0750d81a811409d297d6ef9072091f83a86c0d408a0018ea794868387e0ea1c236064017026b50bd1661f62183c86e
  | 18 => 0x28c474670be1621802880500400547a0a33c2c45088c0c01282400c004518798dd19e19c2483e0560780980b4a05986e8ae15a218338520a21141ed307349d0f40dd1a633c670c70a21240f52fa5cfb49c11d1e03746d8cf
  | 19 => 0xb21582a05103001000d314e8851041e823a3fc6d8cf1722704504908cfbdf73364e881ccb1241a226c2884b0460140099e2a04745f0b11101ac2f8520a212c1a032004978cf11d2283c05f0b112414c2584a0900d001333
  | 20 => 0x7a09c04006a68fc8fb8a51181f430832018018003f156e154250380560500580800600299a301fc2444806f056028040030014c9252414505a0a19161982181901837a5a0778ed0c611c1f83001e01c020007e0a1069868
  | 21 => 0xae11c2003226236c678c70a21242183e03c04005d3672e5686d8c70ae15028849086010e493825436c678c70ae1582a05109210c1f01e7e685c9c1151b633c670c713815c2b05108607a9a9c337a3a8708ad10c19c29048
  | 22 => 0x840f81e83603c0680980f41a5f0530970921181a01a02603c025392f8298248460840f81e83603404c0780c0154e1219a82f83c46a0890b41242303e03c04dfa2243b4660c917c1f42604b8320314ddccae04485f04c097
  | 23 => 0xc01582a8540a61442802f04a0110b8ef19e1fc340560a814c2884305e094023200b415c2484207c0e81b02903c0680980f7ecfd59017f2621682484307c0d80f53ba74a50fd97c1901182283d026020d397c29c4ec53046
  | 24 => 0x860bc1282203cfdc988f00d01802b0540a61442802f04a088022c92ac1a0300560a61442804305e0940f00442e3c0778d10d01802b0530a21402182f044010b092419c1a0300560a81442804305e09402002a7891467068
  | 25 => 0x860d81782500800a9f3372d81a0300540a61442182f008724c40f01701a0300500860bc020025f885cc416c1e01a0300540a61402182f008994be9241e01a0300560a81442804305e0940253d5923d0340600ac15028850
  | 26 => 0x2103084585505e0840d818026008378550740d4178210360600980f0041ec2f03d0760e81782902603c02002a7ecb89805d09c0bc1701c0320480880d01201d328600ac1542a0530a21402182f04a088021ec2fe5842c047
  | 27 => 0xc00090517e1cc3085c07d0c011809804005509471b83024b8820c217c22423804a83501fc3592d21dc2c0560a814c2182503a010ba15025a2b84e82f0460840c00a00a00c010017ee2dc1c02f0460840c0140140080098e
  | 28 => 0x380640901101201c02d453d85a49892d2422e023843008008b413125a490340600ac150288500860d0128047f2ccd0b1b919c2f80c00800a00800d4473a9a1289b01702983e84704600aa1a51438828d817e1842e05307d
  | 29 => 0x2ae3b04202d03c0640800b01201c02804334530760a31080b80f01902002c048076b6899058841061f80e8190220400600a012014970dc1202384201d0320400600a000b30e60a11181f42402803004c060027f09182e84e
  | 30 => 0xa8e8605209010e21036810002000d48840c60c41801702a0380600a00e018018007f66c44203104c0540700c01401c03003002001fd24040c7f0ef12c1502101b0120135184205507e0780e0190240440800b01201c029be
  | 31 => 0x55a7c8d2167232330420830c803003aad3e4758b3919198210418640820b00e80c004d39132151342102203c0720e01181401c014008ab1202103585f0700cc1180c014024040071fc2444206f0c60c01000a00e00c00548
  | _ => 0
def ruleIdData10_ : Nat → Nat
  | 0 => 0x20024035496706302081d0380640901102003405809008f0980ab75207ecc59660b41141500056ea40b886508a1041d02a052050002902301702d0450740a81481401e0010c1d62ce55c941191d82f44988405a07804807
  | 1 => 0x1742884908a10a2043f03c05d52d3398d2ac250398540a210c0800b00e01000be648c35c4786506201c03005006002a52460ba1581001d0320480880900eb90c60d211a2202301502601c028014366306c8780da1641301d
  | 2 => 0x10a20434017004ab4ae12519820c3406402e030040022623c0700b60d018028048086010010cf0fe1a02a0530a210c0800b008005121db2ca4f04b8340640a80d81301f531771302383683284c024044038034ce5ecb9101
  | 3 => 0x95395c08c0de1842c0350360600a01301e00aa69db2781601901b03004c0780800ca4c5e0770b01402301d02603c020026c6cb92c9c82341601a830030008009181181601f03d02603c0600a00c004f49ba30a468808b4
  | 4 => 0x100094aa4d34e2984c85806a0d01281b02603c020025265b04585808c0ec1a02503604c07804004ff1e88a60b01181a83404a06c0980f00800800550a9e4183b05808c0940d80f008001439520b00d41a03204a06c0980f
  | 5 => 0x4a06c0980f008009f61d82d84945308b0b01181a01b026010011a714c2782c04606c0d41a03203604c0780214c1602a84606a0c80d81802603c0400258ea4c5e05808c0c80d81802603c045517faae0460580360600980f
  | 6 => 0x5551feab81ee308460880b01200c002aa6d211f2321781602384606403c022513c82983d0580aa0d41a02501e00928a1c14c1bc2c0550740d40c00f0055492217114c1601a83404a04c020023fc338530580a61181a834
  | 7 => 0x480400580952a2e85305508c0f01a83404a06c0980f0080014a96f1f23985e0890ca11c2303c009555ff1ec3245a4848e91ae1f83e0091f2398610b81121e82c05508e11819004004fb52c9c831c474738c20b01540c016
  | 8 => 0x6000cb84904e07c0d00c01401801802000cb1069e536666c1f03404e0680600a00c00c0015d1c631c5c8a70e8170228410540740800b012830638b914e124228410540780e810016024015564184a4718c818e2e42e03d
  | 9 => 0x1600c003ff3a025c2482e05809c0f01a02602c0380319029c4b85c0a41302283d03402401b6e1881b83484207c09c0f81a02e02003003000a60ff92f07809c0d00c014020018002762442103e04e07c0d01701802804006
  | 10 => 0x2202bc2102703e0780d01702602c04003ab08749d84207c09c0f81e03405c058080060020029a41a5145104908409c0f81e03402c0180060c2e82484207c09c0f81e03405c0980b006002ab94e0921081f02a04e07c0d017
  | 11 => 0x12619c2102e0540680180013819c2103e04e07c0f01a02e04c058080063d04985c0921081f02703e0780d01701600c002eb2c02bc2102703e0780d017016020018001741081f03204e07c0f01a02e04c058080060014d11b
  | 12 => 0x1382543382e05a09c0d008006001b99151e42704803d05c0b41381a02e0200180052e2bc3d85c0981081e81f03400c002992ea4f0578a712e1d82603e03402401ba815e1302484207c09c0f81a02e04c040030006c871095
  | 13 => 0x6002acc0153619c1702d04e06803803000c90f39152203144e06705c09c0d003646c89071c029e2702e01a00e00c00323644838b20fe05c0b41301a006001f99151e42cc4e06705c0b41602703401c018005c6454790c6
  | 14 => 0x2761081f03a05209c1201a02e03c04006000a58370490840f81d02904e0900d01701e0200014e2761b83485c0b40f81d03605206807806000350648c115e1702d03a06c0a40d00f01401800324544a6cdc09c0b80b40d008
  | 15 => 0xdc1701e83605c0b41201a01e001c1af039c594a904907c0f41b01a01e0280300038a1682483e0740d81481a02603c031c529c2bc2e05a0921081d0360520780d00f0002bc4184207c0e8148270480680b80f0100180014e
  | 16 => 0x5c0b00c811020028030056286dc4e87f0e00f41a8190240240232c2300f81381f02e03005003002002adbd22ca52c22841054074088100175698aaa550c4545b82d04e0680b807626a2cc792a1e62fc5a0890440680a149
  | 17 => 0x2002c0480700ab8ccd14c2183b0170190220400580900e0140255c564510980550820b80e0190240440800d0162c03303f0380640901102002c0480700a0100035a6048c44207e0320440800c0140240380600af84980b4
  | 18 => 0x2401c0255f33e3d4490810c41402501e0380640900700957aae9d728440c3682803a064080002983b03a0660980b80c81102002c03805008000f394c1d83142602e0320440800b01201c02804642abc7602e0540780c811
  | 19 => 0x1fc3c83286305208003805006002b01e72e6400790e40ca08003803000514710af0ca07c0f01702803805808006000d79830ec1942f05a07e0900900f002f40ce0ff1d82484084a05c064038042864587f8f50c41280c816
  | 20 => 0x5008b090414e1fc2081d0220400780b01201000d626609bce80d31781943105b09011d942872e22e03282103004c0700800d5854394514a1941a83202603c0700822a4487f0f20ca0b013020010014018005b05308a912
  | 21 => 0xa0112da181d829c3f84103c07408810016024020020fe1041d81f03a0700800b0080080031127629c3f84107c0780e01102002c0480400453c3f83b05c0b40f01c02002c038050080010c1702022d05387f0d219020810
  | 22 => 0x120180121b0fe1c03684105007c0e8100040010d8d714e1fc3e0700da1041401d020024030021b229c3f84c0820740e01102002c04804005008b090414e1fc3a04308207408810016010009c029e1fc3801102002c04807
  | 23 => 0x3e0780b81602802c040030007385389e0fe1902e85607a0740e011012018013b85f0810b50a80fe1381702d0220251b87f0e01382082e05a0740480700d00e008830fe1b43204103e0740800214e2903f8700da1040e810
  | 24 => 0x16020020030022e82f05b03e05c0a013016020020030040040005e0aa0f01901f03c05c0a00b01000c008002fa3d02f05506407c0b81401602001802002001cf2b70bc0f81e02503e0780b81401600c000e20bc0f019025
  | 25 => 0x2c03c04002002000538760bc16c26035040024018020021782a84c03e05c0a01301001001802002000888930bc07c0f01702802c0400400600800800ac69cc2f01f02e04c0580800800c010010004102f03c03e05c0a013
  | 26 => 0x3e0740e0100180280100029e3bc7205e07e0b81201601e01c0008d0de1782a83a05205c0a01301e008e70a80f61781e83a0640a40a01301e010010003c43903785e0740a41201702603c040020001b82f03a0520a012017
  | 27 => 0xc014010e91741e02c8370640740800c01402403005566a78740780b20dc1901d0200300500900a0084c8780e81b82c83c06e0740800c0140240300532e4183c05906e0740800c01402403005004004720910ee16428028
  | 28 => 0x17a1b82c8370620740800c014024028020007c8620800b20dc0e8100180280480600a0099c9010f01b82c8370640400600a0120180280227e3003c0740b20dc0e81001802804806004404620780b20f01b81d02003005009
  | 29 => 0x58a2903e0780c81642702403a0240300500435c3e0780b20f01b81d020024030050f01a43205906e0c80e81001801802802234258488780dc1641b81d0200300500900a008f913f1461641b83203a0400600a012018011f2
  | 30 => 0x6005270800e81741301502001802803002f51509b72aa4342e85905009804801aca6dcaf9551602a42e8590ac0b014020012004aa89e0f01742c8560520a01001d01201c03001ac8c38888780da1642701d01201801381
  | 31 => 0x4ae390560400500540700c01400c010010002003702e04c0540700c01402401801ad95aeb5569ad159c1701501802803803002002b31f621240c1881501c0300500800c00c0080023c3104006e07e0980a80e01802804806
  | _ => 0
def ruleIdData11_ : Nat → Nat
  | 0 => 0x780c40a80e014020030030003105603c0500540980e01802804003002002b70ba1580c81401501c030050080060040056d20c3105602802a0380600a01000c010010005e4720ac1320a00a80e0180280400300400400404
  | 1 => 0xf80f01401501c02001801000390560960d21001401501c030040030040040011a1c82b04886e07c0c40a80a0100140180200083c3c03702a0300500800c014018022dc5b4888ac0cc0ac14015018028040030040005a06f
  | 2 => 0x780d01081501e018001a511a0c81882102e0540980f01001a02ae931e2884686f0aa1181e01501f015288a51442343785502a04c078023f04f86f0ac0500900a80f0040040056f6744784001501c024030050060046b8ac
  | 3 => 0xaa0a41001e0220400580900e01000d73ae421c318550580800881001601c020010015c6b83ae4a8534a10ca0780380400533a5ac9a89f0620901001500c004001541582783e07b0680a01081502603c0100078cb452b86d
  | 4 => 0xaa0dc150290400440800b01201cf39841b221c3902d0400400580900e014022f754221c3302602002c02804002001090870e81c8160210400440800b01201c0200110e1983182a0520800800b00e014020010002c043872
  | 5 => 0xe415426035060080048070060051b08e0aa0e81802d01601401801000e1d7b23e1a021c3d02003a048088044c6958498870e40b0150200220400580900e014c20f410e1d03902104007808810016024038052ba3d043872
  | 6 => 0x600b014820028038058070060040033b3ca0d01801401c02c020030020007f0b00cc18c1802c0520800a00b00800c0080080c3f87a0660c61541802002802c03803002000318300580a41382003c0500980b00800c0089a
  | 7 => 0x58080058070060040026337a5f4330630600800f00b00e010018010015d1539e62940d41802003c02c048040060059e0740e40d4180260400780580900a010018013aa2c0330630600b41602002802c0200300200031855
  | 8 => 0xe0140180016028c338630600a81482003c05005807006000bc9621601983183005a02c020030035d4e80660c60c01682002602c03804006004000660c616c1802d04c0800980b00e010018010003d0330630b61541802d
  | 9 => 0x5a0600b00f0022c04d06307e0c01682802c03c008000cc18c2603005a0800980700800c008660c616c2a84c0600b41302000e00c00800aed01c3185b0980c01602002803803803002001259351e818c1802c0400780a00b
  | 10 => 0x40040015d1b82503b8320540a40e0100160018293f12820c3203703a0400600a004664738df11a1bc2a8440600500400211a1ec3a8550740c01482002804c03afa21a1d41d0350600981001e00a002bb91018a26831830
  | 11 => 0x60080080061e5147103205607c0f01401600c001cd2242cc3c8320560a40f016016020018002944d4890af0f20ac1482703c05805808006001e73bd34a38c6a87005605c058090065b8830fe1c81981582801c03005003
  | 12 => 0x1ec2383c82b05202c04004006008008007f8cf44c88e0f20ac0700b01001001802002002bc93620c2383c85b0a60ac0700b01000c008002202383c8760780ac0700b01001001802002002bc1cd1662383c82b01c02c04004
  | 13 => 0x11c16c2602b01000c010010015eebd1d41ec2382d84c056038020030040040026b3521e41581e01c02c0400300400135a493624483c86f0560780700b01000c0100039a6f45988e0ec0b41582001602002003002000e6906
  | 14 => 0x67c7e0b893e0740ac0a00e0160040057c67a4d01682b040020020030020019e99018616c1580e01000c010010006749b1101ec2383c8760980ac02003004004001d433a2644704c06c0ac07004006008008003a8684b70fe
  | 15 => 0x806f5d5114c0a0074088100126c8760951261401d82e054040028001881dc2801f03a07008810014024013b62e82383c83c01c02c04004002001471f73204105f0a811216c2183b056cc137a011f21882d8430760b415801
  | 16 => 0x3e0705e8b61261401d82e05a07003804000c78eb10a16c24c2802e038024038042142d84985f0a01281702d03802c048070083305b0a70ee1902804105007c0e81c018018013b92f25a85b0770a00a00f81c01802abf57d
  | 17 => 0x1242244087d0ee184280480190255c9ba3105a85385005007001000afebf4e018820a2482801c00e010001ba2d430c5b0a70a01041d81f0380100100043641c5b0a70da1402081c00c008004083743805b0770c81401902a
  | 18 => 0x1882d0348480780cc0f81b030058030002f2334348480660a00f81b0300580980c00c00ac00f81220cc1401f0360600b00c0140080010403e06c0c014026038058040060041902a03e0780d81802c05005808006000830a5
  | 19 => 0x660a00f81b0300580100020c2884c86e0d21201981f036058060060002e0348480780cc0f81b0300580980c00c008000e91d02e8348480660c80f81b03005806006000acd4f0830d21201981f0360600b00c004000ef906
  | 20 => 0x660b80d8160160240380449083ccd0c51562542f83305c06c0b00b012010ec10c1560f41982e03605c0b012016024040044ea3b85585f0800cc1701b02e0580900b012010b603e0760cc1381f03c06c0b81301631034840
  | 21 => 0x2402c021be15617c2603305c0780d81602402c048070096048505f0660b81681b02c0480580900e010a794021417c1982e0360580900b01201c0200037e3145585f0660b80d81602402c04807008000e119c20a3b85585f
  | 22 => 0x3e0780d81802c000820e019a1201b83303e06c0c016026010011b21c42e44a8930f20cc1702a036024850bd1260ec1982e05a06c0b01301201c0231e27424c1d83305c06c0b01201601c02000380500380640be0cc1301b
  | 23 => 0x2401c0040a3b0700828ab0e01301981b01201c0240a3b01ac2d84c0660b81301b0240242f84c0760cc17026036058090040005645585f0980cc1702c0360580900952e3e02603b0660c81381f03605c000e00800ec19832
  | 24 => 0x19a30c2403303e06c0c0160080009d13419a30c1d83303e06c0b816008008001c020e3346183304c06c0b012008001080d61560cc1701b02e058090090106cc6184207c0cc1381f03605c0200059e5006f05f0b61301981b
  | 25 => 0x4206c0c0160267b4b31081bc22c3582804806c0b8090100080021b14e1c03683303605c0480800c009511d82681c01e83303604804808008700839051f230c6103303601c020003743e0618a706606c0b81600800800106
  | 26 => 0x360080011c1160fc1e83605c0900d81201201ac1aa41e22a0458690c80d80d806004598a010811a22c3d83d03604c020028106e88e108116190238320540840dd822384205588b0b40c815021036024840f81161ac19028
  | 27 => 0x1a026c2e83c072074088013fc6b87d0ab0be0cc1701602402c048070087f86206e0d21201981f03005806006004000dd8e61502744483404a0880d80a0047e09f1091bc3481d02403605000800812ae55229f1e22a045828
  | 28 => 0xc0080058649a744758e20780e01981f00c000620380460500980e01802804003004004001131c03083f04a0700cc1300e008000898e016023c3304a0700dc1982c008002c2b8b7106105f89b0d617c2e82303b611519f5
  | 29 => 0x460880280137a47c858b00cc1101c02d04808c1100700a004518440860f01c83804808c1101401c00800aae51c748e51000aa1282303802601ec3ab814a2881c03706a04c07802002c1c800a40f81b42003c0700dc19823
  | 30 => 0x2be4205585f0580a804af54c2894700b60f21c83202c042078039582442dc478660940f01c037046088c91582442dc478660800e01b832046088014002b0488858b711e1982003e0700dc1182200447c330440700b416024
  | 31 => 0x3c0700900900ed750c21337c4c82f81201601c02000426718991011d82483486407807c065891ee32c4b06e0c412c0b01202001d9d1cd1f63706309d07e08c0800b0036210a8c51041b01f81702c0480800a3de7b4e5162
  | _ => 0
def ruleIdData12_ : Nat → Nat
  | 0 => 0x2e83ec6e09d13408c070030027d0a68ae1041581182103a0700c005004878c993722c2a04f0900f41381b012b144dc930ed1161e83085a09c0fc0900500884c990e01862483204a05c07009007008001099be26424c2502e
  | 1 => 0x4e07c0b80c00c002c6b1622a43c4e06705c0b4138070004e47b8cb1382583384b05a09c03803b1962d0a85207e0e41a00e00600800b3f3d06809c0ad1141482483d04e01801a141e62b44504907c05c0700a01000e05af2
  | 2 => 0x4808c0b80f0100180100118c1b01f83b0580901181702c0480780800c348578ae15a2284106705209c1201701e020e894e15c2b44504907c0a41382402e03c0400635c6547d0920c81281701602401c021ae2c83e83483e
  | 3 => 0x1962f45d83f0760b40b01401e0140090e1d0214380690800840c00f004004b994d1940fc1682403005807807002ad50e89910a0e4120230420600b00f01001400c0c5525045709e0de0e4120210300580780800465057029
  | 4 => 0x2fd10f11c1f42ac3e8170240280480781c5609388b10a1282404006408c1081802c00ac72ac1861e82703f06c0800780e008005531932924f09509c1201e81b02d01e534570a304808c1081802c03c040050040060690e
  | 5 => 0x3d46b4ab8810f20f2c7b374980600b00c014024040060049284f84d07e0e414023030038058011e23a0568860ea19c2904d08a0f41380800d03cda94b290450870be1762303104802803d95b254966d4a59482284385d814
  | 6 => 0x1ca34864867292348658ad1382083384b05a09c03a4c2b85009286b02e02c040040040020815c24a1ac1d82d02c02c03804000930ae1250921081f02703c05c05800498570928690900600b00c00c00800591b20f15e2393
  | 7 => 0x5ac6b4d59381ca32422022028016ca3133044082203e0720900a00800b038458820d817c2683f04808c0b816024020038d215c28c410230420600b008004005882723bc6b4d58d217c2a04783c06b64ec937e4287fcd6938
  | 8 => 0x5a08805007634ae5239651f42242484207c088062b95186ec9e12a1f43c4578890920f81126f4548a4990810c21281701c02401e08b3933e4c86b0921202043101c0243cc578ad11419c290440840f41382404405c04595
  | 9 => 0x2402802b123c4504600820d81841f81601401ecb0f31a82dc578ad1141482683d04e02003003386574740dc1b0320568860a41202283d04e020798dd15a228370670a41442483e07a09c110082722dc5689c0dc19c2e04b
  | 10 => 0x7a0c80800800c00800bfa3563d4540810fa1882502c024012cbbc81ea2a03e8620940981101200867c7a8cb1562484086c0c417c2501c02401c020e513a20c4106c07e08c0b816024029de338636854480820d80fc0b816
  | 11 => 0x10004b98e41941c0358620960b40c00a00ecfcf11411de3283803f05a060050072c457c7f89a0d61882684b0720b00310d1342343104d0960e41300e00c004ae88d10c148268390680c81481600c6507f8be0d61482684b
  | 12 => 0x780868d514724c1e82904907c0a41393926e498768e70c21540b812014015f52082e43fc4908a1021f82502e059048bd9721d82e8538a21242184288146e6c8710cb172254468810f212c175984623ec6e09d1201481180e
  | 13 => 0x2904003104d0961281659a3403ac4308508a1001e82704405d159271e63ac710ba1442284284004449c758850dc188258480800c80c00e00c0095298e24e3ac4284b0800f81101701d665381b5290450870bb11e2303104d
  | 14 => 0x22034038057d2a451c1a63024e8820d81a61f42daec376590788d416e0f81382203c05d489e934c4e87a8d30fa1882d85a0246a89b9161ea2a03e86209408809007008b696cad83225204984a0800b41101eb3966de6191
  | 15 => 0xe002ceb1f42465c5007e04c0640800d018028048066807a4eb14322c3d43e8620b4048021e81c236c678c70ae1582a05109e10c1e82a03cfade6a7c412808e69291f83a86a0c80ce002061f41041b0270410460740b012
  | 16 => 0x3405c058030004a4890f40740680580800a00c001ed240234408730d617c2e84b0720b011007476444488780dc1641601001a0300500900c3a4630901081f81001d0320440800d01802804b122583902e84e05e0700c80d
  | 17 => 0x1602401d9f7e4d5193a112d62d42c80900c7543906306a0c01602003c0500580900a00c000870e81c82a82c0520800f01102002c0480700304d4e8720ca0d41802a04c0800580901001401d9e53aa585104207c09c0f81e
  | 18 => 0x4a06a8bb0dd140220430520a20f41900700c9410e1761ba3545002b05402c03bcf63a764bb0e31ba2e45005009f682093d61aa2d44a05605405c05a0916a25c3905c0980c0160090065d4640b916a21c3905d0aa13016010
  | 19 => 0xae0680980f01401c031f02f04ec590971101c42b81a02603c03806352320580a010e1c83802c04007808810016026d132632e2803281e01c02c04803b42310500690ca0980700600600194ae63b23d06e8d319c2e450013
  | 20 => 0x2c62e84f88610015c035a7b4cca0cc17a2c63044c089101696d22324346a8cc9981a82c803da34281d0388650920980f00f01cdd1738e7164270480710ae0d81832a1962603886e0ae0680980a00eca8bc17012a22038869
  | 21 => 0x10408c0680700c004c4935252320638b909e1381e8097ecfd4bf93109e1142183d06c0a8e49311b631c2b05109e1142183d0549410b8e11b631c5c8560a81442784307a0a80227840044c700c80ce17019826000c2921178
  | 22 => 0x18c2444807e03a0640881001a03005009b5aac86b04e05e0700c81101a01ed65ab670ac8a20d609c1041781c0320480880d66cc99270d10e80980c80d00a00ed52f53004e8698cf16224806804b536a1021b425c2c44d88f
  | 23 => 0x220400680965a1902601c0320400680700a011f1baf65a314320410380640901001a02c02be717a2ec4b07e0320440800d01802402ac627e2380c81001a030050070006f8ab8c60fc0d41601d0320400680c01402402983
  | 24 => 0x5c06c09807008ad4fa14d1602083604e07e08c0b01201a01c02db03e868c628b01041b02702302c0480680700b6bed732716021c3904e0480800f00d0120059c9e9284480478810f806406805808b4d360d60820700c812
  | 25 => 0x33a0d41580f012ad90c9a223c1c81a83004003c04db37f29eca88a906e0500600300280cdc9b41622a44d83805008c0700d00e01800db2b62cc87e8a90d808c0880f0146e0a107e0da1a81a81d03204004a3d17822c3502f
  | 26 => 0xa211421810016012dba1c2ee518658b10e601c02801b6c8d4cf0fd1a2314588730d817c2582f00f6d5a0a8f2ce3f47a8cf0e617c025b4682bfcdb19e1fa1cc0c80700a70cb58e811a2182683904e02c00c0b56caa91ca19
  | 27 => 0x6c8990a08fd19e2c43e86c00f6f2ddb34664a3c7e8f50be16c0bdba662ab11e9b63323d47385a0aabf9269502283cc780b111012c00db94fe3fc490810fc1cc2502c018f70c692e1c02d839854086098025b82c23544a073
  | 28 => 0x18e2e42b8560a81440f5be81ebf4da948228438750bb01efbdf733640e7a0cb0d10a212c0295023a3c0758be16212c2504806800adec145525048e8f3162148288390680091a98d23a2f8588990d617c290510960d001414
  | 29 => 0x5e0941080f0085345709d05e0840c00a00600800bf04146246886f0c01502882f0436fd9f9a015a2182b85208a0f40321a2f82982304207c0f40d01301ea750d15627036c678c70ae1582a051086078f413822a36c678ce
  | 30 => 0xe01400dc03183d46a8b6136048038040007acc61420da194320260100180192f1462103f02e05806408810018028048055de9204a84107e0780e01902203c0480442c6e45f06b0be148258340640200120528e1e81b032
  | 31 => 0x3403c0016422a3f87903e03e0680b8130062bc2101f03c0680b81301c02c040035347942e04207a0780d00b006002e1dc2b82a702e03d034018018001e831c5c8af14e1d02e04103c0740800b012918bf97319414811820
  | _ => 0
def ruleIdData13_ : Nat → Nat
  | 0 => 0x220400580900e670a60ec0aa1302082e0320440800b01201c022263d62103f0740c80740c81102003005005005711e9b3562aa951d2383a06e09e0971121240d36c5e05943483e07a068078060005387185c0b41081d029
  | 1 => 0x2601d6813d11a1942d8140260480780762873c839050ca0a01200f01201c860c60fc1941f835018028040036348a4cf93f264248408610940700c81200e530760b00980b80c811020024025c7b8d7160982904c0800e819
  | 2 => 0x12018012dc39c5c85387f0c81581e81d038044030040044f4960c114e1fc2e85607a0a00f81d0120080014f27a3903f8700ba1381702802202403dcbb957259d87f0540440800b01201402001b90ab90d0a30f61d432846
  | 3 => 0xd01caa8870e41742c8560aa0a41402002202403dcf6746943c0700b20f40800900d7390e1460bc0e81481700c00800dcd73667c788810fe1040f01c0057319f2b4422754c487f0ba07408809002c385387f0ec1b42b03d
  | 4 => 0xacecf28870e40d0150260400780881001602402dd26783d0438720580a41001102002c0480700b0187a0870e40981001102002c04807008006e8dd05f28846309102a0280480336e57caa8b513c1e02e8590580a010009
  | 5 => 0x220400580900882c6a8940e80800e81102002c04804004004d28e31aa2501e82403a07008810016024008f40e40d41802604002c04805006848700870e4190160290400780881001602403b3c63eab84382603c0440800b
  | 6 => 0x440200325e2e65886506b0be1482580e00f751b596727e4646601d018008005d34c097c5b09b124154250070004107f0b311c1e41581301602002003004005ff33e4226249f0940ba074088094164106a8940e80dc0f01d
  | 7 => 0x2383e84906109408809007bab0419b8ab0e017c0900a01201cac14d116214240400460840c01600c0095a90415c090118210300580a00f01000800c0d29232c5d8860ce1081682701e590a710f1e62b4450520920f81e827
  | 8 => 0x4807408810016025852293d250c8b07d0c216809006bb1055cab4044e8087a87d0240120ac1168089cf48d60fa1882d0122402344086b0be1742583c0720dc1901dbaf759ec1392662b44e0900b812c1680a01001d1499f
  | 9 => 0x1141482884907aad8580870e81c82b02c04007808810016025019b92ee2a44d82804601c00b4128c3f43a01902203403804bb2f69eaa782ea3205b02c000871019962ee5186e8a01142202480700cfc4718d51722d44a055
  | 10 => 0x176cca15017c1ac2904b07a075ffb354748e0dc13c12e2240d5da7f68984207e04c06408810014024033925525408e8be162220358520a212c1c83429c3cc6e8ad
  | _ => 0
def ruleIdData (i : Nat) : Nat :=
  match i/32 with
  | 0 => ruleIdData0_ (i % 32)
  | 1 => ruleIdData1_ (i % 32)
  | 2 => ruleIdData2_ (i % 32)
  | 3 => ruleIdData3_ (i % 32)
  | 4 => ruleIdData4_ (i % 32)
  | 5 => ruleIdData5_ (i % 32)
  | 6 => ruleIdData6_ (i % 32)
  | 7 => ruleIdData7_ (i % 32)
  | 8 => ruleIdData8_ (i % 32)
  | 9 => ruleIdData9_ (i % 32)
  | 10 => ruleIdData10_ (i % 32)
  | 11 => ruleIdData11_ (i % 32)
  | 12 => ruleIdData12_ (i % 32)
  | 13 => ruleIdData13_ (i % 32)
  | _ => 0
def ruleId (i : Nat) : Nat := (ruleIdData (i/64) >>> (11*(i % 64))) &&& 2047
def ruleWordData : Nat → Nat
  | 0 => 0x21135421aac00099554872b0040160024288009808008822001264002993800c4180024ca00124121d43ac0124180090020012600010a1a92d4ce8f751100490135d114c008414f56c3700022323dd4c4018410000284946112ddb8cb40084540002b000214535d914c01449c002246004011002000800900400244a000225000911801180400820c96b771d25a81c0084180004420003410001320008440c76449000b220001912ca58c600a44e47b528bd5b05c020424d568330002415421bac0044116f2ce3
  | 1 => 0x2501000b1a0015020c773090055274c5903c02182400520c0011250028a38001d052d6463002410002b1c00184000024c60041045b3d05d8ee6920048040012040030880018c8800516000800900208b00110056f2cc3005148001209800005000204a00820900228080004880004c65ab419800192800980400d160000260000290ad1a8670d6ec3aa13b5800291001409c0040220001100001908008a2c00148494677280420480180100030a800132531ddc34d2a15600172271bb96802003000049400c44e
  | 2 => 0x8a439580120a80208e400602c37a528a1d54ac00801800d0a80002460009108004400c7244900822b335a9840048816a8e5144a855801429000800800942c0022064a28894020440002a460026350002b3000a1cc00c2280082690021128018050004200000a4100408500144200060080024110003911a10dd6ccaa6100300600199111e94a2005202003b2200120318dc892976a5500160400220b00008d8002ac80013414cb3d14000d18004c6400280144b3d1400958800436079b65b8001a12edc61a00720c
  | 3 => 0x22600011a292d4020014200029020020588006e0c00e44e0033420004b2000285164d6530022450005c1000981400c04e003104094b18c005c8c008246006522000c281e6d82ed54c1798620780130a8014a1d6cf437a26b29802111812a15600d64400074600094180008800110b2002850004884800455000520a00038235da3cc0218e400a0100000b90001c88000088001702000025000548801101800a64400243200140100006496ad43300200124dc2d51dd4a364c6490001b9001a031aad82e016212
  | 4 => 0x812b00408a800460c000a46006054000a82000890d5026ab0024570003b20018414000f52000376001058a12dd86a52c634ab60b800c820005e800003040086020040050d1a1566f6a510063420029a380242c427556b00a109000dc88018c9c00482c0012465d23cc4008188002c46b7467180213200148840086029431128011c596de612006a44004a110024db001c550ae8ce30052414230894016a5d648c631b419680100b2a84e560091620016634421bad92d40f54876ba81375dda0cb401849c003008
  | 5 => 0x581000dc01aa906600d0a000026600030805d19c6aacc61a6b530d32a9840001600005220054180030910001504f54c170066040040a5801499000c40800823b00389380222c00022a0002451001102800a14c00800800660000012c21ac8c600816c005a8700250300004540165220052910008328ead06600c2840021565bc330c00a858002eca6b92298002b200250448d50eb64b533a1d42ad86504b48ea67000441000134000840c005064002857000020800c8940006e8001b2300008a1119dca00840c
  | 6 => 0x84b50380105b2d690ce0160120048560012830004a007370b50007210008b0000c9a14d6a81001004524a99c01c410010814003506005920a655e8a008ca20084020003928024410001706bb6386805a0480044140102b2b5a4038043958002d9000500a0005360010458016c9d092a07634224b23a81de6ee1a000ac00001540014d88016c88004a04000b250051138001160016c12002a9300242a00201a400c360009851000bb0000a144002a4200615400043b001851000422c5246318024d8802e16531622f
  | 7 => 0x28500218880185206f7511009051000cc18001c8c00250a001b85003911aed061a0043160072640015032d598c200036000481100340200018880100220016640028c38000c982950ab647533d2a39440185140046ee0002815b350cc01255800742c1796719d5b05c0069055068aba65533ccdbd0c00019400640c0019a30042848020414012c1200790600329399e668b4d6a670017a30003b28000a28003340006115000ba089add8600c6880026100020928001d8c87152b0004101d4a0cd2e54aa00c286
  | 8 => 0xa11000041b192d40200a220004234005b1d00258e80001740031221bb29459e51ca008046a4b53080103380091cc0102940041560bdd444005d8c0001680088090020db000984c00542a0033ab25dc15400a018001160004604294318c00e018002c00000b2300140990da1d72caee30051145a3504d96c89200e24684b2318011b12519c4ab6c70900b2215d23c44002c8400af521246318048049a10d5600024600018a0014382d5686600d7040042600042008005c948ef5310005420001b28020cac00a030
  | 9 => 0x24b11baa94400a84000d20a0068745b3cadc00258000300000290000140000148202750ab007156000bd2a61c8de0106d2001346000141a655eca00a3720044b600023b000a69c00c80c0024b000185b000aac00050208495338023010001960000312001b21001120802499000d00000123400198b2498c9200a32e0048061dc914e61481eb6832d00079100102b98d6e1a000ee00015203359124010994004c8a00223500413595e59c7488a070095640040d80018418c7774d0060060014b10009948000702
  | 10 => 0x389004305000421447770d17ba988042088001e9576c70900526300588819a504a00030a4a960bdbcb18d5698c2d52833a4950380033c001d9900052ae0044b15c24ad51aa156010cb20066380011b3800900c004b1651941280333980011e02f6a510073275b3c85d6ec8920042845b79a4a2342ad6ec92601028a6bb249804802001aac000aacc0015660025c1800c2ec00a36098b20180045c8000e6801464e000b85003011001a8508d6463665534801c0200002d800248000a287004b1c80006688f5511
  | 11 => 0x21002208000558c0070a8b55400803391000c990772893007148000393000a04400088c3ba86a8cdc2d40088d972c7490011b035ca24d2ad86e000732004056002308a655e86cc0a610007445ad3184ee08a600682ca44533804b00986ee1b0ccee5000810004b28801e55800a24400a4090014b3a6188de00900800bb91004cd8801488c00a682b46b79b5c114c00149c0102260081430000a1801d158015160865761a0ddcb6a04ed6000eec001235000cb20005d90774a559961b280008991addc600270a
  | 12 => 0x524824dc2ac01d059692c6347ba85800541002861d7148070080b1002110000a40c0108209457718008c00019040007428002357000058ada900ed56c370085690040dc80118c893556b63472880331a001a4e0000ee8000b922dbcca691d40e000f40007638425a99c012c89650c630002270000ca002849c00b72200328b0020288000d1000c226000962535a81c01c51c000b040085390008841ea582e0002ac00432500429d801141800eac80063822dd914c018558004cae43aab58010c98014e4400aa44
  | 13 => 0x64b5308040012255e8a00e00c33a8558003d18010008002400009001003480066aad6b693090b4984a3b294400a6d80048000023a7393192402c52c00aac80074b62dda3cc02654400480a954b2a8009b28009d1400008462980780400d001561c000b12a8335580320a80099cc00e16c0021085c2595402c9800130b2465771802a90a1ac98600548468345580240b0005d18004ca2443112bbddc34006c946328250031580014ab002856511440f94011280405b802ae1c00a10e83b7a18025588004480014a12
  | 14 => 0x72983780014d0002a48d128250018640035210a10dd60066f0006774004c8080299ec000f040007580050a40010550f34c1717bb86800c00a1ad4ce0042967547288018928000510d564930066053521daccc6e1a00b70e0050b4001a8b000980c005006002a050049418006e800055220055084ad918c00cd04008a2c000a8124ddc340010d800d52e005b8123343ac000e940023400a9419c4511beca601e006044001b81004b01000c44036830d41bb8680542c800c558014294b96384801d0325add86d36cb7
  | 15 => 0xb5a6338008c28010050d026eb67b2248003c28000244016f40411b9680442800200040166825b72848011cd802c5402d50ab0022403ad21840115900167220005630013310001498af0cc337aa88a9dcc24018c1000d0206bb419a3aa9440118d0534c1753b224855a0cc0002e0005422001a91001458800984401647200326521c43ac001e240122345b79b48011809185dc6001712456112a2543ac00258c006e44001243000c3b001642000880400310800508400219480122a80094b100382b000a62c0164d2
  | 16 => 0x49510058a3802105400ea4e00877b00259280211a400d7280006740022b3001411c000d620074065419bac00a4d50964c3007027001420802d5a4004e8200084100504389ac8c714872500095100509580244ac01221400667431ccc24019d10002f0a008615004549800560c002f06008ba7004c08801851c00ac10008059000b12800658c0104140096340000a28002dd0004c860065380009c8800ee08ce88e50001ba0049048021428002c6a008263004931800e1592c900f0072635519dac015dd11086ab
  | 17 => 0x61500005ccaedc642008220002477000a20800dde0008cee00b12700330a000c6496a9655246112800a232ec861a46370d00a22b25d435402d0280072ac4ba52a800228801009400013284b53080442919e268b4ad653453112d22a99c002918010c64b36b79801bbb04ea1d600a630496ab583b1924001d810c0a67491b86d30298402c89d68f41700228325c295402c52800c400007106003439801a05128f4170030145a4c03c01a55000f40c00867b004c04802456400442a0079b6003282001182000ae82
  | 18 => 0x642004325802104c000962003142001cd518de6920074840048b6002500a284e5600e22c0001160048a5802852c000f500003a8002b0c00208e80144d2007a160021438015058c9300f0006623419baec6605e001022b66a0badd9224eec92764d493683355804dc180082dc016acc00750600431d002d48401404e0094510045480005dc0009160002a450000410014c8400a690006a150005b0002241400b34e0046105bcb3840082180150200015a00bcb30c010a04011420003b2500380b00104d800cc20
  | 19 => 0x3478001aa1250ddca0060c800006400003c21ad50200664a046855800cd28028024f3774d0019850005900009800004c660031b600405c80110c832d56b00452300049b001a840acf3690b79848002b1112e1566970ab004b800033d495c9986008cc80002390001250919dca00a6ec002932002204000914800a6840039ab003145801945000c62800229b0dda94401464800b6c80051424cb3d94ceee1a004ace0063470003dc800a054004f1600083222308940092ec008cf00063a700105d8008eac01428e
  | 20 => 0x4bb528805ac084ea2d76f08c3006056002d48802d5900017400025323409aac0090d4002ca000215034d32dc0009000090a066922480054a00262c4936f4300438b0002c18011488e7772d000a90000040802d4e400a820002056000ca8001810976c30d07aa8880222895e59864caec35b9229814b18d4898c6050c633594128000312d690c36b48010003921bbd44400c45800226c00810b335a805e86e1a00660c0007810002190dd6a62776893b72661dba330e90540eb5283324450399c912400049c7350b5
  | 21 => 0x778001bd49ae91e60148f6006b8300359180298240010680027735a2d0cc01c6d9548f110008640012b1952601e0008226ab984b5530dd2a586e008326009223533a89ed9d44e00830600822321dd4ac02046800ace821bb86800a9a00118d4b77309000a440009d2802905524d653865231802a1c000c15000e008b25b2980331a8004a048ccee5006b870022888004418008e4a0008664a5bb8c00440c004f6000008a0048c1801d98c00534688b513804891800560400d0e0966772800cb00008c44004a22
  | 22 => 0x88b900100a80108100108a2005091005a848001850003480002770000045801410528cee3981751802048a551886000316b84b7a8058802a2d40e776a51b89631c35a98400408c00ca8400b53b0004b2801a81000c8000024331bb192651840b6b2c63884372a2442accd08920050c4006a870003a180190e0000f540003784cdbd14002cd0af336500840500442980212c400a30400b281005c048016e08368f110034180059048018ead70f4170048b4003cd380048980006c4000625000902800895968f217
  | 23 => 0x42215bb192401ea1c00c826b66a09ca5bb9402ce0400f2a800266335da14c0148d070ac0944687580211b000a1587350ab0001551bd542c0158d400d1720086341dd9125aec89200736c0043220004c890e264a00f2c6
  | _ => 0
def ruleWord (i : Nat) : Nat := (ruleWordData (i/64) >>> (25*(i % 64))) &&& 33554431
def posRow : Nat → SingleShare.Row
  | 0 => 0
  | 1 => 4
  | 2 => 7
  | 3 => 1
  | 4 => 15
  | 5 => 2
  | 6 => 5
  | 7 => 8
  | 8 => 38
  | 9 => 16
  | 10 => 39
  | 11 => 77
  | _ => 0
def negRow : Nat → SingleShare.Row
  | 0 => 55
  | 1 => 65
  | 2 => 86
  | 3 => 119
  | 4 => 130
  | 5 => 154
  | 6 => 183
  | 7 => 188
  | 8 => 212
  | 9 => 227
  | 10 => 237
  | 11 => 253
  | _ => 0
def decode (q : Nat) : Rule :=
  let p := posRow ((q >>> 1) &&& 15)
  let n := negRow ((q >>> 5) &&& 15)
  let pp := posRow ((q >>> 9) &&& 15)
  let nn := negRow ((q >>> 13) &&& 15)
  if q &&& 1 = 0 then .row p n pp nn else .cross p n pp nn (posRow ((q >>> 17) &&& 15)) (negRow ((q >>> 21) &&& 15))
def readRules : Nat → Nat → List Rule
  | 0,_ => []
  | n+1,j => decode (ruleWord (ruleId j)) :: readRules n (j+1)
def rulesAt (i : Nat) : List Rule := readRules (pointer (i+1)-pointer i) (pointer i)
end Core.HybridData

namespace Core.HybridData
open KWMemo
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem span_join {p : Nat → Bool} {a i b : Nat}
    (ha : span p a i = true) (hb : span p b (i+a) = true) : span p (a+b) i = true := by
  induction a generalizing i with
  | zero => simpa [span] using hb
  | succ a ih =>
    simp only [span,Bool.and_eq_true] at ha
    rw [Nat.succ_add]
    simp only [span,Bool.and_eq_true]
    exact ⟨ha.1,ih ha.2 (by rw [show i+1+a=i+(a+1) by omega]; exact hb)⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c0 : span (Hybrid.node table rulesAt) 32 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c32 : span (Hybrid.node table rulesAt) 32 32 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c64 : span (Hybrid.node table rulesAt) 32 64 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c96 : span (Hybrid.node table rulesAt) 32 96 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c128 : span (Hybrid.node table rulesAt) 32 128 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c160 : span (Hybrid.node table rulesAt) 32 160 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c192 : span (Hybrid.node table rulesAt) 32 192 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c224 : span (Hybrid.node table rulesAt) 32 224 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c256 : span (Hybrid.node table rulesAt) 32 256 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c288 : span (Hybrid.node table rulesAt) 32 288 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c320 : span (Hybrid.node table rulesAt) 32 320 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c352 : span (Hybrid.node table rulesAt) 32 352 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c384 : span (Hybrid.node table rulesAt) 32 384 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c416 : span (Hybrid.node table rulesAt) 32 416 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c448 : span (Hybrid.node table rulesAt) 32 448 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c480 : span (Hybrid.node table rulesAt) 32 480 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c512 : span (Hybrid.node table rulesAt) 32 512 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c544 : span (Hybrid.node table rulesAt) 32 544 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c576 : span (Hybrid.node table rulesAt) 32 576 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c608 : span (Hybrid.node table rulesAt) 32 608 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c640 : span (Hybrid.node table rulesAt) 32 640 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c672 : span (Hybrid.node table rulesAt) 32 672 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c704 : span (Hybrid.node table rulesAt) 32 704 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c736 : span (Hybrid.node table rulesAt) 32 736 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c768 : span (Hybrid.node table rulesAt) 32 768 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c800 : span (Hybrid.node table rulesAt) 32 800 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c832 : span (Hybrid.node table rulesAt) 32 832 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c864 : span (Hybrid.node table rulesAt) 32 864 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c896 : span (Hybrid.node table rulesAt) 32 896 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c928 : span (Hybrid.node table rulesAt) 32 928 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c960 : span (Hybrid.node table rulesAt) 32 960 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c992 : span (Hybrid.node table rulesAt) 32 992 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1024 : span (Hybrid.node table rulesAt) 32 1024 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1056 : span (Hybrid.node table rulesAt) 32 1056 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1088 : span (Hybrid.node table rulesAt) 32 1088 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1120 : span (Hybrid.node table rulesAt) 32 1120 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1152 : span (Hybrid.node table rulesAt) 32 1152 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1184 : span (Hybrid.node table rulesAt) 32 1184 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1216 : span (Hybrid.node table rulesAt) 32 1216 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1248 : span (Hybrid.node table rulesAt) 32 1248 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1280 : span (Hybrid.node table rulesAt) 32 1280 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1312 : span (Hybrid.node table rulesAt) 32 1312 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1344 : span (Hybrid.node table rulesAt) 32 1344 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1376 : span (Hybrid.node table rulesAt) 32 1376 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1408 : span (Hybrid.node table rulesAt) 32 1408 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1440 : span (Hybrid.node table rulesAt) 32 1440 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1472 : span (Hybrid.node table rulesAt) 32 1472 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1504 : span (Hybrid.node table rulesAt) 32 1504 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1536 : span (Hybrid.node table rulesAt) 32 1536 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1568 : span (Hybrid.node table rulesAt) 32 1568 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1600 : span (Hybrid.node table rulesAt) 32 1600 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1632 : span (Hybrid.node table rulesAt) 32 1632 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1664 : span (Hybrid.node table rulesAt) 32 1664 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1696 : span (Hybrid.node table rulesAt) 32 1696 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1728 : span (Hybrid.node table rulesAt) 32 1728 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1760 : span (Hybrid.node table rulesAt) 32 1760 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1792 : span (Hybrid.node table rulesAt) 32 1792 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1824 : span (Hybrid.node table rulesAt) 32 1824 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1856 : span (Hybrid.node table rulesAt) 32 1856 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1888 : span (Hybrid.node table rulesAt) 32 1888 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1920 : span (Hybrid.node table rulesAt) 32 1920 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1952 : span (Hybrid.node table rulesAt) 32 1952 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1984 : span (Hybrid.node table rulesAt) 18 1984 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem cover : span (Hybrid.node table rulesAt) 2002 0 = true := (span_join (span_join (span_join (span_join (span_join (span_join c0 c32) (span_join c64 c96)) (span_join (span_join c128 c160) (span_join c192 c224))) (span_join (span_join (span_join c256 c288) (span_join c320 c352)) (span_join (span_join c384 c416) (span_join c448 c480)))) (span_join (span_join (span_join (span_join c512 c544) (span_join c576 c608)) (span_join (span_join c640 c672) (span_join c704 c736))) (span_join (span_join (span_join c768 c800) (span_join c832 c864)) (span_join (span_join c896 c928) (span_join c960 c992))))) (span_join (span_join (span_join (span_join (span_join c1024 c1056) (span_join c1088 c1120)) (span_join (span_join c1152 c1184) (span_join c1216 c1248))) (span_join (span_join (span_join c1280 c1312) (span_join c1344 c1376)) (span_join (span_join c1408 c1440) (span_join c1472 c1504)))) (span_join (span_join (span_join (span_join c1536 c1568) (span_join c1600 c1632)) (span_join (span_join c1664 c1696) (span_join c1728 c1760))) (span_join (span_join (span_join c1792 c1824) (span_join c1856 c1888)) (span_join (span_join c1920 c1952) c1984)))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allOK (i : Nat) (hi : i < 2002) : Hybrid.node table rulesAt i = true := span_ok cover i (Nat.zero_le _) hi
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem root0 : Impossible 13 0 wiresW := by
  have h := Hybrid.all_nodes table rulesAt allOK 2 (by decide)
  have eq : permCheck wiresW (node 2).w = true := by decide +kernel
  exact perm_impossible (permCheck_perm eq) h
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem root1 : Impossible 13 1 wiresW := by
  have h := Hybrid.all_nodes table rulesAt allOK 3 (by decide)
  have eq : permCheck wiresW (node 3).w = true := by decide +kernel
  exact perm_impossible (permCheck_perm eq) h
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem root2 : Impossible 13 2 wiresW := by
  have h := Hybrid.all_nodes table rulesAt allOK 4 (by decide)
  have eq : permCheck wiresW (node 4).w = true := by decide +kernel
  exact perm_impossible (permCheck_perm eq) h
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem root3 : Impossible 13 3 wiresW := by
  have h := Hybrid.all_nodes table rulesAt allOK 5 (by decide)
  have eq : permCheck wiresW (node 5).w = true := by decide +kernel
  exact perm_impossible (permCheck_perm eq) h
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem root4 : Impossible 13 4 wiresW := by
  exact BulkKW.excludes_sound (base:=467) (n:=19) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allRoots (t : Nat) (hle : t ≤ 4) : Impossible 13 t wiresW := by
  interval_cases t
  · exact root0
  · exact root1
  · exact root2
  · exact root3
  · exact root4
end Core.HybridData

end PEqualNP.Outside.L_meta_3561

theorem PEqualNP.Outside.L_meta_3561 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (13 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn (Function.update x5 (4 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (4 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ))]) = x1 x5) → False :=
  PEqualNP.Outside.L_meta_3561.Core.conclude PEqualNP.Outside.L_meta_3561.Core.HybridData.allRoots
