import Mathlib
import PEqualNP.Defs


-- The extraction and first 414 test pairs follow the public Petersen graph
-- certificates L-meta-1672 and L-meta-2913 (Josh and contributors).
-- The remaining 130 positions check equalities and rectangle intersections.
namespace PEqualNP.Outside.L_meta_3561

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

end PEqualNP.Outside.L_meta_3561


namespace PEqualNP.Outside.L_meta_3561
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

end PEqualNP.Outside.L_meta_3561

namespace PEqualNP.Outside.L_meta_3561
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
end PEqualNP.Outside.L_meta_3561
namespace PEqualNP.Outside.L_meta_3561.KWCertificate
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
end PEqualNP.Outside.L_meta_3561.KWCertificate
namespace PEqualNP.Outside.L_meta_3561.KWMemo
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
end PEqualNP.Outside.L_meta_3561.KWMemo


namespace PEqualNP.Outside.L_meta_3561.BulkKW
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

end PEqualNP.Outside.L_meta_3561.BulkKW

namespace PEqualNP.Outside.L_meta_3561.KWMemo
open KWCertificate

/-- A single scan rejects every saturated state with one of these shared rectangle conflicts. -/
def bulkChild (table : Table) (k t : Nat) (w : List Wire) : Bool :=
  (decide (w.length+t=k+1) && BulkKW.excludes 467 19 (sigsOf w)) || childOK table k t w

def bulkNode (table : Table) (i : Nat) : Bool :=
  let state := table.node i
  match state.k with
  | 0 => !(search 0 state.t state.w)
  | k+1 => !stepTest k state.t state.w (fun w => !bulkChild table k (state.t-1) w) (fun w => !bulkChild table k state.t w)

private theorem bulkChild_sound (tab : Table) (k t : Nat) (w : List Wire)
    (prev : ∀ i < tab.count, (tab.node i).k = k → Impossible k (tab.node i).t (tab.node i).w)
    (ok : bulkChild tab k t w = true) : Impossible k t w := by
  simp only [bulkChild,Bool.or_eq_true] at ok
  rcases ok with yes | hit
  · exact BulkKW.excludes_sound (by decide) (of_decide_eq_true (Bool.and_eq_true_iff.mp yes).1) (Bool.and_eq_true_iff.mp yes).2
  · unfold childOK at hit
    by_cases select : (tab.hint k t w) &&& 3 = 0
    · simp only [ite_eq_left select,Bool.and_eq_true,decide_eq_true_eq] at hit
      have res := prev _ hit.1.1.1.2 hit.1.1.2
      rw [hit.1.2] at res
      exact perm_impossible (permCheck_perm hit.2) res
    · exact certified_sound (by simpa [select] using hit)

theorem bulk_nodes (tab : Table) (valid : ∀ i < tab.count, bulkNode tab i = true)
    (i : Nat) (hi : i < tab.count) : Impossible (tab.node i).k (tab.node i).t (tab.node i).w := by
  generalize level : (tab.node i).k = k
  induction k generalizing i with
  | zero =>
    have h := valid i hi
    simp only [bulkNode,level,Bool.not_eq_true'] at h
    exact exclude_search h
  | succ k ih =>
    have h := valid i hi
    simp only [bulkNode,level,Bool.not_eq_true'] at h
    apply exclude_step _ _ h <;> intro w no <;> exact bulkChild_sound tab k _ w (fun i hi eq => ih i hi eq) (by simpa using no)
end PEqualNP.Outside.L_meta_3561.KWMemo

namespace PEqualNP.Outside.L_meta_3561.Normal
open KWMemo KWCertificate
def hash (salt : Nat) (v : List Wire) (k t : Nat) : Nat :=
  (v.foldl (fun s w =>
    let x := ((w.1.1 % 1048573)*(65537+salt) + (w.1.2 % 1048573)*131 + 317) % 1048573
    s + ((x*x % 1048573)*x % 1048573)) (75*k+263*t)) % 1048573
def shiftsData0_ : Nat → Nat
  | 0 => 0xb828020a020200005148600c06150080e040015022133a0000003040007608008885231060540e03038001c00070b8560104004fa071c0000605000080002000640209400045228
  | 1 => 0x402c0d81012090181c0018118000001018ac0c090d064120701168081e0006808190085002001902446041381c02170b0b4880c0b800060e0c0243e0a070180601030980c02
  | 2 => 0x1044021c00000183c0601c04d7000100e3e000081604000100804058241e09028e04614008141e000601800000281002000e0141805060011c0710800120c028000c05000080000
  | 3 => 0x49101c0c220242402010040216030200453000300c8f0587454140b00002170400c30810c8001e070b8244600030e0024537808160e178140001050100000008041604040040000
  | 4 => 0x30002400010143c00070009e06048080205000000a09718ec9a00000054202040003402028080010010000e030780c3200068141a24010080400000280a1f008000000090001c0c
  | 5 => 0x88343c0f0201c0e0118010000104000000001088001c018081a00024ac0000068000e011e81842037180d280901844020a010543e04008080e001202c0403000240e2407828200a
  | 6 => 0x94422280201c0001070000404080980001018a00a000002c2000020980000090000033000b8021105008001a00034fc0107804d80100020321b00004320702810020303004fa04
  | 7 => 0xc0100201000101e1f0005848052880004020201c02060e9902e15000040c0a00008200107008080002030020a0485c081300844040108000e813020780a07108d4000204878480c
  | 8 => 0x2182002282f11c4a020218c0423070080806098342c090584800000183400022b80426010182414380b81802180e8781200000003201008200e06020000c1202814021c01850300c
  | 9 => 0x2828200d0c0083202010843a0d00004163f00078000600018020504010840001000040606000104c08810020b0286c06091802c4410090040c200085c5c07010002e0d008001403
  | 10 => 0x18241c270081404110500402140087004071a0702214010c81a000382c04001400008150300006020780804173208c0814030e4080d0e8141a020018c0018008442002000440600
  | 11 => 0x181014430300802080980008010c85000080401890000081c00090d02400070185410260188818170000028001e00c040002800000a000201009010500803018580a050b84c002e
  | 12 => 0x4800380302188000301814482a018b07c000000830160408800000003802001501836020080072130502816020000c0c130881814000a87414032c000100c008040005058003201
  | 13 => 0x18102207160200e040083c002e020480a020000426013482c0c0a068481006028c8003a058180a3900970002d0001c0202150f40001038140c0f0308418420802c04010d8001200
  | 14 => 0x10101400091100c1a05240001003000346e03248800006050082e0803000820b1503814470c80014081900000180084128071d850140d078f820200000478330592c2000
  | 15 => 0xb00828021189406010b00c040e0e80456095e80400001508808050101034010783c000f2080812050288c003700008000d088bc0c13050000e001b2106e240806c0600080500000
  | 16 => 0x387c0c0116000242c02000060e0480038010180800000285004100000c4c040300c020000000043f02838001b00000000b0001802001683c5e000003c0c020600c9603000082405
  | 17 => 0x3c08160681410010c894040113b5000100600610005a14c00000180400000102000050c80c1407030006401088000a0a0f800061302000520000824b003160e01419000180c00
  | 18 => 0x8741a0601928000c02004022d018205600011d00640000040e10050c8240b070001c062188c02170005402030101c0403070fc020904004481a01824001f068040805010000c01
  | 19 => 0x309406020387872040083c082a0107c7c070080c00300300c221304808b6011b00472130101060480000806062a8743a3e0106c062c020081e03010000e0a008101606088200a06
  | 20 => 0x58a82c051106002110c0442c04008004c0e038580434030144410048182402030040c080080000001002c0a000180c22050f848140508018100a078243a00078000000010541615
  | 21 => 0x6466000905c0e2e008380801180100a000e82840220e008fc0701018160b150000404148300a000a028041702804020000000420400000a85a018240e010783c06031410c1012
  | 22 => 0x390c161209818c40a020b4041900818440603800a00d0180004010180020001883c0000010305e090500018010000804240203008001b00c2227198c4160c0c86c0803058081805
  | 23 => 0x20100401000241400000041807008086600000480600018001029000682603008403e00050000c0d048cc22030084418010400000162002008130280446000d828060c010283008
  | 24 => 0x186400180000000030d820300101015140f040800001008005813018081c501f000000027000000c1f8302e2f068201a001887460080d000100404118021e02020060a1c0000eb4
  | 25 => 0x80c40000005c3425378000200050b4000b0b00002120002c0a110184408070400000420589c8a090003c06110502830090482004030082416060e000000c0002400020880c0401
  | 26 => 0x118100051090040400028043e16080041200050180401098000e320f0c0127f048080a070006c08010b03488601002c5e720b8000001000183001038180e24018440201008140006
  | 27 => 0x300201000940c070a860040c030140615028881c000a008041900818000a0481402040180416030185412010484402020201c12020400402030e8580215240200a0501838140e
  | 28 => 0x1004000002000161800028180f0083c1036008280000048243c50050680200040040019029f428040c06c2462188081a010c0085401000740403000440000310040009158141c10
  | 29 => 0x300c0254018783402018108413000100c2f0380c2e020000c2633030040600160cc0212058180000058905400010101a0f09000081a148102a003a8e41e6f030640006020281401
  | 30 => 0xe00000010781000160102010310182c00050b00c02020002406040c014020e018680a1002804500107008d0390d170021f0884030d000844560e0402000040a004061f00808080c
  | 31 => 0x1828000005018060505010020508860120c070080010000000e020f0004a051801824030380058010e80c001b000740208079283a07050501007020c8020201808000701800041a
  | _ => 0
def shiftsData1_ : Nat → Nat
  | 0 => 0x8000e42312010042a07804700d01800000a070040613010004a001a83802000f80c3012020001c0102800040e03800000a1682c20000300400093b86eda000980004081a0349e05
  | 1 => 0x8002a0a070e804041c09808090380c28000000006010001c0678118340c020280000001700c580801008440e0302002050387006b204004f4030102c18060180c20070d838000e
  | 2 => 0x280808010004c1208078101201188381410000004e000182c04000005400020008c04050091c2008010302a4300864040404800000002824180101008020c1600024130892c0405
  | 3 => 0x6800400c000ec020b0901480050d8003008000800c140000008000f0044a0d010043408000140013030500a020100ca400560100a011a0a40c0a03060000b01800e001008000406
  | 4 => 0x6030340f07000020c0000808100082c1a130181c14220102c1201030082205008003e0703838040d0d03000000280804030a800260f000581c000480c0a0008920024409824580b
  | 5 => 0x108000601010140003020a45e060000808090300022001501c160a030643e050105000121602c2a06098200602028101010030101e0014800044c0501000060980c10020c8a02c01
  | 6 => 0x118440205000080210020081002018180004008100400018240a08178000000160100206020293a1907044000005808040a0103c0021000000c050d0003a00058001004028e86824
  | 7 => 0x1080002000101c060103810020006000081200000080f0a80000090f00000020780c020000800080000820020400020f0000982c000b0002002060e00002010000c040e000006602
  | 8 => 0x104c0a0c080440c0a0082c1e00000380e110302800010185c28020d0280c20068181016078080a21000001402061a4020b0b81c021c1a0803c25010400000000104a16000803200
  | 9 => 0x8800e6000d0448801050000c00050040e0d1d8440a0d040180018051101a000b804120002004001208040000e06024540a0002c4402070e0141e0a8100009000040217150180201
  | 10 => 0xa030128e0500008200086c3015098180a08078100400008000000098001215008780a040b028000b0000002010000c06380000004070901008140200416800585c102102034240b
  | 11 => 0x185838000100c4a02000048010020480a000300004070082412130b8000c02048e8020702000380a320282647010140a0f00108060000878ca0107028343e1d00c1401000000061
  | 12 => 0xe01c0a000080024140486004041381800130c84c0c170202438090001840140280c020d008980e000300404150b064140801028020400800041a00024080f02804000c008040e18
  | 13 => 0x28006e010000c02011286886002b8001207028045e1e020081a0205028060c000244421000342e2f0000412061480400121301c5c05190f82e0200004161b00048101c000701801
  | 14 => 0x81800010583808160509c100009814080c0b83028030580004060f0100e0f2700008130180404120084c7603008001c350e8000c020381888010483000150c00c0a3a020180a00
  | 15 => 0x1018bc001685c222203000240f089c00804010040205068884a030281c00300b0000a00018b0063100820040400000001400224160301108380200834160708010021b019980215
  | 16 => 0x600c04020182430020183c060a008cc000f0d03806031e04c001300008000c0980836060300002161404056090083c020507084180800811700f000040204008000000030200c02
  | 17 => 0x9008100c0b01c221a0242412510280c02130307c000009a3c260a018289c15270041e01020041a010201416054b97426200b0441c06028180601001040002028bc0202060104a00
  | 18 => 0x15a30000b07810d8620201808070480c140004024220a00a2c009f1780002081180c000101894300305834761a0180c841e200043200010000804100080002388100200000cc0005
  | 19 => 0x306c00130282802030185c020306034421300800700a1d824001c0101c2c08009f83c1c070080c0e00034005b018581800038080008068103a000000c2a03088341a01000140200
  | 20 => 0x900c3207068983209000041c130106000161487802440a8280c06030681078011845a080000008030200002000387820010d0b4f20f0584040050083812000006c2606158300001
  | 21 => 0x40241404008000a27002e824260010804001703c0002090485a070483c9223018908a0303810500a0383c2a1a0887c240007804420400034080004004120501800a60210a340822
  | 22 => 0x1801000060880000250001c00680080428052d0281228428d80403158103c00000000200038340e04038045c070c07c08030002854011a8282801000040208000480002000100206
  | 23 => 0x301478081000c0a020100c00010003880030180808030201c18030c9dc0c710e030080502008121b020180c250c07810060803c360b048000000150300402039b004000881c0a00
  | 24 => 0xd064228f2f800040e0003c06060087c060601838601403020061412064080c03804000001000000107818000c178a000000500402340102cbe0100084207307018040b1207c1406
  | 25 => 0x180026040580414080200c0c011581c08240f0380a081882c300d1101002000480c1006090a00c0a1f85402090102c100f010006c00050001c19048242a001f0644c010b0000a01
  | 26 => 0xf8a810010010cd80102800500d0003404000004000030b83400050500802040704d4a02100680e090003800000380000000005c0003000901e0c15004241d0c81002030180c0c04
  | 27 => 0xe020020004044100d0a8007c01018000e200201c3c210380040050401c0005058501c0000004002100820083013000120c06034220814800361c088157601008240a00010003ca8
  | 28 => 0x3000140d0800c26010380002030080c040a0002000010003c00051b02c02192d8182617080201c012700c0800040442a001402810020e010000d0000018000380c1c07450001e00
  | 29 => 0x2800140a0883c4a0001004041f0081000020c000040d0180440002d0000c0400800121e0002002060000004f300000a2002f8400001028002c001007c00010b0380a0c018002000
  | 30 => 0x387004002200800120013c040a130301c150888002000d81c0200028500c000001c0c2d0183c00050d8001411010f41c020e0a4000d0f03c260201108b0070a0b40011068cc0400
  | 31 => 0x6800060e0000c28b8160400e0b000841c4d0004c7e010280c1202038000e300b26c00080281040000000c0e26018101a3a0180002000f81022040e8144216048201e0d008640006
  | _ => 0
def shiftsData (i : Nat) : Nat :=
  match i/32 with
  | 0 => shiftsData0_ (i % 32)
  | 1 => shiftsData1_ (i % 32)
  | _ => 0
def shifts (i : Nat) : Nat := (shiftsData (i/64) >>> (9*(i % 64))) &&& 511
def slotCodeData0_ : Nat → Nat
  | 0 => 0x16b7587cbc29b1d318ebd07f116b4974000c528a3f71cd26f9082bc613064851f6c8926552c56da3a661508d64cd28ec87014325b0e6084500024639fe5a3e091800051d40006cfa48c6c0400040c40003b767b316ded8f7708c156ef67497c8ed867a99066bf0c26f2eef10300002e5
  | 1 => 0x418d339781a0100002cbe9ea347bb5a24e00002a5b60c75f025d680131b9469d159b0991b50e204514e794fe27eb1b6f43865f4f56ea4898c03651b9dec324163cba539ccdfc29f55b2a4133ae61a60c6703f2aca758f5f662652460ecaa9034a963af9ec6c62f91a0600f4a4cc8eea4
  | 2 => 0xbe1f08faa8a7b435991fbd6769d891bc091a97e80ba5cde8ba478ff026369079a411a4095611c9778ec0bd3050f99ca8d98578bb931c18187217327a71c857cea6806a4323ff7396a18be66dbd583a1a24d043f30002c2f92ec2495a8495566ef184677d8d6d4ec3da20a2949218ceec
  | 3 => 0x1280d20bdb47a92da6a7127a2f7f000359800009de33a66f28e28252306b63cc75f3ad3e553a72e100008222d359f04000bdc800003b84530002f409f3d6d60a3c96c88661c6611ab6a19c5e363f7000027831cccab575796ac00026c66ba47c2172538f3e5a5fa3c605a832c176732f
  | 4 => 0x1f1f9cf07c8c6e40005c3dbfda2a6cd075bc59300034b1000000000027d000008d15d34000d288000975984f2208dad9ec80004289b05000000000032210002d180000f2a514c00000002fd00005f74128000b92dc66c614393bac61abbdb0000b040000abcafcdcb02d7ea4702da
  | 5 => 0x2d1300024c97059e0a68c03429d18000180efa031ab5e0c06c27a3f0ec4300027410002cb22b4b58a2ca512493cb2ae00027d2d6c0ee200022852dec577808297dc7b6a1b29f244a489da32b34dc485eeef48692930ac3a13baa69eb799ba80000000000d2558ed53523c8997c000
  | 6 => 0x6d9000015fb43299fc0009e180001c0011f22d2083796800081cc000a80496db31f200915800017b646e441944f4d1ebbf0000000478a6284bc5b7752b63bf221c22100002a700027f6d518b860001e88c41d75c763c0005bde0780ec5873bf666d64eb161800032c700020a7705c000
  | 7 => 0x11b7d8ea7e51c5a588827e87b02c96f25e7462f000190d5f4a4d70874000594357dd7934d6700441eaee1db3ca70000000288600026fb000250675b93f35c3a5ae632db2e82994e20000ffe37168e100018b4064a4a30000000acb0c0a71bc0000000000b81417e52f435e8c3ab91
  | 8 => 0x6fd4e79464106e0fa64e70002dc2237d896c80c1ef4771d2700025f3839d2eb765909a95153c28c30000ccd692482aa7281de449449f349f8f5f54f629286e0564000491dcfb0b73224716828acaedeb423b8d0900009c0805577c6eb871a6324000ac2eaf88d29cf7156091b59ed68f
  | 9 => 0x31e4000ba98ae15f222d2026d891cd5077b4c5926b7eb1d0b8bced76d29adbfb985314b884183adbd83c5d4d1464234a4267140df3e9853a882c6f7b716bcc92247dd7bfea40048748f101200e955e3f9296c000ae2185a27f9cad70a686402a72c620edb7bcff2ed89a3c49c050a3a5
  | 10 => 0x1f428c957f80006426bad0000000a08ae89354b0000b580003c2ddf134c10949c76198537eb133c60d7800000007b11670af1000042c0000000190ca304b3c94cb68fd6befb400027940000e4400020ad159a97629e902f62dd16a0002a52ac44e39030d2609009fe9acf00000000c43
  | 11 => 0x5585e9a0cc912d5eb6a8a3c42729364cb5e00000001cf89d66bee65cb58e5f07488c3310e82d900003ab8cd66c03a4f2099fe00000003684436b188b39000000008e9662d27585b98bf8a186ca015f0a7b5216fb330d0aa000000045bb3505d6a7df91a8945cb42cbc0002aa44ee46a7
  | 12 => 0x2831f084458000855c4951d4c7be8db44174f56b2237755fb5bfc000000328f49c2ad2a748aca2e91296239c14b06b74de2c4a39ea94e30f000095f35ee5b02b50af96d8093b24bc7eb04a041c276cb4c962415f3d951f5d55c000000341dac7711e5a39cfe22fedd340f1e2b082a0b4
  | 13 => 0x31750f74123278d69d6cd44babf59f24d01b9e8000cbf2d5157e2340315025c99050ee8a9963f3ed30c6403ee7f08d021ea5816e3c968a2273029ebca7b0560ea90d1a7874481cddd15a91a671a7bd14989f2f3f76701356f409e275ea86320add7299a515a58c055573a19c94ba5560
  | 14 => 0x7fdf4e33cff322994a3074d5a67687f8b132d966aea6a18375c8de65967f4208976b9fbbf08cb1f028339a4e69733c80008c41150d8e6eb5869c14d15201bfcff93725e916e03964848bc7935d7b294b3821f12e3cc4430a506727c8492a960d3060356598093b65edd83cf726200d04
  | 15 => 0x4156c70bd1f39f72dc7d28f9928d00023ac0000000536ad008d51c46d3e9e0b826e1698019ee40002cf23668df59c3089d2690b2b958a5d4ba2ea29000000009b181c34e2be0d515696bf2c00054e1d33308532a96ce5e883ef1c61f11c8f1a7f3e4a28243ac398ac71cd2d7c9adad33
  | 16 => 0xbd3a63100017d42fd0eb6567752d0002f2f038c2db2724c6f6c28b7e0359c79181c0bc02482fa6a8686b118c669824283e34f2584a51eaacbaada879b7d0fd155ca7b48e5aa83f3b1427107042d0eeaf30097362c03b3f9619dbda853219f8c2f07102c2cba71ba34100031051bc2be2
  | 17 => 0x40745d1a6240667ff8b71929d4702818ae285d53a0340194b8511e5244fc032bc0ecc5d2a59e7000344e4b9ef5100014250001c4045295a40a80000c6aaa88992d8a3bc15aa600009f797706df58aac8ca915e6a13a8ea0d8b0cee25ada48d4d29db47542706f8200d4a7c66b1287176
  | 18 => 0x3e646e37d3935f8645d5358b572813dc0000001e4ccec750a6fb9ad25fe153c000274c848c00036f800069e717e6e7f36900035fcbb52ab468cc000cca038a5f9325168b2136c79c695000086f7bbc0000002e5c3f6c0000001cb18296eebd5a03c175f33db8b6c51178dc80e620623a
  | 19 => 0x3358000193928c5b32000220477340000e3595189fc0003b6d780396a8f8b538b3a1d974cbd281fa605946301fe1cd90c69f01556886c0003661c6eb57693f348100017ae6894065d7a50eb0002218598000072fe2d602200000001bb24ef84bea3fb0fb4e502792a9de1e
  | 20 => 0x10760001f7e86370020000000d53aa0b752800063305fe0f36c557ed0f64cd440002cdd12c000286d690a6ced4cf5c7a936a04d98c52e84ed4197c10000722594f5b9512972614fba0d80007b7800054653675181698161c000aeac000112e5f5d4a09a903bf41e00010e30000a1c
  | 21 => 0xc289218000bf98c9cb4ba77e56db599947669a7d2ef960000afb1fd856806640008a334446dbd09d5ad46a4596ca8cb78400094040004a3c66a27396dfcd6890b97765464320000af989d9763acd75ada15332f0a63bfade64c0f60d28e5d7115af703c43d32a474d26751a2c731
  | 22 => 0x50d1bab488176b0000000000000019e5a9e3a2f014000178500000000001a4d72d764600035a0ae68000000010e000000000001dc00000000ae8000b5180000001688000000077d800080905bc93d353a25640003587311792633138e0866c9d0000b654d8876291f655d80000000000
  | 23 => 0x2a595d61d927ce42f157062d886b3206a00075500003450002525643c00000000000000ccb000158700001390000fa7a18abf387e95a7000079ad8296d1bd4de9900001aa376000000000000001a53500edad5d9d9c802fc918826531f56873d40740e014b18437d3c9002a6863b4
  | 24 => 0xb6980000002b1b3f3400072c12680000f13ac9ad5000000005528000b9b9d6a663b54347a56fc000317b4aae8c4704115432b758392c64efc6c00007254000d8c0000b4c000071971fd99c1496bfe400096080005b5cccd4e622c9ae34afc506c00000000000000000000368d
  | 25 => 0xba69c128a84d290000000000026706a66010001a411b6c0000000000814810900030800000000a7c00000001eb980aece5995d2169675bb77ee86018c0c0009abd5c531dc000b1af62e1d7aa508944000237733e00028a30001b2685a9d29000221e33f187a691c1522ba45e02037638
  | 26 => 0xaa667bc11f0000a9b400048d4d44000273b000000035611b858bd6f6aa3c09474245f05cfee2b5400f1c5f16bd40000000121e0893ca46d2cb062bf269938e6f1c000c4fc00022a55a250ed258000175067db41fb8280008df4000133c00000028165c5a7514f8971b18e4000210c000
  | 27 => 0x317c000c30688b0002efe8608c00660dab815f574a6ba11725ed650c0000b92bf9e7ff856aa4372e400025d880901f940447790100001c39d496e3f7894b73bb10eae223825b000081b6d483ea6025b3f000211352a702c387b47a3b9e68c5d825a7000323b8424000b826b71d2fc23f
  | 28 => 0x64fc000603a82820cc0000f2b5b30c80c65a3ac000c4a800043ee45cbefc000673dff800035cd771c000bce4f8495321b20000000212f2dcd5440000001148000187751e6124646822ca6f5aad126768c43392b3000189c0001d6600000000000000000000000000005270677bb54000
  | 29 => 0x30b1caf89e4f7f4c3761b883f591d64d3002ad9ed01e815348ff2e1432d80c5bffeaba0d8e6bc18b924d58ca19a45d1b36351c6ff21240004e8c3e7abb400079b095b0d940000000985195800002dc0000dd4000c7eb46c6aae42a00007a83e6c00052d6f460002a2d00024315962971
  | 30 => 0x8e572d9a6ce73a43668072fb66868114000c340ebacbe70ac9420fad479c000676985e0b42df651d947cc772c450323308b22f488bfd0ca9000076e2c9574fc69ecb0a2fe8c26d54c110c9556a1ee593d76014cad03dfb1b848929d66ea1608d5d2a5106638d534b6c2e083c2cd826cb
  | 31 => 0xbf497107258000b91635eb0a008bb1f27fd96a13b7ceab0ab2f9e955125ad31c5e034bb5740410175701a1be6140000000800497d6aa8f5200017c9653840e2b38000000209800002e70000f0564d4000191c0005e7d4545c5ecd9b7749da3f240005b9d86d4cc5f6fab0b0465a12004
  | _ => 0
def slotCodeData1_ : Nat → Nat
  | 0 => 0x62605bf00000007bab48081320490b0000000035323fb69fb000252fbb80adcb3acd5010d8000659d41a000352b97927af48c9c991af5a289899e4abf2000068ada7c95a4f92ccec24fd7726126ceed170c9c87a9b2000068bc0de56e19557241bd7a84c2aec82974cc48de555240715
  | 1 => 0x9733166187400064f0000c2e0000322c000000333dad6f629000000049580001b75952a6a8000186c00094c40000f273c015a4000000000000000000000000933c00000021633730e040001dbd00000004010000ba300006b5e08eb23c00085b46e9000000000032b858975d386a315f
  | 2 => 0x44dcbba7937097080e1700000a2ebe6d016b3240002a0590e72d8b40805c44d4daaf10108985300000001c22695a83800028000000001be59b73632c2da8d000027420000000ae7ab0e00001980000133000000046e40000000000000030ac8175e800032ef9229c9c3fa15230000405
  | 3 => 0x37e960652c747d8a2afd321ddce75fd73934f440cb3e027e02b400004b92a5621b4001a33b43970b20846df4b217ebcd7515340003aee082c8787c240f8a17000051ecad2221300a5057e32d87a030fb67adacc80c774e50001d32009139e8e11ba5469c00089f55b0483ea37c1f1b63
  | 4 => 0x5d840000d600026bc403b7fbd21b7dec00063004e9031137e9f0cbced26422711e4117623a11d225c62019c899343013de49d869a55c8ffb27d084db228c076b8eff678994096158a62067dcce42ad5c9af872776f027eb7a01f8f4b052f618b26d24c4e23897bde2eb07a85bd94c508
  | 5 => 0x63c28cdd40d39bc46d489bcc4f98335cb6884d067b8bfd9950f1c37db0b9fc54eb81806d88e9cd625f6c7d5c0bdb6c55c2b956f28000336a3ba89729dd9e5600024fe0a26d8d1694e9bbc8677212094cf2e1f1a2a055aa2182570da08079d000200a06d066648a80005232d030000000
  | 6 => 0x113031600005a619b028e00000000000f8db4d8c9600000000000948425419a89a6a3a69fd94308b533f65c09eb69508a1cd862e9952a7474a153490e180000002e524ab288401b9b19a2508f1818920684223c785249d57cca5c68745cb37eedd07cdea2c41fba98d5eeb04c
  | 7 => 0x7edb114b73725205a4138496a93e791acd697245f53370c087bdef2e2dc224c000133200029dc00000008d3000043c0000a06887d6a700007bcc2600000cea4a09689d52d497001164700890571a5817200026e500003efab5ee70a613013cd6760e3cb98ee407dc8745da3dc00000e0
  | 8 => 0x7de5284649e25f42a28f100003d19dad1f80002b3100035db999752e0001683a6b40003b82da76f9a832741065cb2c54d67bb5c525e4542bb346dde242984ec6ccd154d010e7bc89661a404b1d0001c180fe129296b0fe9a2b182903e14d850855116565583b2b98203dadef5b830970
  | 9 => 0x67418c8a0c117f7276ff87fd5f1eb4e1fdf0b11624cf065171e4541e979e1e046eb13e12a71bb872182724d00000001aaea66000016100000001e96b1bc0009d5604a9c92a754921f9400035057332d981a08fc23d8a54485f6ee59c1ec905d90a5c6ae68e002d04e7000cc1714bc000
  | 10 => 0xc3e40000dd0000ae4290e43ceb999858ff63d1dfec3570e1373243fa2fbb317000000000000000001b5f18d00cfc811cb241ae1c42e45e002e054ea250b2f5519d1130003258d3cea7ea711d40b8db03e65013042a91e080c2042d00029b8000191d00022ea5edc0006fd0864aef9cdd
  | 11 => 0xa59d8c6ad1d85d000277c69c913d0e74274cfc89e3d4129f5823761ca7500006a6c0005fb4000a32c00091ec0ca909d9012674a8e8016ea76591157aa8033c42e94646fa933555f18482740005000043465f744932c93cb5dc2eac000268540066b8862332c1af1594a462440471056b
  | 12 => 0x7484f8fc705f98c0420bc7b19337d5fd938acfd3e46a51f50b5c91ca7ad45ce89495633350fcb6a9e0f19c2cce300e5cf1adec55fb5e041a8e609087f8e1550ae0f4484195e9c9965665169ca29e14017d3fc399357a61586e993030eab4c0dcc2b2c2bcf6cc1a1a69053a5953f5216c
  | 13 => 0x9b34c626f919580001433ceaed5513713967b45d388a7ac09526435aa56cd7651a2a173758c637f007b7103ca24b1f54ef5f54c6626971afbf39b41b5705e50f76619c1f496ea9e5603ab0108a40b8a864ddc8d915190f93742de987fc00092eb482510e53eb30a18f01e6e3ca7ca055
  | 14 => 0x26e8987222900007e28cf85d0d2c80005c140001cba7ea53ce92784468de8b50d575618df360d8efa0e5d712ce9127bb2ec000a2027378851b99bc9d96a01f300c9d4000000000007d66f8100000001eb240a00014ed000203a7871c47bf24a9b237a4a2af0c0000001d6c0001b2b
  | 15 => 0x47fe7f2a23eb6080b8ce138d46b7d96deee916658f10e47185dc965d34d132b000284fd195c3e00000eabb2c000c976b631b569500a680069fbdbca463d0e51a96126972f34a5e9af6600023ea3642f6700009acb9dd173484c4a5a8db4ba2e371e422f00006184d082f25f7a0001f53
  | 16 => 0x2e6d416bf70b75d1e32f331f5edac9eb5f9761a8a70000478cf1ad3408e2549423cff89885ebc0000000ab3dcc2096503416ae996776667d9c0ce21ce4833a3eb1f82a3e850518d6b040002c97548a4df77a4089a63800041eb3013b100000000fd55b301cb0001e9700006890111611
  | 17 => 0x57a1491cb68d231d4200fb97859db33deecb8bb23cc0197f41e782073aa078b0bd26b496492df76accdb016800040d8c4e3a8929023f57d7907487c994d04781104aa69ab0899d65385cf99910b3a9e2222313a54c9549438683526838db8586a142775e2fa50ca824bbfddebcc4f1cf
  | 18 => 0x77f53c0004c39f22a00000b826e37770a76ccaac44bfee5ce7eae5c152dd2d5000119bbc2522dd976ada90b70e585df38e3b65386718cbaf576f16f3699f4d825453e6d0ab1487ba02fd1d46c2bd2cb3611ea95a96a6ea869390acd04b012a570b453e46a87cb6e57f59975f4d842b19
  | 19 => 0x234ccfe00016a7abd81202c6b22667cc000aa799b26d12731000000002db1046a002d800015fc76335381de101508f822400000079a9525000000004db9f342cd478833c4097117caaacb4443e076d8f1a67e3a1b1c5cac7af62b1028c4d8d888b23a7e1bd42c7a93c8844c51cc30394
  | 20 => 0x46ae290251b396a52c00000000000002493d21ce85b20d22b47000590001f4cd30ae84000104d65100000000f0830d60d41ac6264d81df9a750cb9f4a5011566c00000000573b8bc000c894a1978b093e2f4c00000013fe65cca384e112c9bb76cc45ab0196303e766256a6605570f22
  | 21 => 0xa6bb0d3945405f4611b729c29257413c000163a7de615e53cbc34000836c0005c82df0d13000000000003d9dc4d4be17f700009be00017665adec2715fc0000528000150a82ebcd4e6b3ea4f01000353092d2b4ac14ef19c0880ac0001d171b201906d7aa7f7e023c2cba688737864f7
  | 22 => 0x2c0e8cce4c86c5108e36480001919cae64a917d73b40000e1e81e98754f6000310b961dcb8743800037bc88a3e9562bb1a2d40bc38c67d5b2b3269917e95a4ebb6b9d400014898c5a7cd8aa1a706b478f40007fd81fb7444ffaaa443d003c88db86b66a81455f0c33fc000000244e
  | 23 => 0x4abcad686fc00000001c7ca6e23b2b2c7fc2539ba41e162027a4f15b166e76196b5125aeaace736351a3148400056b1af4a1a1e50626a2a7ced63e563800c10f2ccd6170dfe23305d4d23e52fbbcec61f2118111605e97031faebe6028000d9220b7bf063567f6c0000f006629a8e6f3
  | 24 => 0x3dd69651d9803555bdbf3286defb94380001760da257e8000154c1cf255c0008cb51c5000213e000294c3b18e080000000b38f0d40911c8800000008b89f681bc743e0002dc0d6109b743809610940000000042758554d97bf8b5017baee60000000c5132711dd75f5d748000626df85
  | 25 => 0xcbdac2d190e1cb7b6e5bf4414b6f00000000000b9d7c9109b2b1b091ad640003f41916aaad3d41cb0000000180162b01b596503c5044c000c7771a18ce800054b4a9f158d97e9fd1904352230500000005b1c0002686d2f40483fb0002070c3d8d640d26c99000000080d0000a8257a7
  | 26 => 0x6450000431c00038ceec3c5a8f942b9e0e87cb1e94c094964577df6512115bb7fa938c553d00e04ef24e62762570001334889446047f66208e0000051b751f07d329a3940fabcbb17fe67bd4f00ed278e90021398efaad142f4000bf13331a09402a3e7dec20000000289d933d8355d6
  | 27 => 0x3291da1858728bb1ba1ea981add4cf148c36d282426d01a83a9632d540a31c256151ef946aa4ab137040000097a1ef6cf400017404a307df00000000c3f05f8854000aa114ab0a554020002bf213bd104612ae34c584000a052da90001751d3f9e3851a8b763b576028955d398d1ab8e
  | 28 => 0x11f66f5853881870695d9b37657d2eb0aea3bb9979c3be9263639ace5ac57aa58426661d835e15cf40006ca4e63719c75b0002a6c1b6252100033e844221780a3698c277d8b270647054f5d84d6d32ce92add2bdd3e4c6c4da403e36b0db3ac7b35cd509f3bc90b2577e80549296842e
  | 29 => 0x17acb18cb110002f6a965d6e8cc1d50670b967d17ad82b4fcb5b47698000af54966ace14f94dacd4655482146d77473a98ce3bb835dec710804e7a760252a2cb8c6b7de81ceccfc1485f5a66b91acc5c2944eab6e48f8194fde175550437d866785734d4d75d6e159223f535a832b
  | 30 => 0x7ba28132e89d54341f1d43c8164e846e60982043e6000243091c9ce25a36e1c8a8eb8f943755072ea58b65b35940001cc5214706f2bd8000be4d3cf1dac000b861014c7f1a0800020b5d96a683442c000a125067c6197ef8b0000044af04f680d00800014a090f40cc425c000aef4000
  | 31 => 0x18b10a4c000cd92fc0000065109a567900012d82fe54d731a6ae6cc3f073ad2c84a73d07e0ac1e085ca76ae8c78a43385150418d11b6d1a8d17586971d024432c4205c88382330d914113c31fe5d0507867080002b678b8c08f0001b238f59bdf156c82339be4604f4aaea4c15cfd
  | _ => 0
def slotCodeData2_ : Nat → Nat
  | 0 => 0x66cf2ff3ff730d0000f3300014519c01cf05bb2e6f0002d9b7b0c00009864070185440d811947000268930530dfa9e23896bfc000a9f6e6da881db0d75645286c0c4841edb7000000004c560660000e780001b8f94515a8d789a5900032991df24d9826a9753a007b827cb12bd4dcab4
  | 1 => 0x44774060dea9771551df7a2c9139d8cde3331cc4ba4d3e70f7cc47e66c097a0d0287ae56730b052a9d14c3f0000a8f1f5d51308cd4c33183aa9eff340b53f599b051829773f6096b51000032e1b3f49f13b7263b6c108725928f250ece8a4c120db1339858c2665afdb79af867d0c5b2
  | 2 => 0x47f0e3cb48ae1eb876a7700015f6b4b658c10b320bab77196634968b0002038b1952ba5e5f0c063534378f65f5c000125116bf0bc5c5405271fc8b1936abc2ad3b47ccf60a0589b4b4bbd5c987064d32366dc0db2d7036900026f00001dc8a06c2f70000000a6d0aed14700004fc0000
  | 3 => 0x8eaf4b67ff68d4456c3e0923a2b9797c6fb226679c4d5336f8b38621d8856c57d2530b70c6dc7c7b1240ca32b7ec73b192430ddde8f5260f23bc310504d7e5ca39e864b443859e00000a520000b67232997aea23a7fe116717400039319b5000000050aa9ea41c9742157af446efe85a
  | 4 => 0xae32934c8b1f7120e308654fa23d2e9a72cac58f340fde4c6cc0e1d90001d2600018e37b503f4d1a217184c9de67a86046a0dc000000000000018f300000003aad3e000000005d04000bc5da7d0002027853d50906e4000b7c6ca500000000000000a483395687c0001939eb8314b160
  | 5 => 0x3275924439b7b30000c8a877eb20864f7811581adfe8824e236894ecdf13000064ba8ceafd508004c000183e4b5ed9007324ffa242f260d857f90000e4139f453f474c6c493ba06ccfc0676da1d591cfff19000018eb57fcd9401b401cd525e058d5f5cf9fa45e39bfcb4f86e01d3
  | 6 => 0x1a6d91700029edbfc228b00000000002aae0ac16c300000000000d8ac390000764cda700031807612421ce9b3867b489bcd49f051c308d5bc05d9055db17c73efeb4681ac00013851b4a07467885768adc922fa60000ac378d760679f66f7217e662a0128a84119c3a87adb21958d62c
  | 7 => 0x7d23508373b2b10712292518c5aca0d00000000000778511cc18b10144eca95c97e91b1339a3a70f400024f2390a7a2a9a70a9478a72abd300000009f180008bb304116919a1b730e74000284b0002af5ce62a39b07c2d257bc475bd94cb10000f4e67870c3000213d1995c6cd040000
  | 8 => 0x49c8c055b68d9f0000d43c2d57b92abef92d5f065bd06c0000001882be201e7ce799f40000000caf0000ac2725e31da50200017690002faa942ee763514d0b56f8580c78000033ecb55b7ea844c24925e000203e7ef835fbe28b418d8c56f1702c67311985444be8c6cb0b4ea8a00000
  | 9 => 0x11b4f8c20480001e6c0004b3e27bc4a68ee0001d95720c000ce40a674ca40000000e51b5780000000f3b0000000000236cb68400000000000001a849fa1e425a69320cb890f1a6c000000027e174fb61e000273f3815cbe2cfe92e00000000c5d119a141fe1bf145927e7d81e327d6f5
  | 10 => 0x89125fb575671067b343324084a860bf14e8eddf3f114354a1a3c00032b9db60ec082a00021f6c0d46fc00015f272ad45f7eb9f7d8728222af6551556dc9ed7b3f18d96e31945dfc0007cf88b20001133524c00000030072bfe60e0c8f2a549886f30000b630001acf2324000d7765c4
  | 11 => 0x32070002d3a50993469fc2a0800014a35ea552a6a36ba903cdef94ac00008171a06ac049e700000004b714c3282d1e0971ecad132b4e839340f7228252354140005476fbe7028000b1feffaaac0000ad070676efa2221a993d6773123d4eac663ccdb61a09010290bc907ea4c4e6c
  | 12 => 0x836e2848f05759f00544d14212e523d3fc686aee9991580075ac0f482e0962019ed39b9a82c9698a6d8cfb67f55e2d58ab6ce281c26c45d898089a45c07355735d5b89c4cb71c9184b1595a5c457ad4314c954ed5d56416bb41052fc41c3683f05ec9a00007a380009fdce9e59dcae0
  | 13 => 0x6d7279844409530000df1ca7f15e491479386dc19b000331cca50ff5911000030aca39d224000843c000b3db5bf271f1d509ba4bfae10e60bc92d81c61e3b3394d96d516eeb9d08ceeb000147faaf65bc464407b03a0d9e19fd18bc6290c106ec856b1ece2bd1e6349171022e44da605
  | 14 => 0x8aa8873000199da99554d8275eb3054761400000145be6ee342dd4580d758c375600a73ec0d11d5cf3335177620410b1536d65f9252d994a8559bc8d2e6f764faa35b6c00d9638264486c1eb37000000027987820000000575295700035ea0000000000000050f1462
  | 15 => 0x6be8638000000013667520000000840d3ff692448a2a20eb386ecba120f0000900e4770db4f50a6040000001e7fd4a8837c38000006dec3b0002835b5e658385e8a612a66838c9bdde579a33c8080818f47359eba1dab5a32c257535c8581afc400092ca206d8253aa3e274fc6354000
  | 16 => 0xb3b9ec18aad541c760e45282471ea2bdd9a00029d924c21cd12e240e8df2d88c3f4ceb5caa64400019e321060ae0d36c81c3362261c65dae4ada4c2d504d4d94033fa417ab6c49ce373b30e7f329c8e40cf59e320002f2c0002b68b5ce6041b068296ff00008502c750002d8e9c4a033
  | 17 => 0xc1b81e9a5aae331e587217128b57939882f66990ad5ab6732b2541ea13d74af8ec45195aee83a34b343a91a05cbbe132669b41c56b02b655000363db624e5f6a60f163928973bb875ce6854e25bf1c31805f46c675b6e91b516c6aa87b2bec37578935263b69ccec1dac1654b6d68965
  | 18 => 0x7f807e7305a7caa445d51460e0f82863241266d6ca29fb5acb2aa716c47064d33e63e4958720263b1d5fbd08bc6200d87f66169331720fa079c475d43184024d88e54ce762093bbc99063daf8c00c19abd765923d39eae358cddbc5ed128bae5e9d19dfd90a99e4631302e8be054d087
  | 19 => 0x2792993000046badb63cd355000069db48e93adae95f752e8a4ae63901c8a4114b14d3894155f74bdc6296f4101a0aca48d8bcf930435b3909898ab75f9b9600007ab9b0e1356dbb47f08ac05b312656fa2c03396c89d85caaa3cca495b6b3fc8395c7d59b91bd8e2869e10197460ed7
  | 20 => 0x2a4637a0000b30adb80002c8081e00000000002a02755c182aa940000000000000125b443c00011cc0004a8656b0000331772a71a5ef94d2bc8eb34166203569a17c23ce81e000035625e5637f0001b1e6a20000498c8a4a870000509000a00019080002cde24a24e29a7c8fa048d5e1
  | 21 => 0xc360d3a5faecf3890dc0e42daaf9bbe236677bd4a5aec6fcca224bb6130ea9dce5f57151c6936da0ab30842cf4a2894000bc46590d49143eca0cf0d0003339b33a87c0a1e688519800076907cfbb5d07f599a69bcc58000211c0007c880000002572000097175480004fdcf410000f28
  | 22 => 0xd9014e6bda5fd89471e85c79a56c41d2e83b5ddf629e6400031af4eb000000057814d0c5000003aa8d8308180004fad0092c021020e6ad370dbf1f200007c10400000021aa6b031c000bc2a7889f8d9fe0002da4bbded67cf1000013fe07d74f46de9bbdda7455aefd245a5db7c3c108
  | 23 => 0x1aec05265f944ea41812d1cd1d41f3de000000089da2b0c8adda89b899c600035a54842e4986d0a750001ea77f7000000010ff5f8d8553ff2092bb4e031000039c37b02b70000000ce85fb0cc602a6000049a0001af383d00003c440000000049502000059640007d540000001feb
  | 24 => 0xaca215f8600641a944d1731a00007c5024daaa400076640000002f2b00000000001638ca4c000000348c4c89ef437559afd97924257b40001fb61e14ee0aab217123459fcb486180dc400023db49c4a5418c9ebfa95049b6e6923f724a6db90e04559a7a35f91c6ac6780c00007ac7ba
  | 25 => 0x150e36ac13c72d31a600000002d9926c0000000b504cda66288150a88b60b5348ca0000000aedd6e95576a69705180c11dd2ef873c7238cf20cd2de8435acdae3112754c200000006ccd117b7d0ab5b53e83b000000027a82ded2df66071ac000a538a8a0c880f566315b36da6a5d
  | 26 => 0x999c0000000a8d0fb80001f2adeca5bb59670ccf270000000c7a235d0001ed60000000000299238a9a1d00032ab5e4b492aa148b00002cc1105ac080000474d61800014747af88f8773000151f000177e5e60000ac32c0f3849f8e59e96050000ac0000035600031b20000000267e0a2
  | 27 => 0x2c9881354c4a837e45dba0000000d994a85000000058f148820080007724c9a000024a9e91e2a9eb09e192826878cc076c28dc08a0000248000253655aca2f28f4ed20001fe7663c98b6b855ecb15179e0002e94896d122000000000035857e892f500016516915e9e9720ce73700000
  | 28 => 0x1a840006e75205797000000011ae1d880006688000312854b0001da93a48d1895d0ea7ce68726bddccf4a2eac20306cd2b96d92833065a8fd1c47d4b7b4000d59400055d082dc3dc3ba00000000b46a3f34496818174c1c806e1121c0c0007a0800067f02ffa100000c0140006604aa5
  | 29 => 0xb99f04bba1555637e05710002dea4df76010000ac9299400000006b86dd899400030d60000000b99861100021f37804000d1363ce7bf5747552186fc2568dd0000000a8aa3215a9701c6e0582c000336ec54a06acfb00005c1c3add54e8e4284e2cda9d31985b98000d99c3ec93e4000
  | 30 => 0xc230c18000354800024beb90f2af8e22128b139d489cb8adb6d9ce761c51aeb04da98f14a1c9a85bc371838decd3170154000000083ca5b49b3dc2206834e455f40009b30ef86b512289140000566b1eb17fd30eade29dabf18179787c000589d0d427fea25cf2d0efced0e2d09ae643
  | 31 => 0x6ee53a96db09226f2d92600021470000000bb31fc8969a30295de26f92da432b189c000003302a22800000000002ced2a700022030000853522ea66a3da6d459900519b9b414d24d8dc00773acd9dd99ac5cd988000173489b80001128f1580c14c60bf18a00b85b480001e603a35d2d
  | _ => 0
def slotCodeData3_ : Nat → Nat
  | 0 => 0x1fca000331fd8dc0006e1dfcd565529c77d5a266b4db51002c00091140006de56d560a9a7ac701e6fc234000cd9534522780c2138af5400000000001a2dcf4b27c4948000b681c6950b8000d9e400000000004da00005214000a14debe1299a435e06658213a3ef653000050c2059
  | 1 => 0x64e981ac22a24956b66a9b9cc000294de2fc9c01d7000201800027012af158fb78035182c85c992f5096b994000000000001f76515cb036a000328a00021d300000007f3c0004d0d63db8c2fd60000000919b119bdac00084f268b00000746bc1c8e46626a20471da26479fa38828000
  | 2 => 0x4484a6d13209333180000aa034e60000eb9cda2f7d3c6510224941621eaa1899ad6e03b86568a540ec26bf0ae0b00031958fc35226dfaed2a1503ed29b33e9d376f4f0c0b5c92a78eded14442b74fd342a73a734000000000023484bb12a4a80de3fd476e5a8cd870bd0d4cf0cf88bc5
  | 3 => 0x6804e77cef00870000000cdec0008cadca4b77207b778aed90001652b6d8e9018f547e0002b830061eabb4fd89359bd7f26cc19990479ad1b23abb59db363691b2e04c7a86e4d894000c8e9c7d08731c800000542f96559c17400000008e800011cb1e184128281b2c527ea0c846021b
  | 4 => 0x26123e040b16de5bb957b9b171720b3259113749030000e0e75d8a57b218b7dba41527671d99181a27210003045c44a057778228f000000000009bad550000d9aef6200022070f4c0001a200001bd34eeca4645f2f12edc3e788eba72dba257f75fe804a1305392c0d75683b887627ba
  | 5 => 0xd900002d8421694aa9d06e8165617a42ad0002db70001e24c1fc00000022a200000000000047d9bc9cd235cb4d0a30bec83884496fe8e19b98a3fdc5a0000250cb5100005965ae8ab091ae66a0ff5eb02810e7f114800016cc00000002d3c4f000020db0d50429ff42b14000036730b
  | 6 => 0x707854c0001d4629fd0f29cc000035f76529dc5821c2f48b5da000008c75ba777a9d71c2b8000663427fb46c00097a9b389eaccd00001ddb00030a60000000000151b759f0f5292c0000000f61420ae69604ce3fb9518a1d8572b64e659f92c0ecf75f7b4c7b372a55685836b00009d1
  | 7 => 0xc89da2952fb07b252acb898fa0dc65d0df903fa883457000078385744e740000002f5079e0000635c00006323a05d97608000000000013440000000954dd000000000325400000027b5b29a4747370000cb5b1d67f597d880a4dcb180800023ab5be302457018350df9ec1d9dbe55a5b
  | 8 => 0xc7a4b540714000000027552492a023f87da9da57461d706178d96afaa7fa0ffc6b6d9e49d317a0002c4c706f4df11c70a5488dd1e93900005bf8000855052086c547b59c6c7656e7136ae2e3c1a60a0b1401e3478f1159b75867c500000000002f20000362b97f6411c845c8d311e3ca
  | 9 => 0x9e3e4ec4b30258955aede00000000002f6800016362296f15069579400000007fecf0000002ed000062dac600007cf55d09254000b1a400000015a30000612860471c26dac5e013d7860003634ca4a859437a818660a9f4000000000033a341a4ef4cb3cc814115f6a20d4b783dbe879
  | 10 => 0x3a6933a493c8918d44517cad66abba6e6fc4912a2b00036592f203de2898b6b2c5a3e249dc366716d7731582735d9881348dd5e30bd75c2185231f81d61a951f3591b3ce6fe438f92c214d029d153c348d2292b16198bf24f74cd922d8bd0c38c000d9a9e546a64b3e1f84da00001231
  | 11 => 0xc674000994000000015a667b4ae500027e497f0edf6fc5293000064c0dd8556bcdb0260002d29d5b9c9e41cd16436ef42f9b288ae4eb48c740e16ef0001e4400000003f22b0019a102b020eccd1ba8c9b194d9195b0a013952188590d519ec401bb8738eb815a0abd2487078cd9b9756
  | 12 => 0x8c52c370de00007110000ac4a3a8000594d6340001b980000c6100026b2000062432d531d00027fb2a714cb0002af0babd3ef75067b7b75535e0906067bb3c000b1497bd0002f2dc275a92000134814ec83d8b1400092a67c40000fca78a5269512c000034d7622e2650a950d6d4
  | 13 => 0xabda7b000116c64d10887adcec2bef535c2a5f16d974dfcb2391a2e2b3e051acedd904bb87efa73e3d3b5a8a4460cf201cde58df0b3abda852d3b68312d9450d45db605a9853f6297c86d7128aa1adbc0ffe10d9d7c0000b8c3f1653441464d986ad6ac12b24c68a628c03a4
  | 14 => 0xbb227a18abc0001540000779c54500014954bc87d8cf2b247038a92fd1847eaa03d968b9b214d934de9b051802da1220770e94867c08c6ba1f454f7411170c08edf1c25834132a58f3839180006cf0000d179ad5a984f35000000065580007172af128d9a2756b8e610001224bec2893
  | 15 => 0x98ab425762cb2f7378c74c02151400030e2461f23d0a52720a7928998d2c43d13caaecd4822728674541b5ad9750e0f02b52d176f3a22ddbb67689c7472b2764ed0519f2c2784fa04bb40ed429600a94d0654cc0581ed4441f00009412fba000000000026b33734bd271d84886485d03
  | 16 => 0xbce0db28c64481be34ba9308e558c4bd61726206aeb0654fda4a63bd805a75e9b572ed2c57149ba2a5d7b7966a40db9fc461608429caa8114b52f5f347f074a6e4cd21cec451b65e97848009f57d98531128a4268baf59e66baa12b91c000bb44a0837cade2b609c6819553026886725
  | 17 => 0x353e187a836141a79e32321e01a109147d90700805715dbf94b6cd853d0ce4b6571ac671df1315de29d38cbe01c6df24a4c8c5a6e069d819a775f96a3fccd55d7a8129d4caee8a1218575081e52b7da6c60ff15db4f2d83913065db98e52ebeaf63122e9d79b291d5d07cb0ffb4adbf8
  | 18 => 0x1e3a2b31d21f6020664436f75ef8b49d5a99d28d1cae033d37286e2293d886e80b4e5cbeb1847d060800a232b0a9eef2f412e4529189b2fa1a001ec143a763b010870370a6375fe9c0805b55d3a4551a6254ac3cc541b82726cde0acaccafd0f1eaf2e800738fa287a0b88b8a9ac5207
  | 19 => 0xcee82a4b68cd77d4c50809f37234675a75c2c1efe07aecf5e244c924b4334ec686700f2c2eff7505df255d4931ca81e4f8553108ccf335d04e6aad527172554152301834ee2661aea302f917997e131589a088ad5884e9dbdf0be0c1eb3b77978d9b5649f5eb2d5fa9c0ee534c044795
  | 20 => 0xd9fdd772fa1e840000d0a8eee777704e3c00000000956f085d70f4969a35120cd3482c9342b69083a5161ed80004ad1c03d4e5971b0726e9a87cf2cc20aa34c5d47f1ac8605031307e56049cf32258f7d8f410fa11711991a6260300011683b605c211528e6c88d1adac92ea984dca01
  | 21 => 0x5239230903460aa0c4f4cb2acb06000048d75a298700000007ba6a05c1240000002acd2baf17d000151c1c7de4129996e4587c0002f02b982aec000636a787bc94000cbe03ac83ad5c41ac0000b694000b8b58990000e07927ab5839fa6c215699e83b062e43afc89f00003909fb4147
  | 22 => 0x454d60f2560000a9802aa00012fd0002778658000000000000000e263f9ade71ffcd8b42405b8322800021502eab5c23c30c4ce8f0788000c521327aa4d0cc0000a0d774d565c31e5d888340e582ac000000302700007e4000097cc0933678ab4b7fcdcd23acdf3500bd84000802608f
  | 23 => 0xcd5d06000028dc000191c624b4a8000175505ef36b4bea1f9cd3dee7000067a3ed40122398000000259c75895de1b2c3414b834e990780004fe5cf82874dfd799d0cd88907e816d0000796c20b000123b51e800017e80005aadcd4af600008cb8000000164d0001928396c0004740194
  | 24 => 0xa9693e7bde6dd87ff069949ab45a1b4ebb2d3eda1097865702a3da61c349f3c54292667f4000d175f2a86dd30cb6be4b0f460879f6288995be9749101b32b26a800ae31eec4900009a8953cfa1039b191786f613795c0001b80b5f5afb02a7e7124a0cb85783b14000b9084b042cca68
  | 25 => 0x9dc03d5307733714e49abb40a300ce364a8a8773a2cd0a21a9b7762a6408000387d2a8761c444c4b62080000000cb4af303a5454e89155ab000324f7c00000000000091fee11ccfd0f8145220ea528dc80360eed8bf04d2135cbbc000328100000004efc0000000000000145ca869dfa
  | 26 => 0xa2856b3708eba898cf1208c54dfb012ef75cf3ebde25403fe3eaa1f76eeac74475e3aa0c54b0532845ef530643c6ad4096c21c57aba1c000ce535d60000000d718e75640000064dc1fe0001931bb040002630000378d61c00006ec00000000003020b37e28db50ad53d30d9c11fcda50
  | 27 => 0x543264d7b5d8ce3de743d55e93e61e1e38fa4b08205b6d01ec84c27d57b98643a5cee36fa2265124000099e0f90008605ab745d94360b2504fc71213503263655d8af00017e87db876f9951141630746f2e01dd15cd9cc12f59e6e3ea01e89b448269680701543c8bec85289163e144d
  | 28 => 0x2bb1f0d428571fd3453b4a53c8f8bf433d7a3e5bdc10201418f56ce800000006f4a47cb0c9415864d62000017cdae2a332852a66e0f0f10900028bc65ed26e0001f56cfd6a72d36f4f8000249b0a120f9000000090ae4de0cdedda8ec02b965a434a402b470a8e02f35ebec3a0002b61
  | 29 => 0x131ef6f6f561c066a6c078ab21380af800000026846893289b55d67208a2fae6d533c924ac51fb30044649505d428b410cc2d10dd760ebfe65e2e462b9943f029260d5abefe10002fb5000300a1abcaef3c38dd79eaace623cc7fabd164ab02975e5cbdf0ec139908126470778450822
  | 30 => 0x16d704300013dc00010130001d828ae85f8bd923a88ce710298332e70003681b71195fce04cbb0ac40003b85c4bb0925d176e00005d513bc67721ed6fb4000b560000bded8620000ec88fe9692c9b188ccca447e3c1937812f4c13b6c178f8eb72eea4c155b0001f0eaafea2e7208000
  | 31 => 0x984338880c94317b1e5110118350bceb4b0373f3764cf25b71982236c6dd0b101c1f279d749fbcd1223c46294bb8970000404566acd0f40028ec0006b2c0000002760062c0008de53b0ae580002bc9544af4623705140605dd34f600000008c1166d63f2c36377286702780004652632
  | _ => 0
def slotCodeData4_ : Nat → Nat
  | 0 => 0x4931ba0000bc30000cefcb3d05a15e7ab2dd817ed4a82a7a490793332fb00fd5593fe400000021e9a47c9d3a68c8320000000810534ac2402ac5b40d5d2c32916168d6f38fd830c00471bc5f85df9c1e4d80a162e9d1a78fe22e22064942433d96847deb2a599b040c9b9d4a706c
  | 1 => 0xa205e31203c000b8caef216f73555354000c596a35778c000372a6e00b9263abbc65cfa1de3506766f892c92d658a620ef38ea17e0bfa7a91e1261362551c9c49d43d0846fbcb24cc7c7b00674098e07618616c4358234db9100006a75badce2ca1667284d6d366a64321322854c0ea9
  | 2 => 0xa924000c630000074802c762166300000003994000000000000018c7a07cd4c96c800041a2bb034a000034f400000028b400034d51c1930779875523d5ef1200000000000000a5b13fb5b65972ab856a2762737e6b06fec14184760002ad9d45000075d45cc5d67501d5c013da42e299
  | 3 => 0x251d5bf3a856ed090f3dd00028fccaa40009be00008bd1c84000000082527b10001e2d0e0a6fd00015ce2c24000b6ee892a666a0f6ef14fa84b169f18fce021870000a08c0000001f9d0fd83cf9628000b668d8ca48896fac94d03bad9f97d305c583ad4b5d000000000033e126e0000
  | 4 => 0x361d78e3da619ea70493db105b0d638691d1ec81b3b580cc824e2fb100cdb7515f14afca1678439c8e108dc9b58658c000c46956283a8000536c38100020d1a845929000053683f14fe5ba8cc47f302f99a8544696d6ed600000000002942045973e06204f1d0d812f00034056f5ab72
  | 5 => 0x1c3756b84b5fe54af9ed5cd38156702427128f0e99b5d35a2137e17f00413616fbc5fc46d43df76ddb133de8d4a00016f17eccb5a5268cbe2aa2a981b02a76c572a8e5cc4f32a75417a6cb44b7482d27e18a40001c3dda529ba50f000052d1ad8cc6cff530675eeb76887cfa367493db
  | 6 => 0xb384cefd478720640ebb416d8b964be6115b7284d54f194ae0bee699c0bb0d76d35bd31b3f5f21acdc3c13e364110fda13c149afc4e24b1f17a8000389dba60801b340002b7d77a000084c6eb8359401a916b476cb7e4bcad0966b0001dff862e75423c0b22751000049e80009c7cadd
  | 7 => 0x6b58000000110e8b040009ed91f100009b57f2726d54daabb00032610e480009efa82fa58584c00010358c35932a15abee10c6c0c991f1a059b14b02c2256797e00008c7d4b83ba3572baaa1a44806b101018c5e48600c60000af34d8ca4a00f00001c5c73955533eab89cb3316148f7
  | 8 => 0x63ed0ea235b1db3bd8000000259a050c0000000181150d57f03f10ca000232863995bcb06ec8d5f3c00000023cb9066eb7d5f844f93720ee6a5d883d085b2595c713d7750de2290351b517aec5727ed92c7d05006710912aae0c56735ceb80c7e5416b287a3a7894e515747c90000de6
  | 9 => 0x2bca568000024000000000000840744f1d85549bb24fd2ca08fe334842766a249402ddc7d700018d1c3d121173f1bf08a4e95443b5996000000047b965c80d8c974436eb3ab94ded9c78af887896ddce1606f9e9cb4746691611325ab142d43a240300000000000cb51f26c0be186
  | 10 => 0x103065c66c0001ed46d079472dd2e3976d0e115470001484d8f81bc810f2de35a41d15c94d91ab1511124b899798001c1cea34d8bfc400057d173c621c37c328a84d46169f9c488f0f53c9a0a4f7c66dd4b10c4009d0b446f156d37c181f0000000719032f2466e4800000008f3ecfa
  | 11 => 0x2149ec8387000090480003b1e9b594b043c894d04e87a2e7457960026a7e8ed8400a3a5404d4b5ac80284ae34456b82a9036702e827bc738935659883381618816db98b3e0d95a5c4d034a84ec42e1f175158e67c331f51693040dbc523b2cc40bc213b48f61226b5f3e16cb91d18981
  | 12 => 0x9550000926859568d800049b44484de91a563fda09377de4752756f8b17ee7c680800030be38144526f4b12d3c12881ba3a1b0a9410280009c9b3be84101da46b12784214000b59000000020c72a74000a38c5790636bf9859613f6b77616d91e7a564b176a0fd42c53490d9768128d7
  | 13 => 0x1be99190a33b8b9010a31dd0cab5c9aac90c7aa813235bfb0c44c784c482bb67a666bd19a45d3b4ee1b228a1fb6af2ab306c1eaa6a8ef5cb3fd9cdd10ad6f2c628039c656379919f1b42f08ec5fc6069c3eb5d80001a070000c3f0000923839913851b08d8223e1ef8000cbf0000362
  | 14 => 0xc4311b2a62d9481d1e74e4af0fb85128368c4610bb0299ea932f564430b41a341b50b23b2d79c3d50c72a85343f300539002b5ea5189dd7f2254d058d4f578610ae3d87ca37bb7f81f34ff4000d4364e15bd2585d586713847ec77b261a5a3104465d6aa8395aa4ed60b1d1bb6792086
  | 15 => 0x740800099f02209e6ef16610605fc0d0c3245f31109b64d7c7db4d1e173e0de8cd00003974c53ca59807b14cab9a3169907a706ee1d29cec0000300651a9624fb939148e05a1995761d07568551d2f61f243a47dd3386ab354f31bcf8e4e8b7f71ae41b0dd96c20fee6224277266210e
  | 16 => 0x68531823d3d60a02eec809f8b46b320a13a266ad9f6016296a4ed8b07d2af912f8a72b936d14c34767dda93a3d214ad0629adce55bf5c5f2a6535232435d5ecf9cc8e1ef00236c4a291bbd682691f957809c831491d4b023d684c60c651cc47b726e4d695587b8f5eebe91ac469117e7
  | 17 => 0x51d2c66d62f60550e48b806b05cd7110fb912166350f656c835aee4dab597249cf95089c1ac2c565937975d2d05d2122a92e65a52841edc36ffc62bc2fd584b1f8160be7b3094895c1d13a151e935299c216f20f4639e7c7c088619ff19a7417cf039f716316088122d02c3e1b77f16e
  | 18 => 0x8aee306408766408f6e81a912fb282859d509ec5f99e5c58307398a73e28f2d8362db8d27241fd4d763f2a8e49724e629b1a4efbb60c967521c70a060e9d8d767d1fe6eb300b61f4353d90b25446883309e08664b01b13b6389d0cc914ebe2db5167a65c9b435445a7a5d0a2ac27f486
  | 19 => 0x996de8c83f852684a896a00007424ec800020060bd574661fa4fc37b00002e60944a4998b666f7d52b8246000376d18b64a2772cb024dbc463d0000b068bdc8b8483a4f62f902d9cb0e2c1284287d30150c6ef80a7173c7b41963581fdef14b5a74dd03058aa9f0eaf2720cddd2f2f59
  | 20 => 0xc86722f34e40006ca29fc2426d6da799d69b2dc9fa8354d564d9243e97db46243431eeb6100000002ca31ff8e43734a3df470971c687a56db252d3d6d5edce109040c2d0d39fb64c0007d1400086cc8300003645731a953cf41b65c63e8da8ce1e02a40f5bd589ad2ca3303057e272a3
  | 21 => 0x15bd6ad823333334040f314591dea34f929400050de1e5084074d4ef72bf00027d36ec4000735b1ac748d87cccc2ecebfa6c0509f80004088ccf2b78000438400000021cc000295d0002ba60001ca7773b2790f7111bcd9871008484c24d3b07e5f6c0950000000b4a1084641960b
  | 22 => 0x32b1118124966271300000002718555c0008f780000000000324f5593fcf2e0000315900016010000000d9a4000531e7c80000301000000086a400063a400000017e60002c5d0002261000363bb748885a5607f40000000000000072a0e6a8e72715a48644b7d92ee2bdc00000000000
  | 23 => 0x99470ed9020000000072b448f5ba5d2f399100701a33f670d0d015a52e3cd361434000d50284e08c0466000344ac77e8e258532a795a9a8c252d9130792f632e8ef85207ea9298891bf099046fc869f35140f3bdcd5b229000337d000105cc0658a86126649d22c000cc18000ad34cf5
  | 24 => 0x7ee2eae38c88c18d8688e2fdc1ca0d8345c7ca5ae5adddf071e3e0e03cfa4791ed09a03dc029c83e89965c1339b25feaa3c1a46233ef8000ce9c00061e43c64e480000f8800000021de5af176e0000697424a41606980000002eb2000000071ec000a35509e4d4c6e24ed57cac7e75c4
  | 25 => 0x5b3c0009df6b35931e1bc464c5b900021e77a888688cdd92f369737fd7bda0c36ea3c529c1bf6d4588af35c5525aa5f618a50112629bd486544af8e7760abd8162c51061132d74d40004c4000026894cd0ebb1a524b5fed8802ff2868efca000065f7e6c3700344d0cd77c00096a9395
  | 26 => 0xa0248213108687d9d1bde4390a848391e958c5d89476b49b33e908890081a39cd6eb03d9ee401b568000af5e7904864a9800000005f0d1968341da0575c661c1b447f53d67024afddd007eb26a0000126accd859b8ec000bbc0767000000000029d7ba3ad0b681400000021170de3498
  | 27 => 0x6524fae9348baa2c6f57413958110001808da20e362ce000067c9ed95ef2c0b8b097ea51dd0d589380000000000b1e560482c28f570080001cbd5265060000000161e00006d70001a1b6ca9e1737fa57c837ddee55417d3986b320122d5826afe2e606c716b44c6bb3119cbfca0f2ace
  | 28 => 0x7554f128f843d74a440faa2547f24a3a441593d9f808240002d28268b5b24226390000015a469ca5757b66f070e00024b99a020e9b38826d94cd3f815ee60702749c3d182fb9b4465552d6ecac388c36c4ad534c948902725e4b53106c00032e526428d42312c414576e4c0003862fcf
  | 29 => 0x2d192047a3e39f0002d2a89dcd149600e872331ee293a9246d1b80000001ceecae7430b705fa88c9d2592718c89d100f82000000083d4000d3834a50001612698dbc90ad000010bc0087dc26b06eee7964769128a45e7fe82bcf1fb06137f886c000b8040b500009e5b4563dd09317cb
  | 30 => 0x9e811664c0c3f06194c1ed2f81b24c666962578c4d36aa2ae610c00001e0dd200035fa1b847d64035a674b169c930180009c140003250b6a0000d02c3c868a000048cbc750c59e76d54a598fd99d12483b49a0b334ba80a6c4642f4510d1a978d3e1b4ece69d0d00b10816bdf12f267e
  | 31 => 0x70540000000fb30000000a6db558ac4b49463d40000000fb2000000090ee85f1d45cc382da40b2510000386c00017ce0c50002c39405ec0334b6a2f720634300014140c340008ee80000000000000121f0000000b3b12cb86592878cee4c58ebec1394781dd3b9068559dab6b1915b86
  | _ => 0
def slotCodeData5_ : Nat → Nat
  | 0 => 0x6489c5071cabff11a4561471d718d0685e257219baa2ada58ad11dda8b2018a773cc343d8ee7864908812a1f347b5840af6fdc5098d906a85a02a218d890febe2f4d37bdb49d1cc13526618ab3a020e1655fab15cac19fb84be739bc049540ca5bb4452dd3a1aff41c28549060000f24
  | 1 => 0xa2e62a498f1bcd3509b0697f9ea079d1fadb09732b7d866747fc9997a4e47b0641e7456b663a230f16bf9be8eff000320c736c00038dd613095d2b9b7ac00001d84b55a98000622c3b27c4595b3e2ecf08af2d5f2b5677a071b673a464000d18c64a0bd70a37e7a26cb1280005077157
  | 2 => 0xaeed27d0000c5a3274a90906c0005b3a54700000003684ce411b01f64a894a2bb00ea444c982520962e575701b84624229ab4c6b57f4985fcfac7c5736140d8de2c370e992fc224103239c33bb89521aea0fe5d2664a39b2df08aa065d745b75cfeb5908c5bafc140b3c2acf17d0a048
  | 3 => 0x6fa40000000be95b4c9776bdb5c5328e326d63093f0cd29a62f680000000f0200032e3caf61d646c583d21fc2734e280006c7d9b85c0f256be9c000cbf959ec8ceca82b082375a1a8f00000ca57f56503041d21516c1dbf0001782000000054af1fbd92969b9d0dd65a14b5c2ae57170
  | 4 => 0xb26e9375abaebb1801e75000298a0000c3781c40000ee6ecdaf3e7a25ff0d8f4ceca93129f2c8049c0000000f48ab429bc4a9a5af61ee2be7869a6b07f5d4fced811d80dd9ee709daf8406cefdacb981067fc00001a70812a01863c8ca3f35c200000001c530000000b6a901cd3b6581
  | 5 => 0xcb2817097348a635c351ac1128fb6d6d8b8aaa90c96cde8c73f3246207246148b40f262e512f77e5537b0a1a8e94fb28e56aa7672884308b57aeea10000000b0f62f93fd104b9299d6304dc0fd000364b20b989e0000f56d461a0bb0540005a91a3c3466467a1d0f6867f6f0f8b47126
  | 6 => 0xd216cf800035ff2b670ee82280002fad31b744edae000091fcd21a770cee986d7530e96e4809974bb0760001fdac15ddc46c5973b0f3a484b6d4da4398b5154f299dd2c5000056008447a345377862294b7f33dfaab598405cf3cd69ce62baebdf18becd875cb31b8aa60c8e5cee42eb
  | 7 => 0x34433032a94cf4624a0a58497343f36daf7400000015f0000118dc6fe3082c05593123e5d004b0d1000023e9000081c5480ca0009b1083ad1b880000d7f353800058a161b0000000a8980004955237b270f36d3f67932318604000000065e80004b75f4f8ba27049c24000c0cc000
  | 8 => 0x526232a000063c1b687290002a7a33281be81f008cba7c4eb9051e6b7099e1471f131a00003d48e900000dc80000001fddd558a601aee9b2498503f24da0ac734c000177c2c66870fd162f1d252852ab51d6b5a9a11c000b1080003089171000074c5f380000002f6e7914000
  | 9 => 0xcc382eca99e7817ac4bc10eed4c90000000366400000027ce8bd40004c78000000000080e459176d26c1492f3216c5dd30cb244471eef5ae1beaef48da96c915d9771000056462d5a710002ae95f5b5217f4cbb1625ec604bf8000c0ea2d910964e367c63a7843269236d00003d81fc3
  | 10 => 0x5e8876d4f9720e0b2f427827a5ba94a42cf4c844e30a5d152179d4806a433529ebae4eafbf1feaff430906189b239a0824cfcdea854b86913834000c7111789e54000442678c38c19bfc490597c27aebd00000000c9b34c898a95200000005f7c000a9bee411778000141d308000001e
  | 11 => 0x5302b860000000966e89a95e92e3b5999e600006ed1c9d72103c571300004fdb08e63da592873bac11602ebb1cd26bc0003ab759a0003038bafc0000000d630000a1e1b3000088c5a8e0976e7bb482385a9cd298000000000023fe53a669d1da5f38c9fc37951c98144cf63e36daa22f
  | 12 => 0xab7ef3cc9815700001c8b77b4dea1a52fad788d8045798000d79998700032362430000d2791f930134ef0722454b83e85d5dd505803732378dd80006fb22df000000043f00000001a755e1cc3bce24000caddc056ea1aa5d9611f4088ec35d9400000000db50ed631c120d694d68c000
  | 13 => 0x39604bf816c2bcbc0886220c440b000107d00001cdd51e4fda8f636b85434ca000000055180001e5c00000021ec7e9c1f13a04000995800000025a422f5482b88dce686f40002142ca21854da37d7d8dd3220000af2e869aa3602188aa7383d35c24027017c4a0437738ba96900034aa
  | 14 => 0xd86601a95e22687421ef221d4dc9832f41707c003a64440f9cfbc8b7b9c51ea7a921683249b8047998b30d38aac7f09598a36e3bcc5343a3ac702abbfd49b09c6ebfa4e98000c0c5925b2857ffad4035550ea0a32f0e9519249a6585cea3e93032c57e04148cf0941291918db578cf1d
  | 15 => 0x6ed914f2db89782a82c58a8c4ba76681cf624ca3921626596c6d503772f12a3772e53d19610657539ca32ed492c80eebd6d57762392d57ec71f802ed324dda6bdc9ec1431adc3049c7497c65193bcc6224f36dc967c3189da428e8ba79b85d11b5a15954da8647dfaa4c450866702560
  | 16 => 0xcf91ced1a99f58489f88d2e2d0a13cd5dc01ab0b22f5177a095ac7ad43d1e33be54b94761b4e017b4c0743ee5377fabe978ed623a05d09f27109047774bdb6f31f33c11c9c1bcd22d7bfbea958fb73836e33300051153bad45f30063a5f7a15ed69222ce82aae521461c1e07a97210a
  | 17 => 0x440d4e09590ab8876c27c0fc8b855ddd2f4ca88bad7c86a96c45dcbdd4383be117a6deabd35f75630c20aadb53d502a84a68030c82fc3502c1c91425baea4b00d045b96649743991886a564709d44765fb7597351814432294b14b263cf1a5ce68e787f219b3ef46b91d5dfd13b4070a
  | 18 => 0x338233d0001a3f0003519566635a2fea25e59a252b69b46dc51f4000c92efed29900004f8d806aa0e42541c219458b920d8e0c6ce04c200713f34cf018df67863008d870e1b681b40c9d8d55901572698035400033cf305b212fa300031bd000238e1a3000017f4ba87355c71b1034d0
  | 19 => 0x2c380001d9e4140d337864000977df1dab0c2c260e1b7374a01af499400040e5a0d0206dba00e2ea2a57d37361c8e9837a6ef6b3d568731174f42ff527f7095151d89e5e0c1901789dbb27bd9980003ac69cd2e4e1dfbb7e6d37dad608c94ce6d4ebe2827f507078247036abb9026
  | 20 => 0x48bd0cbc475d1b2450ae8cebe54e81c8bfec9ad826c0a00003d75c8c0001bb09040613b439f2f00000009c8d6190000000000182d4dd4000afb4d81000000098d800000000000002eda66b71d9349853d00014a86c541d9cddc25367801045a75ba100000003ac069d0003628685c713
  | 21 => 0xc47d566794f36cb800000c0c1c515cb920802a000052b313a63606f99aaa95e2fbc0008da4000b94400000031f6832ae20b222510175b497c13800027c36860000000c87ed8c5000c909dbf6005f43075792e8211790000a6ac000bc21bc600005e156bc0000000c59d768b270002eba
  | 22 => 0xa0b177d2c2b01d0002fe300000000002eeda78eb946f6c0ec797400000018b90000000c155299a6928b800016b4000000000000003eeccc50002f4dd0476782624a6aaca87528e30f8e5efe5200c2cce5c16c9bfa1788c42b06e7900032640ea5fe8aa2460ea77ec8986e5e3e2052391
  | 23 => 0x2a25ce492c20265da3577497283d4149a9100026593b3d3a29597324904c000d6b6bf8101c4ac7385ffa8fbb003000201d00000000c390e800030094eeec61000046e0000000057abc900012cd0000000c012b565768d5f010c4644605a31b95c10602e90406d4e49800000000000000
  | 24 => 0x18520000d6280fcc1f7b2ddd200014dc4869ca530411340002dafbf7c000692eb4056a974810411621dca446554c2bd000140f7e400003201374a989b7835ce288d4bf5deb2d80004e1c3e370dad088ea64f101a3016c128f88aaf00005e358747badb834b021584fdb338cc11c0d
  | 25 => 0x8e9645c50c000c9d80000002c5c6671383a40a234c748ddb046c0002ffee3ad5a9fc689cc000acbeb0f46701a4632ad495e33269813a29f5c085aabc7c000511478acf71a96cc670c511082bf88b00196a4ed8b963714158e8000982aba74b680005ac266dc6ac2d743d6dc87edf2e4
  | 26 => 0x1ce955e146a4b317293d3cf0c6733e1800000009cc98c1ca661150a529e11cf7f38000ace67ec5e40ccebb6d8deaeba4cd0002289a43e8c84092e10137b1a43fde38700028aa08100007a24000968c00027cc3eb0000c570a8c00021621aa5c6400000008bb00022c37a8cca7c2889d7
  | 27 => 0x4a5c932e0c000000188400018300000b9e1bf4000a017063030366d067af9400009bd2bc0781000000054a25c0ce32526327b05900007d3998ee9cd2b081a0001edc0000dc1000071b0000000c99e0a41e9000002e105900035bb7bf111f31d64059b680000001efa8dc4535a5aed4b
  | 28 => 0x28874e2a2dd699283c0007d60c8f0e580008a709c284a54a48cb199f0000000a359330ab882a899cc0009f5e7d6295903d642c17607bae58648099e000035cd6918a97886ef3020029f53ff1b697157f0932c0005e4c000b34923ebdc40005ecc000ce8000083b63f13fc525fbc688b3
  | 29 => 0x47c85f4d0389cf277419c0ff1f739b9d24ea6000005b70dbd0ef00000002ba13f1e642c6f800065d8abf18ee8962273246d47235569780000e246330000000ccf1b500002d620002a240a040001b0cdc642b8e4e5bea0ec79e46c5000166e0000000bba065e0002c500000000526de48
  | 30 => 0x3fbeb3e4e0485abc6e7148934f409d015f78b807c323fe0f009aa374383120945ddd3c3df095c2011b20230b477312e45bc2cf536c5b277598fe461b5bb4595e69a22747416c8c958a5bb1b169acf69ee108d66735d21f82fe1f8700d8c85ad769b7000015a2b900003ee80003ac87cb
  | 31 => 0x3ac000036b10f66500003a39e0f0002f49006e0f300000004d80faf00000006b1c540bee2d12c71ef60a2609a7b7a2fa10000745424ebe400021e4ba580008dbd69e2750f9d83860ba8d824499069daa0ef681c6574000bde2b73113a7d4b628b9559f980f4c26f7a167a79a7825f2b
  | _ => 0
def slotCodeData6_ : Nat → Nat
  | 0 => 0x13823672ec0f789a825350a231f1b78e023132cafacaea8b57758c38000231b0002c17000129708f282dce44fa22058000000332d00000e48bde6ec5c25ac52618000415ad5bc2b58900000ad35322861abdee028c51b2f0000f9c0002a9c000000026090981b58157b45ad079578000
  | 1 => 0xc1c8d0765c4af1e88c366a91c7855a503a2f3091d08becdb3a525e2b3b5c603a288acccc8075813ece0c8e0000b85d9d700000007b961d03d45ed8c5df42d733f38acfba01e616eea5a4273845621a18a288000388b0f10002fd8d9b0000aa857d9859ada26b89f760000000d636345
  | 2 => 0xd1fa4155f723860d6e53a0002c0200028bb00003913f961270002ec70002789ab04a50474a8d36c9c7c70001d91745b2e591542f8110d7da4b0c124000080a21d2ba5b051351d6031257f9a3b9a7e81f80000806000048e90d80006e109f8408ddbb02cea0074b0c7ab3695458ae267b
  | 3 => 0x3da1832e7000029d0bf327f400014e33b0000175f40631340002d01c220c402f1dc866678c31053150d8bf821753a0ef2416c00050a1006a3ceeeaaaa151ab645f7fb7e121d8adcbbd4e70457c172246c5fc0000000000472255cba1838bd93e22e676c98ecfc728700009f683098d9
  | 4 => 0x2b8c6f5c20efe5cb5d28698a4b32240400000014a62d5816304b970b3192b87da28000000100549e642e095278d1cca07e57ced1d000116300005628b180000002910bf780001e65a86a908000d3863f8a1c247a8480000402f0a45fba4fb46754b2427202c149723e94b463ac55985c
  | 5 => 0xa13181dbfa024b000105371e838029c5a348da11470000d3b6a6af0773a8616591b0bb4f220036eaae970ada528835d95070ac5c575900004f1528910ce93a658400081ea02a209cf09d6554d12dd35b90000000d7059a300034d293d64582edce0b0002ca0bea282a47755373f85eba
  | 6 => 0xc5d171400000009b84000d58000cb4fb2177fc2de4835a74b0000000c6c57291fa5eae0001e6300000000000dd4732c46a91cdfa434380005639b3d236947360e539700000004309dacc459bc143607d514912ded0540000003218aef0000000277900000000002e2c96387dc51bdbd8
  | 7 => 0xaf420da5b48736da2f0294df032a134410b8fdc000179b42c186649029dcab100026a7703020c96f880bc74e33f54fd6a06337555908f09900ae5ca6e79d78866400032184d30039db1b93eb9cc6654057ab645341770f0cc981f5000080c937631aa7303120000da90001a11adc05d3
  | 8 => 0x2bd2075097b3e09a53363b55af337c1862a4e3c7f0291edffb8ab51348280000002227670800013c00d4000000061c4de4898d2b7bbb3130806749099a07894ea129528380000a2ea5746a748d74c40005c008d2623487e00000004dc00009fc494cac6ad9617c717c24a85be2ce53d9
  | 9 => 0x5f02afc7c658cf1331912c4e55c0b450572000203c00011aa02860c18e59b95100dfde27b98aeb7cdd12195302d59e042983761197b16d102e5e843bd290a45ec551601fde7e90180008d08f7189024ae5374090000000063e460b90e62f2380c215a4d4c7fbdcd9fabc4c89b0001376
  | 10 => 0x930d9775bf5b1a1d1063e253df0b0d0d542c212dcf50052670b5218aa8c965f74680000000e153a99868a4e05c6383db1ca2cd6c159504cd4aa8000d934f3059780002f9b298521ea9f000000076c856a0003341c344fc66dfc7029db74ae63dc0b97962a275924ef10000000542e7e7
  | 11 => 0x97fddc123ca2b5a041a6f00010e9000000000035bc1a114838182cfb80221be688e9720003179000034cbc11366812cc3da1800e1b71abdc51267daa09f22e97b2fea33b69ba731c8119542220233a8b6264a507000125323d0e6ed80c740cdc4ab2a6a560d194b35fbea5f446918118
  | 12 => 0x98942c3000000000030a1c53239a00014f85ff6946c33c000d1b40001dd93017ac800090fc0003d2ef9fc8b680d1f306eb701858d0000b72b1935d12d6631e00013ed3b24000000016f88b7208b25995e814e4171caa2f1201e4ac078ec12a7c63a6d7f6b5ebb08accd4fcf3d3dde0a9
  | 13 => 0x4cd8000590274f6de97fb71382c898d2228bf6f0940a15ab7000077d8f45d3b5e955f9986ce313e04eac3f6a0140d11d98474672d3ba533e07fc0002f3dd2bc6a62744597597b5c4b34b16a2128a5ee24238e434b27a62334dd48d9900be10054abe63f52ce3df9ac987549110576f00
  | 14 => 0xb740000000306a2bc4acd923522cc4460f71e61033293d9d85f18efc2ab40006e340006738000b11c00070e0a4e3bd49d2b484b9805fc0001af84da000117eb491aacbd55b4700002f07e2e845359d77b695f4f0d3dcbb3878ec5b7b8529d1ab229dad554279754000672c7adcb62bfc
  | 15 => 0x34c593e6c622cc3324af735ea4ca00018bb9544a339e9aa5ebb412e10002c34cb9a76759ce40f950b0616f392ca0f5adf599391d6d00a4997c481a27c0c1673554000000257b276132eb0a80000000000d7ec0007e34a5e0000000168b3f8077c0007116c22000265d77900000000000
  | 16 => 0x538690585da9080a85e0c8e4c000b5fc000b8d6f060001e0da448f5847a1fa5000000033d920ea5b43210000c8c05bb0546d3e1ce000355f8684884bbe8000ba8efd49e49e10861015541a819d490dac20e840004501c3034bde5978d07f53f802660002a1045674749b907251f1abba
  | 17 => 0x75cdf379500000c785b56bbbe6f9b32d22e3eded7a3fab262ac7d55132e800066a35a87e1856e2484728a360226a66b4b55408a69a794000864aae7c32755c818d5d8a21740329659aa000084f2d24fe77fe4000964c00038b27831fedfbfd90ec4f167c5a995351ebbf767176b00000
  | 18 => 0x174aeb47a6289738bf5f1d160bbe982076394def97c4d716788ce287a708048ad5c00093440005ee11159bd9f63ab71fe4d95cdbf5e0e4d8413000052781e651408fbb96d1f7504227a0aa4bcd22e4f1ecc5410206b8000b85a4ceb3e4236ca9b64c5f82409658abce74de97f9933146
  | 19 => 0x75154de8e8c000afab050d84749ad8496cbcbac058a6231f300000000001e27d85ed0495db096371e62c1e0e968aa08354747f416917a0bec3ad29e46bd72f899995330a762d9ee10bf5089763c1ad788d152b66003ea0a4c9051253ae8ae7c419d35cc2c5921e6cfe17713f4cd75e69
  | 20 => 0x8c4ec16bedd0a05edad99a1fd12a54e9e7a65995c6d4f8000000000000027d595e4808d6c70daba80bb8c4295790001f522180b4e50b6f37875000000005133e0c4d41a39c540002c9dc134b2a55d42825b005ddb9ada128f608c07c2b624000000000027730001df882a34f115669c0
  | 21 => 0x7081e3ab214f74b1ca75a00c491e465d10085adccd7f5c9ca40800000002c788d62c3018305888fb0608b1ccde5b958d0db0feb534431e4e109b1a3b24af2a3c5edf712cdcefabff46900035690002b08a81b5ed8fd30dc00004ae73819c331c677435b400000005ec5ecaf98248073d
  | 22 => 0xb0056f076e68ef32e285c000015b6340f1b9bb505a0003032639c33f00000000000bdd91daf5ada16c005fcf1337f660b955cccd155b87fd0a43455a50c000c2e893512cae8277ec2c189c1f2063e8e8c737f590080719c3142a6e73212b2a2f563e6aca2f600021c1cbf40004c3c158
  | 23 => 0x9678000c556979afb2ca7c64ca7999e9091639644f4e922470001202c78c000000041fa3b321c6a2b4c5a7f4e969358dae3fb18509f45d4910ec00045b4a10623c86b03a5f2d507094900008e043dad19a6884f66f0c0846f8a3940002a2261e1cc46ac0000777c0000002aef0b7c24e
  | 24 => 0x39990cf4371f2eb8e4ca8229cd27a559a66849545506f400088ac2835f898ef00007a13f1079028f8dde6508f6db72e2d56da29ec1a1854723d4f534db11790002adeb47e19c44f000046f4d3f4bccb17b43d4384ab6e382faab7c570cc27d7333d579c9a7eb2ce6bb0002e131be2424
  | 25 => 0xbab400061104804d42aeba4a1fc1000264a0000cde2f6727e4b4b240d97000028c8eca00031b44b1ebc0863800037d2e0e42641ba0f235c000000000000000507c61078448887a474b37564000ba54000d15e093462000011c0f7600011c175f70980003581501c45ac86c41db6f8a28
  | 26 => 0x54b0ad868dc00017d99cc385d5100001fbc0003409d67083971d44590000d95a6b10dbaa2c000856c7490002b17af232a1148da5100000008549f05c8fd8fe000020f0c12b48546038826aab7a00000004a200001aa80006569e287bc00000000fdd822c86564b4a2b8ad8d98ae4b349
  | 27 => 0x98798150ad4c0ece1df93be74fc064ac00039095676f15a354536487a3f579b5de411a52ea39d06a0e7a6ae873fafdc13e58a61438b2b27205d0a4305426d7000262461f80006af5c808b709176d8520cabfa312000008e73e9b0b19b91950acd533d9a156c1d58000d6227e63d0b243
  | 28 => 0x6505d198b9dc49b818bd8b15dd47a2783e41641e8740c30b79bb99e23af2e7271c306611008dc18dda553f5af3e000110a62983351bc8000aabc0000000bd7893d221c53d15d11c83d841be736337ec910000dd17ddd24ca4519e56d2c000627caa10001aaf0001236b7663ae166885e
  | 29 => 0x30e6ad4ba4cd866b0e7c7d106dfb993cf59bedae9994600000059b0e87c0c9100028b1a67b0b1d5be49dafa35e7470c000cba8743af144869d95c91000089400000008a680006746e1565f0fdfd12c000313d1ec88d59ac0002a9b326345301deb52374f42633e06404d35bd187d6e64
  | 30 => 0x450ce52d431e1688c345b3ef2f3dac8345f544e87200beb3a0002d4cd9e8000d5e54a100000001c32b2dd4f0000429a94510e158bbdd33147482b230001b24a1f4bdf8ac86cd93cf1e51dc55ea000000057c40ff38451d92200efe280c03d00028c38bc04a3395ecbd00018230001083
  | 31 => 0x40a834f1a40f3c6aee9c356d40004c9a5e60002b459bfabdb755a8191e3665a13d00009e444587ef69bebdf8000010888d518508b21554ce880586e922d7ab9d5ee8fa4b5b899d600008ddceb753bab7408c838c9cbc8a30ed9c94b6acbcbd286841718625a976a99b136dc047b4cc87
  | _ => 0
def slotCodeData7_ : Nat → Nat
  | 0 => 0xc3cd72b2b688cf5cdeba20002d0972ec000c840055320e28e3a8df75249eab10002f18b5f5249043f1634686ee78c5b1c30b74000c36ceda74d80ed2130000c1e1e6d050358f1114d6890123204f24a127e668718591c359bae217ba01233ab326bdd3344112abb2309ab41d82f79371
  | 1 => 0x3cacd847530000c4369de21a600b7a7c1d4d7d95dd07580008d7120399909cb000075f1b98000bd489ae871d0498bf50750000000129096335b800096ec754cb39609c2e5b1004433120002b02a1d7424d7ccea5c4b000080f556886557a328b0c0dc2a2242c51c0aa8e2f2396750000
  | 2 => 0x79d9c5e8ed6481cf38a29297effd8aa2b897a4a4b829170e7d9f1da30b566c7195d5b4d67d35b1b44280a4008d52feeb852e6a4b70efc420567c2ca42f8ca694c05b1d0375b2260cef7d7b16c650388c80003018afee4424557273be3f09c0001ca0d1cb2b37fba92a2f45eac1e51f36
  | 3 => 0x16e9b43982ec3324551b64aeeffe4bfef83cf68f6600006e51ccc0000000000d9c74ab268c000000201f2a49ab476fa6c466958c287c4969b318c55cd02028b436e3e27f000012af2590001df2387418730fb5cbb0840000281280262af82c41a17b8479e136e71aeec3a88fca1e1025
  | 4 => 0x7875a8bd91114e46f893747900458b758b6930665e37fe488053e2d32505c97000207402aef290a6c6e76e6df15811c659602d0d20002a2cad9481d8bb61741bbe6275e5a586803206ec0ddc07d609333a69655f8101043477f3f79ae74ad5ae17325e1037e63a0c2a4619e70
  | 5 => 0x91e10a70002764a34637e2d48636793e6ac36e40001e9f649144000000004fb66c50d66cc4f2fbf8aee4a3027d988c853310542ef00013cc1dfc000b89497b0000000000337873d71624e2c0009031e6290a4b2dc875d06c3873462bd7592bc2ebe5bd6c000000153992843330002a6a
  | 6 => 0x4b96da89afd5c7a44c00086993e91682457ac1aa70000171e2918000bebc00077f00a2000000000025f2b5d5a2089063595859622000305ac854359c97071d000128a4d6220c00014c422ad9a4000168565170fe159da601c481c20002ba4000339c6ebc000d00515833dc00014c1a81
  | 7 => 0x348a681754142f4e02c9a87271f700000000000000000292392000008870e24000367679ce1dc0000000b47b5f85c1a8f400003570001691000058bc66986c956a91a3c10000000302136740001310328aeb04fa04b477700018f279dc0002ae80007fcc000382800046ccde8142b2e8
  | 8 => 0xbb8c9900000005d77422808a0c9b5289f95c680000894000d95000007b400084ae7eebbee8666afa5a54d575b83f3eabed448000014f37287484fe5cb734ba6bcde744071cacd7b452b3f00005f0486a86bd24133a1a38a8a31c91f8c000b51f4bd858192e0002f320002e9273e7280
  | 9 => 0x2498000140756361d946b0136eee19c00006ba80000001cff7ee636e00017b0ad89b669c3ac3e20fd75b1b51406c329317392256e4e0861a8be2b9d81e4000bf47526c454000a5bf33400005a800019ea000165a2577670aa300007e280003b956aa00023c9000000071b655dc881359
  | 10 => 0x37b916951940003e5800077c25d9000000000002081d65c3f2946ba0471800066f40007b8016ba4c800037ac5ae9b24e20c744000140abf4a418cec3ec51b0000357a99220c80d1f2443a1aaa64b1148189aa5e5cdc205604fc15c2559521039d13504eb1b8183c00053d136f46a0000
  | 11 => 0x204000076bc0000002a68b5ec91a000136571662750e380007b3a2a52385ceb397921ecfee69c3c3354419f301f2100e3d9f327b945ea8f747cd0892f55f74c0fc0008331f3ab4c8692d2d0f9700016577ca8ef0ad7211a000000020d2fd565ff38f235085dca36aca804767e0f94ece
  | 12 => 0x74355b1c85b5e3ce94cb4d95acd40001c118546ae00002213d0667681608bb4b7c867d04c97336bc8768af8e42c62f545260baa482d0a4af8b1c9513b346830002cbf51205dab3bc000c76918ccfd1e2060d61dd96e6d593b0d5cc73a4306ab6319fd424d3eafac3af64543f941e5f72
  | 13 => 0x9e8de904db4bca504645105900000000650be885940000d1b42bc0009845edd3dec74115483383850f466a0b438c1c08e24fe8ed100018add7ae3821e714c5b3560cf6e5e0618c254bcc4e0000d9d61c5000000007dc9688b7883e72a409853c4e490000b583b303a08f6a324944953d
  | 14 => 0xc9240001f380000000000552c00093a50ec087c886aca61672f8dab30000000391c3d23c1c66f6ed56d8ad0ee4a28080009708a9a1e49acd40692ae0002ac71b247bfb97c5c7286b15a81795d229cc49fc8d67db4cb0a55000167c00007b300034bb9a44000334dfff00000004e3724a
  | 15 => 0xb9f515f62eb5679fe91d48e373d98e65b91856411258ef382c888f37ac35adac4c913e9136133b0460966c3116fc65d7444e4c586ad24f5c00000714f1ebf64000000b930125766e1a02fd54fca51355a5555ee62d8b113573c000000279e0000fff8964ed47229444a34abc793e95f5
  | 16 => 0x4f97a0eb4f0a64b1c66422ee046689f7902618c6a0000d6db24d356b428775499cd01dbe3c24e9f76dc668ed9f596b0000000925034691c0d255a300006b629bb664e60254a64aad41a2a065bd52f08a8265944c0f04b200000000cc2911c000a7da30ad29d2225a8f2f2ad9056d
  | 17 => 0x9eb572219127c2b49609725f87805c763e72efe1213f91fc70002d1cc005ff1c7bc0003da93dab86865a01716b91c88000a7202477d009ad0000218c930f5b000049e9394000b1234082ca293d8b2c3e8a5ec2138641b904bc249c55c4400da0cc5800000005228d163d265fa693c9bb
  | 18 => 0x25273d150a983d86c734d5d4b927c527281d6954185c320778e292cb1447c4ddfa12de6a3bcb4d7c48d4ac2b60a246592b4afdab92d85541dc43d1740003bee9e07b7c000a67581b970c000702dafe5c9c000c9f400012d9690000051605d701e41e2dee885917b95a276a36df284
  | 19 => 0x37400068ee86a0a4b4cc6ecc00000000006c3c0001cf19f79209f1a0f10000634f64e0000000000310ecbc4239000000053b06fe30900007df2bb9b8a560066d00000002d80d639c1c3db8000a71a86500014422bfb50b12c542cae6da3d0c704410001a566c0c000026a5f4be72538
  | 20 => 0x19269a08ad25ee4192e50cdd01711159bc2895a57348a5840000232267790d356e8462740617cd35c7ec0003325590df5bcb0e87e0edc000a03a3eb44780002b4662e0002318c6040006c752d90002a1950db55b00000d0a144d065fd8aa20868770a429824c5168887de173a99dc421
  | 21 => 0x253ba11801f21db16477cc6816d14cfa00000003362bcd4899d7000020fd70a30be035d9b652fd29a9310fd30002248a3c8000875c38f000032d7ca2c9fca80461a2969bf5d0c91c6ce99655791ac855de5a25ea0000ab13517b81c7644d5ddb5cc2accc06d80005500db0000067e
  | 22 => 0xcc78491000040900028ca00000003c51f8344c000000013c4c1633757999beb00000006902fee0cd8000b974a4c104c599c67809f12b44682e2d74ed590000770029e000223fb7e532830b80001c120bb439b08e1d3c0ce3a7dbf23a100000000d6c064679f000227800000003626f41
  | 23 => 0xb6d2e084c6318e69d0c039ef452a28d112731104e436f2ab24b8b0ce41de748d5781857329c3b9258000a91e88d16ec0000000bf6985c25f1ec519216734643f5ca1100008ed8b680000000c2663a8428a904000a5e80000002fda8769517add6080224f1cb6e3ae1f9f602a50002802
  | 24 => 0x59d26c618180008dc25e938034470a633800000caa82700004f41d609afb29047ea1798441112ab2051b1d38e4f0209bcf1cb46ad00001ab2960062a856c3110a988acd4c0000e792ea565c000000331a0000000370c0006bbdb1b4bb671c5a7000001acc6d66fb56da9301890001cda
  | 25 => 0xa9ec6250000e7ca93e7117854000cec80000000f9a03364379d880000000d4188e59185808bab0b3628356342919070e347ec9e3c0dfc0fb1a35caa000012a9e2b1f0000000079ed0b900028cf707c000a26c9e99d6c00000030a926021e600a7345ba614a712630391909f6905987a5
  | 26 => 0x61463fb87f4000000000000015899c88000287cdaf69c0b44142e26717a221dc26aef9b8de10517ec000b9a1639d20ed1a19200000ea00004f387f76b9c000622000001903a74ce2f9a13b8000bd7800018a354cb6ca7560000000d72000019d40009cf40008962ba336d8000d31007a
  | 27 => 0x15b2e88c2a92d02772f1c7d19c345f45669b9facd8bd616a841c408500000003a257760002caf00012121878000000204db2d2d23241493a71544c0c5515e2467dcf295f89676a140006977151b1180004ec5bfe32cf0c4cc7668a4a6f297bff31c535e742bcb3454aca231deaadd2d3
  | 28 => 0x6b6d32f572ee59790eebc51b9e3929af5b73b98f551aa62bd1065d0a744047b0c0c0007c25d248395e125832bc14b98000c5c400000000006b40ad7000164bd0aac2947955323f15c5f37dc0001704e9100002e9c62e042697c00000000006e50000ccbb49b0000000000134b9a9980d
  | 29 => 0x70dc94d381b5ca5b8a1c26f6511a2a9a539d322e6000026f11acb286435cc25954800020a58c4c3e0000d0ba2ef3c8c0008300a4d00022fb3c84b1993c278b66603675491535331f20db54ab930864e56282853c8fcb33ad0a48596d2400000007a68d393a100005512e400000002311
  | 30 => 0x476c2f6d59acca771800070b5be170bc0006b98d320002f5635f8e71d19f5b52ec9738d8997cc21ed96e68a800071aa5b12cc441805ddc4f243d78a0001b8b82fc0006cd55430000f870001f1604c40003a0eafbd36a62f000214600250039eff1ff2b20ce235bcc3007e6b54ba368df
  | 31 => 0x572a90d00011451da8000441ddf4892c000000161d89ac0000129ade02f9e8a7d1d2a55e855646bd540c7d6aeca771605400020c3d37360c888cf73770c3db7b24000947c00085880001b644c57d051e12cb9749b6b06a25330a23344f4318a563b8b7be9951a8360b6f9c00039edcd0
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
def slotCode (i : Nat) : Nat := (slotCodeData (i/64) >>> (14*(i % 64))) &&& 16383
def recipeData0_ : Nat → Nat
  | 0 => 0x90054020016008005401c0160070054018016006005402800e00a003402400e009003402000e008003401c00e007003401800e006003401400e005003402800a00a002402400a009002402000a008002401c00a007002401800a006002401400a005002400c00a00300240240050080018020005007001801c00500600180180050050018014005003001800c005002001800800500a00080280010080008020001007000801c00100600080180010050008014001003000800c001002000800800100100080040010040018010002
  | 1 => 0x18007406001a0180064060016018005406000e0180034060009018001806000504500a8114029045009811402504500881140210450068114019045003811400d04500281140090450018114005045000811400103100a80c402903100980c402503100780c401d03100680c401903100580c401503100380c400d03100180c400503100080c400100a009402802200a0084024022009008402801e00a007402401e009007402001e008007402801a00a006402401a009006402001a008006401c01a007006402801600a0054024016
  | 2 => 0x5b005416c00e05b003416c00905b001403c02a00f008803c01e00f007403c01a00f005803c01500f002803c00900f001803c00503c00a80f002603c00940f001e03c00740f001a03c00640f001603c00540f000a03c00240f000603c00140f000203c000404c02a01300a404c022013008404c01e013007404c016013005404c00e013003404c00a013002404c00601300141000260400094100022040008410001e040007410001a0400064100016040005410000a0400024100006040000810000101800a8060029018009406001e
  | 3 => 0x3900240e400503900080e400105200981480250520088148021052007814801d0520058148015052003814800a052002414800605200080c802a03200a40c802203200840c801e03200740c801a03200640c801603200540c800e03200340c800603200140c800201e009807802501e008807802101e007807801d01e006807801901e005807801501e002807800901e000807800104b009412c02204b008412c01d04b006812c01904b003812c00d04b002812c00904b000812c00105b00a416c01e05b007416c01a05b006416c016
  | 4 => 0x4a006812800e04a002812800604a000812800103f00a40fc02103f00780fc01d03f00640fc01603f00540fc00903f001410c029043009810c025043008810c021043007410c00d043002810c009043001810c005043000810c00103400980d002203400840d001e03400740d001a03400580d001503400380d000603400080d000102900a80a402902900980a402502900840a401e02900740a401902900580a401502900140a400202900040e402a03900a40e402603900940e402203900840e401e03900740e401603900540e400a
  | 5 => 0x46001811800504600081180010210094084022021008408401e0210074084016021005408400e021003408400a021002408400200d008803402100d007803401d00d006803401600d005403400e00d001803400503a00a80e802603a00940e802203a00680e801903a00580e801503a00280e800903a00180e800503a000817802205e008417801e05e007417801a05e005817800e05e002804802901200940480210120074048019012003804800d0120028048009012001804800504a009812802504a008812802104a007812801d
  | 6 => 0x500088140021050007814001d0500058140015050003814000d050002814000602800a80a002602800880a001e02800680a001902800580a001502800180a0005028000805002a01400a4050025014008405001e0140074050015014003405000a0140024050006014001415402a05500a41540250550068154019055005415400e0550034154009055001815400505500041040250410088104021041007810401d0410064104015041002410400104600a8118026046009411801e046007411801a046006411800e0460028118009
  | 7 => 0x420028108009042001810800202e00a80b802602e00880b802102e00680b801902e00580b801502e00380b800602e00080f802203e00780f801a03e00580f801503e00280f800603e00140400290100094040021010007804001d0100064040015010002404000503300a40cc02103300780cc01d03300680cc01903300580cc01503300340cc00603300140dc02903700940dc02203700840dc01d03700640dc00903700140dc001023009808c025023008808c021023006808c016023005408c00e023002808c009023000808c001
  | 8 => 0x2b00340ac00502b0004160022058008416001a058005816000e0580028160006058000811002a0440098110025044008811001a044003811000a044001811000201c009407002101c007807001d01c006807001901c005807001501c003407000201c0004124029049008412401d049006412400d049002412400503500940d402103500780d401d03500680d401903500540d400d035000405402a01500a4054022015008405401a0150058054015015003805400a015001810802a0420098108022042007810801d042003810800d
  | 9 => 0x2d00840b401e02d00740b401502d00340b400502d0004088025022008408801e02200740880150220034088009022000416801e05a007416801a05a005816800e05a002816800605a001413c02904f009413c01d04f005413c00d04f002413c00504f0004098029026009409801d026006809801902600580980150260034098009026000414c025053008814c021053007814c01d053005414c00d053002414c00101700a805c029017007805c01a017005805c00e017002805c00601700140ac02902b00940ac02102b00740ac019
  | 10 => 0x4e007813801604e003813800a04e002413800604e000806802101a007806801d01a006406801501a003406800904700a411c025047007411c019047003411c009047001411c00101f009407c02201f007807c01a01f003807c00d01f002807c00901f000802c02200b007802c01a00b005802c01500b003802c00a04c00a813002604c008813002104c005813000e04c002813000604c00080e002a03800980e002203800780e001603800280e000603800081580220560068158016056003815800a056001815800202d00a40b4025
  | 11 => 0xc009403002100c007403001900c005403000d00c002415002a054009815001a054005815000e054002815000605400080b002a02c00980b002202c00780b001602c00380b000602c00081640250590084164019059005416400d059002416400103000a80c002603000780c001a03000580c000e03000180c0002025009809401e0250068094016025003809400a025002409400205d009417401d05d006417401505d003417400905d00040580290160084058019016005405800d0160028058009016001805800504e00a8138026
  | 12 => 0x240084090019024005409000d0240024090001019008806401e0190068064016019003806400a05100a4144021051007814401d051005414400d051002414400503d00a40f402503d00740f401903d00540f400903d00140f400101d008807401e01d006807401601d002807400203600a80d802603600880d801e03600680d800a03600180d800200e00a403802100e007403801900e005403800d00e00140ec02903b00940ec02103b00640ec01503b00240ec00503b000409c022027007809c01a027005809c00e0270028030029
  | 13 => 0x11008804401e011006804400e011002804400602a00a80a802602a00880a801e02a00680a800e02a00180a800205700a415c021057006415c015057003415c00905700140bc02902f00940bc02102f00640bc01502f00340bc00502f000406c02201b007806c01a01b005806c00e01b000817001e05c006817001605c003817000a05c000812002a048008812001e048006812000e0480028120006020009408002102000740800190200034080009020000413402904d009413402104d005413400d04d002413400504d0004090025
  | 14 => 0xda002466802519a0064b580252d60008cf002233c0078cf001d33c0058cf001533c0038cf000d33c0028cf000905d01e417813205e04c41780b605e02d47e001a1f800089bc0260c600a431801e0c6006831800a0c600187cc01a1f300085b002916c00685b000616c000817c0061be00946f80162f800a4be00222f800340f80b21f500a87d40291f500887d401e1f500687d400a1f500187d400210b009442c02115400a4550025134009829000e0a40018840029210003817014605c051416c0411bd00a46f40221bd0068b14026
  | 15 => 0x20700a881c0262d80098b700262dc0078b7001a2dc0058b7000e2dc00084cc006133000817811a05e046493002905e04e81781393090094c2400e11100a457402215d008457401e15d007457401615d005457400e15d00345740091fc00947f00061fc000880402a201009880401a201005880400e20100188040021e000a47800221e0007878001a1e000187800020f600883d80210f600783d801d0f600683d80190f600583d80150f600383d800d05e03a83680220da008436801e0da007436801a0da006436800e0da003436800a
  | 16 => 0x104003441000a36b009815003205e02a83b802a0ee006879802903d03345dc0061f100947c40161f10018d2402915c008857002115c007857001d15c006457000e15c003457000a15c00246800061a000083500250d40004ae402911000a4440022110002844000205e016416c16111500a44540252e20034b8800a1e500a47dc02a1f700a47dc0221f700847dc01d1f700587dc0151f700287dc0091f700147dc00205e03885f802617e00885f801e17e00385f800a17e00081480fa05203e49b802a26e0098a5c0261fb00a47ec002
  | 17 => 0x25100949440061ea00947a8006046010814c0312f10088bc401a2f10034bc400a116000811807a22f009821800637e00981780dd348009834c0060d3000856c02215b008456c01e15b007456c01915b005456c00a15b0024644029191006864400d191002826802209a008426801e09a006826801609a002833c0220cf007833c01a0cf003833c00a0cf001819002505e04d47900291e4008879000d1e4001457802215e008457801a15e005857801515e003857800a20d00985f402517d00086480252c300a4b0c00e2c30008410022
  | 18 => 0x6900981a40061ab001412c04118600946180062c400a8b100262c40078b100162c40038b100062c4000846c0251c100787040061c100088d002905103d47c00221f000847c001d1f000647c00161f000547c000a1f0001458001e1600068580016160003858000a0f900941780c505102946940291ee00a47b80251ce00987380221ce006873800e1ce00287380022c20094b0800e370009817803905900c4a7002608c00648f402516400a459000234e00a8d38026161007858401d1610064584015161003458400a1610024344026
  | 19 => 0x19b008866c01a19b00285c000e2ec009850c022143007850c01a143003850c00a14300182cc0260dc00940f804e18800a4484022121007848401a121005848400e1210018d4c01a0ab0094e040293810088e0400d03c00c83580250d6000493c02906f0018cc40263310018cc400205104481700fa2a100a4a840222a100348e80260b400a82d00260b400682d00160b400282d00060b4000816c12d3760018dd80021cd009480c029203008880c01a20300344f40290510308a0c0262830088a0c01e2830058a0c00e2830008848025
  | 20 => 0xe5007883802920e003483800a2fb00a4bec00e17100947f802a0e100983840021fa009464c01e193006864c00606c00a41b000d05b04a425800203e00b89a00291d800987700221dc006877000a35800a414c0cd09d00a427400e05e045431402929800a4a6000a05b0594c500262840098a10006284000825c0251b0001838002512000946d00251b40018524022149006852400e149002852400614900081780790b900882e401e0b900682e40160b9002863802a18e009863801a18e003863800a18e00186380022ca0094b28016
  | 21 => 0x13100985e402524a00a892802624a008892801a24a003892800624a000816414515300181fc01e05e02c83980250e6006428802a0a2008828801e0a2003828800a0a20018b5000605b01e491002626d00989b400626d000847402911d008847401a0800064c8002932000081780613190078c6401a31900184240251090014888022222006888800d0ca00a416c0dd33800a840c022103007840c016103005440c00e10300281480cd09c008827001e09c005827000e09c00286d40261b500886d401e1b500686d40161b50008394026
  | 22 => 0x1a300987b000632700940d40312e900a4ba400d36600942c402a3010094cdc0223370028cdc0063370008e1402538500182b40290e7008839c01a0e700280f806e041033482c02a20b009882c02220b003882c00a20b001882c002062006406c04205e04345640250c900a416c14d19e00643480250d200743480012b700a8adc02605d03347a00221e800847a001e1e800687a00161e800547a000e292001833801e0ce00683380160ce003833800a08300a420c02505e03c83b002a0ec00883b001e0ec00683b00160ec00180ec0cd
  | 23 => 0x12c0034cbc02629f00a8a7c02629f0058a7c00e29f0028a7c00629f00081780a21cb009872c0221cb006872c0161cb003872c0020510348c000293000068c0000d30000287b400605e0144ccc0293330068ccc00a049010446402608900542c802a0b200982c801e0b200582c800a0b200182c800206700986000261800088600016180003860000a18000084e002913c00a8144079255007895401a255005895400e25500282b00260ac00782b001a0ac00582b000a0ac0008db800636e0008c9802511a001846800204b0334828025
  | 24 => 0x265005899400e2650028994002101009840401e101005840400e10100284040020bd00882f401e0bd00682f400a0bd001841802905e0448bbc02605e030856802115a007856801d15a006456801515a00344900252cd00183740260dd008837401e0dd00683740160dd00085a402616900185a40020d900943640190d9000451c0250b700a42dc00a2a50088a9401e2a50068a9400e2a500282e00250fc009425402537a005832c0290cb0034d5c0263570078378025163000850801623800948e000623800081440ed2ea00941b4026
  | 25 => 0x820018d100223440068d100163440038d1000202d00c49c002920900a882402620900188240022f9009493801e24e006893801624e003893800a05d0514d9c0250ea00883a801e0ea00683a80160ea00383340290cd00540e40cd2c900a4b2400d19c00188100251e100a89a800623700987f402a1fd00987f40221fd00687f400e1fd00187f40022d200181640791db0094bd002510700088800251b900a86e40261b900886e401e1b900586e40061b900080f80aa0c800a8c5c02516e00941080fa287001462c02505301e499401e
  | 26 => 0x213003884c00a2130018dc4026184008861001e184005861000e1840028a74025236000823402208d007823401a08d005823400a08d00187bc00627b00987ac00632d001845c02a1c9008872401a1c9005872400e1c9002857c02115f006457c01515f003457c00906500a8194026065006853402214d007853401a14d003853400a20f009470c00a1f900a47e400a088001868402534a001835402605e02f42a802a0aa00782a801a0aa00582a800a0aa0018cf80250660074db0006156001814c0f905e05480cc079082007820801a
  | 27 => 0x2d00068b4000e2d00028b400063150098c540061050018a1402a285009887802507e00941f80011d3008826001e0980068260016098002826000205104b48600222180068860016218003886000a28600981440dd09200082ec0220bb00782ec01a0bb00582ec0063540008c580223160068c5800a0db007836c01a2ed00086d802918900a8624026189007862401a18900386240061890008a8802523b00888ec01a23b00388ec00a23b0018ddc02a3100018a00026280007824c0251ac0018470026235009484c02a213008884c01a
  | 28 => 0x17c00088b801d06300a818c026063007818c01a063005818c0060630008c9402910f00942a00220a800782a00160a800382a000a2da0068b6800a23c00a48f000d19f0098a4c0292b80098ae000605b0354bf402525f008897c00a13200744c800524b00987d00290590334acc00610a00a8b5402604c03e80dc0cd31a00684b40062460018e080252cf001812c0fd0e200940f80962ad000830001a0c000180f80861d9001876400217200885c801e17200685c800e17200181180fa26200081d40060750008b1802503e02e8b40022
  | 29 => 0x9000081780ba3520088d4801e3520068d4800e352002859402a165009859402216500685940161650018594002187009861c01e187006861c00e187002861c002233009897002534c0098b94025068001424402505e04289e000634d0018d340021140018dbc02a36f0098dbc01a1820078608016182003860800a18200083c802a0f200883c801a0f200583c800e0f200189c801e0ae00a82b80260ae00782b801a0ae00582b80060ae000871c02a1c7007871c0161c7003871c00a1c700185f002617c00885f001e17c00585f000a
  | 30 => 0x16f00885bc01e16f00685bc01616f00386600251980024c600223180078c6001a3180058c6000e28800983900250e400241e40260790018aac0222ab0078aac01a2ab0038aac00221b001886c00204403e8c4802a3120098c480223120068c480163120018c48002125009849401a1d700a875c0261d700681cc02a07300981cc01a18c00a863002618c007863000e18c002863000618c0008c4c02a3130018c4c00202d01e485800605b02943f400a06e00941b801906e0034cc002a3300018cc0002090008824001e0900068240016
  | 31 => 0x17a00385e800204e03e892002a2480018920002084007821001a084003821000a0840018ad802a2b60018ad800210d009429801e0a6005829800e0a6002829800605b03941780da1e200a478801d0b600782d801a0b600582d800a0b6001854801d26b00989ac01e249009828001e0a00018d8802517500885d401a17500585d400e175001843802a10e009843801e10e005843800a10e001843800226c00987c80221f200787c801a1f200587c800a1080098ce802903e03087fc02a1ff00987fc0221ff00587fc00e1ff00187fc002
  | _ => 0
def recipeData1_ : Nat → Nat
  | 0 => 0xfa005815c12d094008825001e094005825000a0940008d3c02634f00189640020b000a82c00260b000782c001a0b000282c00060b00008a0800611e00a469c0251a7006450002927c000861402a185007861401a185003861400a18500186a00221a800786a00161a800386a000a118009446001d051041468802a1a2009868801a1a2003868800a1a2001868800229900944d402a13500984d401e13500384d400a13500184d400215700181500fa11300948b00023450008ad40262de009418401e17a00985e802217a00785e8016
  | 1 => 0x60e0008d5c17a33c044a1600290ce03c8e2802909e00186dc02a1b700986dc0221b700786dc01a1b700186dc00222500181f00292ae00941440d531c00184a002212800684a001612800384a000203e03489040251da00a87680261da007876801a1da00287680061da00081d802514b007852c01a14b003852c00a14b00089900190c700a4df402516d00a426402505b03b4cc8006077009859c02a167009859c022167006859c00a167001859c002190007864001a190003864000a190001816c1051d5007875401a1d50018978025
  | 2 => 0x3ab0088eac01a3ab0058eac00a3ca0088f2801e3ca0068f2800a3ca0019a000250da0258ef40223bd0078ef40163bd002982001a0ce02a8f740061e8010596002558800a52bc0291f001b9cc802942600947dc06e4d2006934800247a00a4ba412d53900794e401a53900194e400253400a43680aa66600a4a0c0fa0ce02887900791f700b906800552700a5180025460001836808670a0069c2800243e00890f801e43e00690f801643e002832017a4cb009532c0022d803e9ebc02512c0104e2402915c05753f0029104010583801a
  | 3 => 0x46b00691ac00254500a47a013a19405e863817a76800a526802918905e99ac0027bc00a5e640251f00219e8c02581a00a4f880223e20078f8801a3e200593c002934405e9f6002946c00a4e2c0290da01b93980291f701982e01453d70058cf011a29f05e8e3402975a00954a40293ea00952d40295ed00a4eb80023e900943380ba24a05e87dc04626505e92c40291f004b5c00029382051617c01a6390094b880413d5006907802a41e007907801641e002907800641e0009060022418007906001641800290600024c800a5140029
  | 4 => 0x20705e86f412d08e04b53840296e00094e940251da05e9720029675006859c17a49b009516802945a00341b012d67f00a61b80250b005e970c01a5c30009fa002977200a589c02930004b4e5802557000a44d417a6c500a420c1795ab0094e080cd70f0069c3c00248b003503402538101052c00224b000792c001a4b000292c000631205e957c02255f0069e5800278000a42c817a16505e8f640223d90068f640163d900396f00297690094dbc17a40c00a4e0816d88000a4fe401e3f90058fe400e3f9002905c02943d0094a0c13a
  | 5 => 0x3fc0038ff000a44f00081cc17a3a20008ed00297ae00a514c022453006914c00e453002992c01a64b00093f40295eb00946480cd46800791a001a46800591a000a3b20078ec801a3b20058ec800a82200a5bc0029859009550402578100948f416d0ce04491a80297a6009531800e2040514fb001a60600947f417a2ca03353500295f600a529002548c007923001a48c005923000a81b009433813a1d705e96180252c904b5ec001a7b0000903802240e007903801640e0028a8412d7a500a5cd00290da04e9acc02558500a587c029
  | 6 => 0x2c405e82d017a33c02e96cc0253e800a5588002300010534002974500a419417a70100953bc01a20304b52d0006726009581c029433007464814533c02a901c0295a200958c002263000798c001a6300058cf00a27a200a601800250900957040257de00a56840297fd00954440251f702a818c17a33c03c9790029492009480417a4b30019b340294080095f3c0254ae00892b801e4ae00692b80164ae002883c16d51000a481016d4c2009468817a78f0095f7c025480006937c0294e900a534c02940b00a47fc17a3fc0078ff001a
  | 7 => 0x5f5006a16802949700a42e00cd4e0009556000a3b300a47a011a48600183680a20b704b524402984100a4c980cd39400a47a0112823009603c0295f400a43680f26a800948f40cd3a300a49280fa7d200a4f1401a3c5002981402983d00a46f816d0ae05e8be012d1be0515ca80291b705e909001a23d0515a9c02939f0088e7c01e39f0068e7c00a8050095ee40291b905e89940fa746009463017a15c0104c9816d7350069cd40021e803c938c0294e20008f4c0223d30078f4c01a3d3005882c17a10e05ea1b40294b20019498029
  | 8 => 0xa1d000413413401e01e0090090019019014414401d01d003803803b03b004c04c04004000b00b005905900c40c400c00c2868029a1a009a868025a1a008a868021a1a007a86801da1a006a868019a1a005a868015a1a003a86800da1a002a868009a1a000a868001025025017417402a02a005805804e04e006806800a00a0024024008008001c01c00600600140140030030008008001001000000089f00093140cd8e9005a28c00289100962d80168dc008a37001e8dc006a37000a8dc001931416d20f03343680ba1f705d5c10029
  | 9 => 0xa1b003a86c00da1b001a86c005a1b000a86c00104b04b016c16c023023003c03ca2000aa880029a20009a880025a20007a88001da20006a880019a20005a880015a20003a88000da20002a880009a20001a880005a20000a88000105005000f00f00270270050050041041006006000d00d011411403a03a017817801101100f80f805705700bc0bc01b01b017017004804800cc0cc020020287402aa1d00a6874026a1d0096874022a1d008687401ea1d007687401aa1d006687400ea1d003687400aa1d0026874006a1d0016874002
  | 10 => 0x5505500b40b405a05a01181180210210098098012012012812805305300fc0fc01701701101100430430040040a1e00aa878029a1e009a878025a1e008a878021a1e007a87801da1e005a878015a1e003a87800da1e002a878009a1e001a878005a1e000a87800103403400a40a40390392888022a22008688801ea22007688801aa220066888016a22005688800ea22003688800aa220026888006a22000a88800105205200c80c8a1b00aa86c029a1b009a86c025a1b008a86c021a1b007a86c01da1b006a86c019a1b005a86c015
  | 11 => 0xa1f000413c13c05405400ac0ac05805800c00c001c01c2864029a190096864022a19008686401ea19007686401aa190066864016a19005686400ea19003686400aa190026864006a190014124124035035005405404204200b80b8a1c00aa870029a1c009a870025a1c008a870021a1c007a87001da1c006a870019a1c005a870015a1c002a870009a1c001a870005a1c000a870001a2100aa884022a21008688401ea21007688401aa210066884016a21005688400ea21003688400aa210026884006a21001688400203703700a00a0
  | 12 => 0xaf900aabe4025af90014cf8cf8abd00a6af4025abd0086af4019abd0036af4009abd0016af4001a98003aa60006a2d009a8b401aa2d0008cf0cf0a3e009a8f8001b1b00a6c6c005b1b00069c8025a7200769c8005a3600a68d8026abb0016c4c005a83007aa0c006a1b05ea86c179aac0096afc02aabf001aafc002047047007c07c00b00b013013003803800f40f405605600d80d8022022287c02aa1f00a687c026a1f009687c022a1f008687c01aa1f006687c016a1f005687c00ea1f003687c00aa1f002687c006a1f001687c002
  | 13 => 0xa910036a44002af50096bd401daf5001687017aa1c05e4c24c24a8900aaa68026a9a001aa68002a63008a98c021a63007a98c01da63006a98c019a63005a98c015a63003a98c00da63002a98c0091611612c48026a33009ab9c02610310328800f9a38006a8e000da38002ab7c026a1e05ea87817933f33f2a2c026af0009abc0006af0000aad0025aea00a6ba8022aea006aba800aaea0016890029a24009689001da24005689000da240026890005a240006bc800eac500a6b14025ac50076b14019ac50036b14009ac50016b14001
  | 14 => 0xaec0096bb0019aec000687417aa1d05e6904025a39005ab8801dae20016b880010ce0ce2b28026a8e0096bcc02515e15e28640cda1b051696c02aa5b001a96c002add009ab74002a97001aa6400eae40016b90001aa80094534534a2005ea880179a7500aabb4029aed0096bb4021aed0066bb4015aed0036bb4005aed0006a18025afe00aa954029af600aabd8025af6001ab6c006a660096998005a2a00a6a3c026a8f007aa3c006b0700969dc026a3b00947dc7dcb180096c4002aa8000a6be002ab2100a47a07a0a91008aa4401a
  | 15 => 0xa71006ab5802aad6001ab58002a1901e6918026a2203eaaf8025abe0016a08006a82000a870031b00008ac0001ab00002aad8025a4f00a693c025ac70096b1c006a43001a90c002a6000aa980006a60000ab60006ad8000ab40006ad0000a900026a6900aa9a4025ae100aab84026a1a03ea944029a7a0096924029a1905b456c56ca5a00a6968026acb003ab48006ad2000abec025afb00169ac029a6b00969ac01da6b00669ac015a6b00269ac005a6b00068bc026a2f006a89c026a27006a89c006a27000ac30026a1b05b69d0025
  | 16 => 0xa6e00a69b8025a3200a4570570b0f00969fc025a7f00769fc019a7f0016c80029b200096c80021b200076c80019b200056c8000db20002687816da54009aa20025a4c009ab10029ac40096b10021ac40076b10015ac40036b10009ac400047c07c0a3400a6974025a3d0096a88006aa2000ac68026ade0066b78001a4e007a938006a4e000aacc006ab7008aadc00dab7002aadc002aef0096bbc005a5700a68b00290da0da2a90006aa4000a9a0006a68000ab3400ea200516960006a9c006aa70006a9c000a8d4026aad009a9c4026
  | 17 => 0xa7b002a988029a620096988021a620076988019a620036988009a620016898029a260096898019a9e006aa78006a9e000ac0c0250f60f629cc006a73000aabc006aaf000ac50026ae3009a9f0029af400aaae0029b1d009a8a0029a2800968a001db05007ab24029ac90096b24021ac90076b24019ac90056b24005ac90006bf4025afd00168c4026a960094574574b0e001ac38002a4200a6908001aa7009ac7c025b1700a4268268a87001aa1c002a4b009692c019ab0009698401da610066984005a900096a40019b060096c18005
  | 18 => 0xaba00069f8025a7e0006ac8025a76009457c57ca5e00a6978025a5e008697801da5e0066978015a5e0036978001ac3006abfc025aff0066bfc005ad4001ab50002acc000a8f0006a3c000ac64025b1900069e0025a4d00a6bb8029aee0096914026ae60016b98001a1a04b687c17aace001ab38002a9200a6bdc025af7001699c025b080018580580a700096ba0005ae80006a0402aa81001aa04002ab5009abc402aaf1001abc4002a8a00969a802915a15a2c2c025a1e0336b80005ae00006a10029a590096964019afa00aa9ec01a
  | 19 => 0xb4300a71d0025ba800a6afc17ab5c00a6dac01ab6b000b21c025c0900a7154021c550077154019c550057154009b8700a6b10179ada03371a0029cc20096898179cea00a7120025b4f00a6a50025a8c0096940026a9d0096864145aae00968b8029a2e0096a98026b1e0096c78005b1e00068fc025a3f0016920006ac0001ab00002a3000a68c001da200336ac402aa4a007a94c029aa0001aa80002a640016990001adc0016970029a440096910021a440076910019a44005691000da440026aa4006a6d006a9b4006ae5009aae8025
  | 20 => 0x3028029ce900a6ba812dc3600a6dbc029a99a386b8417abeb00a71b8029c9800a6b6017ac7300a6d6c029c3400a6fa0025cef00a6e4c029b2d0036f9c029bcb00a6e2001ab6300a6b6ab2db800096c80179a6b05e7374025bbd00a714c025c2b0016b740fac5800a6e3c025c7200a6ea8025a4f05e6e5c029a2805e6d74029a2405e6e74022b9d006ae7400acca00a6d9c029b69006adb4029
  | _ => 0
def recipeData (i : Nat) : Nat :=
  match i/32 with
  | 0 => recipeData0_ (i % 32)
  | 1 => recipeData1_ (i % 32)
  | _ => 0
def recipe (i : Nat) : Nat := (recipeData (i/64) >>> (26*(i % 64))) &&& 67108863
def value : Nat → Nat → Sig
  | 0,i => raw.getD i zero
  | fuel+1,i => if i < 9 then raw.getD i zero else
    let q := recipe (i-9)
    let a := value fuel ((q >>> 2) &&& 4095)
    if q &&& 3 = 0 then neg a else
      bin (decide (q &&& 3 = 2)) a (value fuel (q >>> 14))
def retained (mask : Nat) : List Sig → List Wire
  | [] => []
  | a::w => let rest := retained (mask >>> 1) w; if mask &&& 1 = 0 then rest else (a,.tNone) :: rest
def extra : Nat → Nat → List Wire
  | 0,_ => []
  | n+1,z => (value 6 (z &&& 4095),.tNone) :: extra n (z >>> 12)
def ns0_Data : Nat → Nat
  | 0 => 0x7fef7ff5bff9dffc6ffe6fff17ff8a
  | _ => 0
def ns0_ (i : Nat) : Nat := (ns0_Data (i/64) >>> (17*(i % 64))) &&& 131071
def ns1_Data0_ : Nat → Nat
  | 0 => 0x8b13fc4c581fe262b0ff131567f898a63fc4c529fe26290ff131447f8989e3fc4c4d9fe2624cff1311e7f8988d3fc4c461fe2622cff1310e7f898863fc4c429fe26210ff131067f897873fc4b9b1fe25c7cff12d407f8966c3fc4b349fe258e0ff12c407f896193fc4b0a9fe257fcff12bee7f895cd3fc4ae51fe25710ff12b207f895473fc4a9d1fe254a8ff12a147f894f13fc4a721fe25364ff129aa7f894953fc4a369fe2516cff1289a7f894443fc4a1f1fe24ff4ff127f47f893a63fc49d21fe24e30ff126787f891e83fc486d1fe24338ff120bc7f89a15bf0450b9fc22834fe111b87f08
  | 1 => 0x9333fc4c991fe264c4ff132607f8992f3fc4c971fe264b4ff132567f899273fc4c901fe26470ff132367f8991a3fc4c8a9fe26450ff132267f899123fc4c889fe26440ff132167f8990a3fc4c831fe26414ff132087f899033fc4c811fe26404ff132007f898fe3fc4c7e9fe263ecff131f47f898f53fc4c7a1fe263ccff131e47f898f13fc4c781fe263bcff131da7f898eb3fc4c751fe263a4ff131d07f898e73fc4c729fe26390ff131c47f898e13fc4c701fe26378ff131b87f898db3fc4c6d1fe26360ff131947f898c93fc4c5f9fe262f8ff131707f898b63fc4c5a9fe262d0ff131667f89
  | 2 => 0x9a13fc4ccf9fe26678ff1333a7f899973fc4ccb1fe26654ff133287f899933fc4cc91fe26644ff1331e7f8998e3fc4cc69fe26630ff133167f899853fc4cc11fe265ecff132f47f899793fc4cb81fe265bcff132dc7f8996d3fc4cb61fe265acff132d47f899693fc4cb41fe26598ff132c87f899633fc4cb11fe26584ff132c07f8995f3fc4cad1fe26564ff132b07f899573fc4cab1fe2653cff1329c7f8994d3fc4ca61fe2652cff132947f899493fc4ca41fe2651cff1328a7f899443fc4ca19fe26508ff132827f8993f3fc4c9e9fe264ecff132747f899393fc4c9c1fe264d4ff132687f89
  | 3 => 0x9fe3fc4cfe9fe267f0ff133f67f899fa3fc4cfc9fe267e0ff133ee7f899f63fc4cfa9fe267d0ff133e67f899f23fc4cf81fe267b4ff133d87f899eb3fc4cf51fe267a4ff133d07f899e73fc4cf31fe26790ff133c67f899de3fc4cee9fe26770ff133b47f899d93fc4ceb9fe26750ff133a67f899cd3fc4ce61fe2672cff133927f899c83fc4ce39fe26718ff1338a7f899c43fc4ce09fe26700ff1337e7f899be3fc4cde1fe266e8ff133727f899b73fc4cdb1fe266d4ff133687f899af3fc4cd71fe266b0ff133567f899aa3fc4cd49fe266a0ff1334e7f899a53fc4cd21fe2668cff133447f89
  | 4 => 0x8989fc4a34cfe274dcff13a6c7f89d353fc4e9a1fe274ccff13a627f89d303fc4e979fe274b8ff13a5a7f89d2c3fc4e959fe274a8ff13a527f89d283fc4e939fe27494ff13a487f89d223fc4e901fe2747cff13a3c7f89d1d3fc4e8e1fe27460ff13a2e7f89d163fc4e8a9fe27450ff13a267f89d123fc4e889fe27440ff13a187f89d0b3fc4e849fe27420ff13a0c7f89d053fc4e821fe27404ff13a007f89cfa3fc4e7c9fe273e0ff139ee7f89cf63fc4e7a9fe273d0ff139e67f89cf23fc4daf1fe26830ff134167f89a093fc4d039fe26818ff1340a7f89a043fc4d011fe26804ff133fe7f89
  | 5 => 0x8a1bf44a1e3fa27436fb133dd7d89971bec4caddf626306fb131757d89894bec4a325f62749af7132797b89928bdc4a9cdee26255ef13a476f89d0eb7c4e855be2740edf134156f89a08b7c4cf7dbe26796df133b76f899d6b7c4cdedbe266c6df1334d6f89990b7c4cbedbe265cedf132cb6f8995db7c4caadbe26502df1326f6f8992ab7c4c8f5be26422df131ef6f898eeb7c4c6fdbe26366df131856f898b9b7c4c57dbe262badf131536f898a0b7c4c4d5be2625adf131216f89889b7c4a335be24f7edf127616f891f7b7c4cf8d7e2743e7f133673f8991f9fc4c7ccfe263127f1317b3f89
  | 6 => 0x23d7fc5114bfe2883dff14408ff8a1f17fc50f43fe286f9ff14324ff8a15c7fc50a13fe28369ff1419cff8a0b87fc502f3fe2812dff151b87f199c3ff04c8eff826247fc12995fe09460fd84c6e1fc2746efe13a0f7f09d02bf84ceadfc2674afe133857f099adbf84cc35fc26612fe132f97f09954bf84c9f5fc264dafe132597f09929bf84c935fc2641efe131ff7f098fcbf84c735fc26372fe131af7f098b2bf84c56dfc2629efe1313b7f09899bf84c475fc2622afe131117f093ddbf849c6dfc247c2fe133b0ff099467f84c6e3fc25315fe132cffa894cbfd44c84fba27466fd131477e89
  | 7 => 0x5dd7fc52ee3fe29735ff14b94ff8a5c47fc52e0bfe296cdff14b50ff8a5a27fc52cdbfe29655ff14b24ff8a5907fc52c7bfe29619ff14af2ff8a55c7fc52a3bfe29505ff14a74ff8a52a7fc5288bfe29429ff14a12ff8a4f17fc52723fe29381ff149b2ff8a4d57fc5268bfe29315ff14984ff8a4a47fc524abfe29249ff148daff8a45b7fc5226bfe29111ff14886ff8a4417fc521f3fe290f5ff14878ff8a4267fc5206bfe29021ff147faff8a3fa7fc51fb3fe28fa5ff14780ff8a3a67fc51d2bfe28e91ff14740ff8a3967fc51c63fe28e09ff146f4ff8a35f7fc519e3fe28c99ff14594ff8a
  | 8 => 0x8607fc542f3fe2a165ff1508eff8a83e7fc541b3fe2a0cdff15062ff8a8237fc540dbfe2a015ff14ffaff8a7f37fc53f93fe29f7dff14fa2ff8a7cf7fc53d7bfe29e99ff14f46ff8a7a07fc53ccbfe29e3dff14f0eff8a7817fc53b73fe29da5ff14ec2ff8a75a7fc53a9bfe29d19ff14e7eff8a7367fc53933fe29c7dff14e3aff8a7017fc537b3fe29b81ff14da6ff8a6cb7fc5359bfe29aa1ff14d40ff8a6977fc53403fe299bdff14cd8ff8a6697fc53343fe29995ff14cb0ff8a6507fc531cbfe298e1ff14c40ff8a6197fc530b3fe29855ff14c1eff8a6067fc52ffbfe297ddff14bd6ff8a
  | 9 => 0xcc27fc56573fe2b2b5ff15950ff8aca47fc564dbfe2b25dff15926ff8ac8d7fc56453fe2b21dff158feff8ac717fc56383fe2b1bdff158daff8ac697fc562d3fe2b159ff15890ff8ac467fc561fbfe2b0cdff15854ff8ac187fc560bbfe2b03dff1580eff8abf87fc55f93fe2afa9ff157d0ff8abe57fc55f1bfe2af81ff157b2ff8abc47fc55e13fe2aeddff15754ff8aba97fc55d03fe2ae7dff1573cff8ab987fc55c7bfe2ae39ff1571aff8ab8c7fc55c03fe2ad79ff156b2ff8ab507fc55a43fe2ad11ff15668ff8ab2e7fc5592bfe2ab69ff154b0ff8aa397fc5440bfe2a1e5ff150dcff8a
  | 10 => 0x398bfc51cadfe28e52ff1471f7f8a38dbfc51c65fe28e2eff147157f8a389bfc51c0dfe28cf2ff1466f7f8a333bfc518b5fe28c02ff145f17f8a2f1bfc5174dfe28b8aff145b57f8a2c9bfc5150dfe28a62ff144bf7f8a23cbfc51115fe2883aff144077f8a1f9bfc50fbdfe287d2ff143e17f8a1e8bfc50f25fe28782ff143b97f8a1bdbfc50cddfe28646ff142c37f8a15dbfc50ad5fe284b2ff1423b7f8a110bfc50825fe2839eff141b57f8a0cebfc5065dfe2831aff1416f7f8a09abfc50365fe2817aff140b77f8a051bfc501f5fe280ceff159d6ff8ace07fc566ebfe2b36dff159aaff8a
  | 11 => 0x45dbfc522ddfe2916aff148b37f8a450bfc5227dfe29136ff148937f8a448bfc5223dfe2911aff148897f8a440bfc521f5fe290beff148597f8a42bbfc52155fe290a6ff1484b7f8a424bfc5211dfe29082ff1483f7f8a41abfc520bdfe2905aff1482b7f8a40fbfc52065fe2902eff1480f7f8a406bfc5202dfe28ff6ff147f57f8a3f5bfc51f75fe28fb2ff147d17f8a3e2bfc51f0dfe28f7eff147bb7f8a3d1bfc51e6dfe28f2aff147937f8a3c7bfc51e2dfe28f0eff1477b7f8a3bcbfc51dcdfe28edeff147677f8a3b2bfc51d85fe28ebeff1474d7f8a3a4bfc51d1dfe28e8aff147437f8a
  | 12 => 0x520bfc528bdfe29442ff14a157f8a508bfc5283dfe2941aff14a097f8a4fdbfc527e5fe293eeff149e37f8a4f0bfc5277dfe293b6ff149d37f8a4e6bfc5272dfe29392ff149c77f8a4e2bfc5270dfe2937eff149b37f8a4d6bfc526adfe29352ff149a77f8a4d2bfc52685fe2933eff149937f8a4c8bfc5260dfe292eeff1496d7f8a4b5bfc5257dfe2929aff149477f8a4a2bfc524d5fe2925eff1492b7f8a491bfc52465fe2922eff149137f8a488bfc52415fe29206ff149017f8a47fbfc523e5fe291eaff148f37f8a478bfc5236dfe291b2ff148d77f8a46abfc5234dfe2919aff148c97f8a
  | 13 => 0x5c9bfc52e45fe29712ff14b877f8a5c0bfc52dfdfe296faff14b797f8a5bbbfc52dc5fe296deff14b6d7f8a5b5bfc52da5fe296caff14b4f7f8a5a5bfc52d0dfe29682ff14b3f7f8a59cbfc52cb5fe2964eff14b237f8a590bfc52c4dfe29622ff14b0b7f8a57fbfc52be5fe295eeff14ae57f8a571bfc52b85fe295b6ff14ad97f8a56bbfc52b1dfe29586ff14ac17f8a55fbfc52aedfe2953eff14a937f8a547bfc52a35fe29516ff14a857f8a540bfc529d5fe294e6ff14a6d7f8a534bfc5299dfe294caff14a637f8a52fbfc52955fe294a6ff14a517f8a527bfc52935fe2948eff14a437f8a
  | 14 => 0x68bbfc533fdfe299f2ff14ced7f8a675bfc5336dfe299b2ff14cd77f8a669bfc53335fe29992ff14cb97f8a65bbfc532cdfe2995eff14ca37f8a64fbfc53275fe29936ff14c977f8a644bfc531c5fe298deff14c6d7f8a630bfc5317dfe298b6ff14c4f7f8a624bfc5310dfe29882ff14c3f7f8a619bfc530c5fe2985eff14c2b7f8a614bfc5309dfe29846ff14c1d7f8a60bbfc53055fe29826ff14c117f8a607bfc5302dfe297feff14bfd7f8a5f8bfc52fbdfe297daff14beb7f8a5f4bfc52f8dfe297c2ff14bdf7f8a5edbfc52f55fe29792ff14bc77f8a5dbbfc52eadfe29736ff14b957f8a
  | 15 => 0x787bfc53c05fe29deaff14ee97f8a773bfc53b95fe29dc6ff14edf7f8a76ebfc53b45fe29d66ff14e9b7f8a745bfc539f5fe29ce2ff14e6f7f8a736bfc539adfe29cd2ff14e657f8a730bfc5397dfe29cbaff14e5b7f8a72abfc5394dfe29ca2ff14e4b7f8a724bfc5391dfe29c7eff14e397f8a71bbfc538bdfe29c3eff14e177f8a70abfc53825fe29c02ff14dff7f8a6febfc537b5fe29bc2ff14ddf7f8a6e7bfc53735fe29b96ff14dbf7f8a6d9bfc5368dfe29b3eff14d9b7f8a6c5bfc535fdfe29adaff14d4f7f8a6a0bfc534f5fe29a76ff14d377f8a699bfc5348dfe29a36ff14d197f8a
  | 16 => 0xb47bfc55a1dfe2aceaff1566d7f8ab31bfc5596dfe2ac9eff1564d7f8ab00bfc55755fe2aadeff155237f8aa7bbfc551c5fe2a202ff150f17f8a877bfc54385fe2a1beff150db7f8a867bfc542fdfe2a176ff150b97f8a85abfc542c5fe2a136ff150937f8a841bfc541edfe2a0d6ff1504d7f8a824bfc54115fe2a072ff150357f8a813bfc54095fe2a03eff1501d7f8a80cbfc54035fe29feaff14fe97f8a7eabfc53f45fe29f96ff14fbd7f8a7d8bfc53e95fe29f42ff14f9d7f8a7c3bfc53de5fe29eeeff14f737f8a7b0bfc53d75fe29ea2ff14f4b7f8a7a2bfc53cfdfe29e52ff14f257f8a
  | 17 => 0xc01bfc55fe5fe2afeeff157f57f8abf9bfc55fbdfe2afdaff157d77f8abe9bfc55f3dfe2af9aff157c97f8abe2bfc55efdfe2af6eff157b17f8abd1bfc55e7dfe2af2eff157957f8abc9bfc55e45fe2af0eff1577b7f8abbcbfc55dddfe2aee6ff157717f8abb4bfc55d75fe2aeaeff157517f8aba1bfc55cedfe2ae6aff1572f7f8ab94bfc55c9dfe2ae4aff157157f8ab89bfc55c45fe2ae1eff1570d7f8ab83bfc55bfdfe2adbeff156dd7f8ab6dbfc55b5dfe2adaaff156d37f8ab68bfc55b3dfe2ad96ff156c77f8ab62bfc55afdfe2ad7aff156bb7f8ab5cbfc55addfe2ad62ff1569f7f8a
  | 18 => 0xce5bfc566f5fe2b352ff159957f8acc9bfc5663dfe2b316ff159897f8acc1bfc565cdfe2b2c6ff1595f7f8acacbfc5655dfe2b28eff159437f8ac9ebfc564c5fe2b252ff159237f8ac90bfc56465fe2b226ff159117f8ac86bfc563f5fe2b1e6ff158e77f8ac72bfc56375fe2b1b2ff158d17f8ac61bfc562fdfe2b17aff158b17f8ac57bfc56295fe2b142ff158997f8ac4abfc5623dfe2b112ff158877f8ac3ebfc561bdfe2b0daff1586b7f8ac34bfc56195fe2b0a6ff158517f8ac25bfc560f5fe2b076ff158397f8ac1bbfc560d5fe2b042ff158177f8ac0abfc5604dfe2b00eff158057f8a
  | 19 => 0x4a1dfc5234efe2918f7f14829bf8a39edfc51cbefe28e237f146d7bf8a342dfc5154efe288eb7f14405bf8a1bcdfc50c1efe2ad78ff14f0e7f8a7363fc538f9fe29a80ff14cd87f8a6693fc531c1fe29880ff14c327f8a6153fc52ff9fe297dcff14b9a7f8a5ca3fc52e21fe29640ff14a8e7f8a53a3fc52951fe29428ff149e27f8a4e43fc526c9fe29354ff1492a7f8a46d3fc522d9fe29134ff148887f8a43e3fc51fe9fe28fe8ff1474c7f8a3a43fc51c61fe28cf0ff143d07f8a0da3fc50671fe28178ff159e37f8acf0bfc5677dfe2b3baff159db7f8acecbfc56755fe2b3a6ff159d17f8a
  | 20 => 0x1f8efc50ddf7e2863fbf14303df8a0c1efc505af7e291a67f159a7bf8acc0dfc5642efe2b19f7f1587bbf8ac31dfc55d3efe2ad0b7f150ffbf8a875dfc542befe2a11b7f15057bf8a80bdfc53f26fe29f5f7f14f9bbf8a7c8dfc53e0efe29edf7f14f5bbf8a78cdfc53c36fe29dff7f14ec1bf8a74cdfc539eefe29c537f14e13bf8a6fcdfc537aefe29bb77f14db1bf8a6cadfc53626fe29af77f14d65bf8a687dfc533a6fe2998f7f14cadbf8a63edfc53166fe2987b7f14bfbbf8a5e2dfc52d8efe2963b7f14b09bf8a578dfc52aa6fe2953b7f14a3bbf8a516dfc5281efe293e77f1499dbf8a
  | 21 => 0x78befc53c2f7e29de7bf14ecddf8a75befc53ac77e29d4bbf14e97df8a747efc53a277e29cf3bf14e59df8a713efc537df7e29bb3bf14dc9df8a6deefc536877e29b0fbf14d79df8a696efc534877e29a2bbf14cf7df8a673efc532af7e29927bf14c87df8a63defc5315f7e29877bf14c25df8a5e9efc52ed77e29753bf14b49df8a58defc52bef7e295dfbf14acddf8a553efc52a6f7e29523bf14a7bdf8a515efc528177e293e3bf1499bdf8a4c0efc525d77e2919fbf148c5df8a413efc520277e28f83bf14763df8a39defc51c3f7e28dabbf14683df8a2e1efc516477e28aa3bf14495df8a
  | 22 => 0x3b0f7c51d57be28e73df1470def8a37ef7c51b4fbe28d03df145b1ef8a2a7f7c5132fbe288e7df14401ef8a1f7f7c50dd7be28637df1417fef8a0b3f7c566ff7e2b373bf159a5df8acbfefc564277e2b1afbf158d5df8ac66efc5627f7e2b10bbf15879df8ac30efc561177e2af5fbf15783df8ab96efc55c2f7e2ad5fbf1569ddf8ab30efc559577e2a1fbbf150d9df8a866efc542977e2a133bf1508bdf8a83cefc541877e2a0abbf1504bdf8a819efc5406f7e2a02bbf15005df8a7f9efc53f8f7e29fc3bf14fd7df8a7e9efc53f3f7e29f77bf14faddf8a7c7efc53e077e29edbbf14f3ddf8a
  | 23 => 0x7a7f7c53d27be29e87df14f23ef8a78af7c53c27be29dfbdf14ef1ef8a767f7c53affbe29d5fdf14e87ef8a722f7c538cfbe29c4bdf14e11ef8a6faf7c537a7be29bafdf14dc7ef8a6ddf7c536bfbe29b27df14d77ef8a6b1f7c53537be29a57df14d13ef8a686f7c533d7be299cbdf14cc5ef8a63cf7c53157be2988fdf14c39ef8a5fcf7c52ecfbe2974fdf14b59ef8a5a6f7c52c67be2960fdf14af5ef8a56af7c52b2fbe29533df14a79ef8a51cf7c528a7be2943fdf14a03ef8a4f7f7c5279fbe2937bdf14941ef8a496f7c52337be29187df14885ef8a403f7c51f3fbe28f7fdf1478def8a
  | 24 => 0x4ddfbc52667de292ffef148cbf78a402fbc51f37de28da3ef1467ff78a2c7fbc51537de287fbef14371f78a17ffbc5058fde2919adf147bf6f8a3b0b7c50fbdbe2b347df15999ef8acbef7c565d7be2b2e3df15917ef8ac83f7c563efbe2b1f3df158cbef8ac51f7c56277be2b12fdf15883ef8ac3bf7c56127be2b03bdf15811ef8abd6f7c55e87be2af3bdf1578fef8aba6f7c55a6fbe2ad07df15673ef8a87df7c543a7be2a1afdf150cbef8a861f7c542b7be2a147df15097ef8a83bf7c541a7be2a0bfdf15043ef8a801f7c53f7fbe29f8fdf14fabef8a7c6f7c53dffbe29ed7df14f59ef8a
  | 25 => 0x2c6fdc51527ee288e3f7143f9fb8a18bfdc50befee2b343ef1597bf78ac64fbc561d7de2b0bfef157abf78aba5fbc55ab7de2a1cfef15091f78a844fbc5414fde2a027ef14ff1f78a7eefbc53f17de29f73ef14fa9f78a7ccfbc53e2fde29efbef14f57f78a789fbc53befde29d97ef14ebdf78a756fbc53a8fde29d2bef14e85f78a73bfbc537cfde29bcfef14dd5f78a6c2fbc535d7de29ac3ef14d29f78a685fbc533cfde299c7ef14cddf78a654fbc53247de2990bef14c53f78a604fbc52fdfde297b3ef14bd1f78a5e1fbc52ec7de2974bef14b17f78a552fbc52a5fde2944fef149edf78a
  | 26 => 0xb4cfdc55a07ee2a1cbf7150c9fb8a850fdc54177ee2a0a3f715041fb8a818fdc54047ee2a003f714feffb8a7e1fdc53e5fee29f13f714f7bfb8a7b4fdc53cefee29e43f714f07fb8a777fdc53b27ee29d77f714ea1fb8a73afdc5388fee29c1ff714de5fb8a6dcfdc536b7ee29b23f714d83fb8a6affdc53427ee299e3f714ce1fb8a661fdc5323fee29907f714c37fb8a603fdc52fd7ee29783f714baffb8a5b0fdc52c17ee295dbf714aa3fb8a539fdc528dfee2943bf714a01fb8a4f5fdc5265fee292fbf71493ffb8a460fdc52097ee29007f7147cbfb8a393fdc51c2fee28d9ff71467dfb8a
  | 27 => 0x7fffec53fb7f629fb7fb14fb7fd8a7d3fec53e17f629eebfb14f39fd8a793fec53c17f629ddbfb14ec7fd8a74ffec53a4ff629ce7fb14e0dfd8a6f8fec5378ff629b57fb14d8ffd8a6c0fec535cff629abbfb14d3ffd8a693fec533bff62991bfb14c81fd8a63bfec530d7f62980bfb14bcffd8a5dffec52eb7f629747fb14b5ffd8a575fec52a87f62946bfb14a25fd8a50dfec527fff629373fb1493dfd8a464fec522fff629047fb14737fd8a384fec519eff628b17fb14547fd8a237fec50c57f6285effb1415ffd8a539bdc5667fee2b2f3f715905fb8ac39fdc56177ee2ae93f7156abfb8a
  | 28 => 0x44bff452257fa29117fd1487ffe8a43cff45218ffa2902bfd14813fe8a3ffff451fbffa28faffd147c9fe8a3deff451dd7fa28ebbfd14759fe8a3a9ff451d3ffa28e6bfd14725fe8a391ff451c87fa28e0ffd14641fe8a309ff4517dffa28b0ffd14527fe8a283ff45127ffa288dbfd14421fe8a1fbff450f9ffa286dbfd14311fe8a170ff450b27fa28373fd14175fe8a0adff4504effa2823ffd1403dfe8a00cff452325f62b33bfb15903fd8ac38fec5616ff62af53fb156a9fd8ab4bfec559fff62a1abfb150c7fd8a855fec5427ff62a10ffb15075fd8a82dfec5413ff62a07ffb1502ffd8a
  | 29 => 0x62eff453137fa29837fd14c03fe8a5f3ff452f37fa2973ffd14b99fe8a5c7ff452e2ffa296f7fd14b75fe8a5b9ff452d77fa29663fd14b15fe8a581ff452bf7fa295d3fd14ae7fe8a56fff452b4ffa295a3fd14ac9fe8a562ff452a27fa2950ffd14a77fe8a52eff45296ffa29497fd14a45fe8a51eff4528cffa29433fd14a0bfe8a4feff4527d7fa293d3fd149ddfe8a4ebff452757fa293a3fd149b7fe8a4d8ff45265ffa2932bfd1498ffe8a4c6ff45261ffa292f7fd14973fe8a498ff4524a7fa2924ffd1490ffe8a485ff45241ffa291f7fd148f7fe8a477ff4522f7fa29163fd14899fe8a
  | 30 => 0x7e6ff453f07fa29f6bfd14f95fe8a7b8ff453d97fa29eabfd14f37fe8a798ff453cb7fa29e57fd14f1dfe8a77cff453b87fa29db7fd14ed9fe8a76aff453ae7fa29d57fd14e9dfe8a741ff45399ffa29cc7fd14e57fe8a727ff45390ffa29c83fd14e3dfe8a718ff4538b7fa29c43fd14e1bfe8a705ff45381ffa29c0bfd14dd3fe8a6e1ff4536dffa29b53fd14da5fe8a6ceff453637fa29afbfd14d71fe8a6b7ff4535affa29ad3fd14d39fe8a69aff453497fa29a3ffd14d1dfe8a688ff453417fa299fbfd14cd5fe8a667ff453307fa2997bfd14cbbfe8a653ff453267fa2992bfd14c75fe8a
  | 31 => 0xc00ff455ffffa2aff7fd157ebfe8abf4ff455f8ffa2afbffd157dbfe8abddff455ed7fa2af4ffd1579bfe8abc0ff455db7fa2aecffd15765fe8abb1ff455d87fa2ae8ffd15739fe8ab9bff455ccffa2ae57fd15709fe8ab7eff455b0ffa2ad6bfd156a7fe8ab51ff455a57fa2ad1bfd1567dfe8ab3bff45599ffa2acbffd15659fe8ab2bff45594ffa2ac93fd155e5fe8aaddff45566ffa2aa67fd15105fe8a87cff4543d7fa2a1dbfd150d3fe8a85bff4542a7fa2a13bfd15095fe8a840ff4541cffa2a0dffd15059fe8a81eff4540b7fa2a053fd15009fe8a7feff453fe7fa29fd7fd14fd9fe8a
  | _ => 0
def ns1_Data1_ : Nat → Nat
  | 0 => 0x3ddff851e27fc28ea3fe14733ff0a38dff851b37fc28c9ffe1463fff0a2c2ff851497fc288d7fe143f5ff0a1f0ff850da7fc2861bfe142f3ff0a162ff85067ffc282affe1411dff0a010ff85265fea290f1fd159cffe8ace4ff45671ffa2b38bfd159b5fe8acd8ff4566b7fa2b337fd15997fe8acb7ff4565b7fa2b2cffd15955fe8aca6ff456517fa2b283fd1593bfe8ac9aff4564b7fa2b23ffd15901fe8ac7bff4563bffa2b1d7fd158c7fe8ac60ff4562e7fa2b153fd1589bfe8ac49ff456207fa2b09ffd15843fe8ac1fff4560cffa2b057fd15827fe8ac11ff45606ffa2b01bfd15809fe8a
  | 1 => 0x6daff853667fc29a0ffe14cfbff0a65fff8532d7fc2994bfe14c8bff0a63fff853147fc29897fe14c45ff0a610ff853067fc29803fe14bf3ff0a5eeff852f2ffc2977bfe14ba1ff0a5ceff852e5ffc2971bfe14b85ff0a5bcff852d6ffc296affe14b47ff0a587ff852c07fc295bbfe14a95ff0a53fff8529f7fc294dffe14a49ff0a51fff8528c7fc2942ffe149e5ff0a4ecff85273ffc2936bfe149afff0a4caff85262ffc29313fe14979ff0a4b8ff8524effc29273fe14937ff0a484ff8523f7fc291dbfe148c1ff0a44eff852187fc290bbfe14821ff0a400ff851ff7fc28fabfe147c7ff0a
  | 2 => 0xbecff855ef7fc2af73fe157a5ff0abccff855e37fc2aefffe1576bff0abafff855d17fc2adf7fe156c1ff0ab52ff855a4ffc2acf7fe15679ff0ab38ff8559affc2accbfe15647ff0aadbff85565ffc2aa63fe150f7ff0a871ff854347fc2a18bfe150a7ff0a842ff8541fffc2a0e3fe15065ff0a81dff8540affc2a047fe15021ff0a807ff85401ffc29feffe14fb3ff0a7c9ff853d9ffc29ec7fe14f53ff0a79aff853cbffc29e37fe14f11ff0a77bff853baffc29daffe14ec5ff0a754ff853a47fc29d03fe14e35ff0a715ff853877fc29c33fe14dfbff0a6f7ff853777fc29ba3fe14dc5ff0a
  | 3 => 0x52a3fcd2851fe693c4ff349c87f9a4d93fcd26a9fe69254ff348da7f9a45b3fcd2269fe69110ff3487c7f9a3fd3fcd1fd1fe68e98ff347487f9a38c3fcd19e1fe687a0ff341b47f9a0ce3fcd02f1fe6932bfc148c1fb0a3ddbf851c6dfc287c2fe1498aff0ace6ff85670ffc2b367fe159afff0acc8ff856637fc2b2effe1596bff0acb4ff856597fc2b2c3fe15953ff0aca5ff8564e7fc2b267fe1592bff0ac8eff8563d7fc2b1dbfe158e9ff0ac62ff8562dffc2b167fe158a7ff0ac2cff856137fc2b08ffe15841ff0ac14ff856097fc2b033fe1580bff0abfeff855f9ffc2afc3fe157ddff0a
  | 4 => 0x13ffc5808ffe2c03fff1601bff8b00bffc5a657f86ad17f6348c1fb1a33efd8d615dfc6971afe347bb7f1a38dbf8d0f85fc69315fe34997fa9aceabf4d626dfa6af9afd35702fe9a45e7f4d21e3fa68c25fd34fa77d9a464becd29cdee6ad91ef3467ef79ab91b7cd3eadbe6919adf347bf6f9a3b0b7cd0fbdbe69f5e7f348d33f9ad323fcd6909fe6b350ff359267f9ac163fcd5df1fe6ae2cff356bc7f9ab373fcd5319fe69e1cff34e6c7f9a71f3fcd3501fe699b0ff34cd27f9a6383fcd3101fe69864ff34c2a7f9a5ff3fcd2fb9fe69734ff34b947f9a5c43fcd2c81fe6951cff34a747f9a
  | 5 => 0x86ffc5842ffe2c213ff16107ff8b082ffc5840ffe2c203ff160ffff8b07effc583effe2c1f3ff160f7ff8b07affc583cffe2c1e3ff160efff8b076ffc583affe2c1d3ff160e7ff8b072ffc5838ffe2c1c3ff160dfff8b06effc5836ffe2c1b3ff160d7ff8b06affc5834ffe2c1a3ff160cfff8b066ffc5832ffe2c193ff160c7ff8b062ffc5830ffe2c183ff160bfff8b05effc582effe2c16fff160b3ff8b057ffc5829ffe2c147ff16097ff8b049ffc5820ffe2c0ffff1606bff8b033ffc5813ffe2c097ff16047ff8b021ffc580fffe2c077ff16037ff8b01affc580cffe2c05fff1602bff8b
  | 6 => 0xc6ffc5862ffe2c313ff16187ff8b0c2ffc5860ffe2c303ff1617fff8b0beffc585effe2c2f3ff16177ff8b0baffc585cffe2c2e3ff1616fff8b0b6ffc585affe2c2d3ff16167ff8b0b2ffc5858ffe2c2c3ff1615fff8b0aeffc5856ffe2c2b3ff16157ff8b0aaffc5854ffe2c2a3ff1614fff8b0a6ffc5852ffe2c293ff16147ff8b0a2ffc5850ffe2c283ff1613fff8b09effc584effe2c273ff16137ff8b09affc584cffe2c263ff1612fff8b096ffc584affe2c253ff16127ff8b092ffc5848ffe2c243ff1611fff8b08effc5846ffe2c233ff16117ff8b08affc5844ffe2c223ff1610fff8b
  | 7 => 0x106ffc5882ffe2c413ff16207ff8b102ffc5880ffe2c403ff161ffff8b0feffc587effe2c3f3ff161f7ff8b0faffc587cffe2c3e3ff161efff8b0f6ffc587affe2c3d3ff161e7ff8b0f2ffc5878ffe2c3c3ff161dfff8b0eeffc5876ffe2c3b3ff161d7ff8b0eaffc5874ffe2c3a3ff161cfff8b0e6ffc5872ffe2c393ff161c7ff8b0e2ffc5870ffe2c383ff161bfff8b0deffc586effe2c373ff161b7ff8b0daffc586cffe2c363ff161afff8b0d6ffc586affe2c353ff161a7ff8b0d2ffc5868ffe2c343ff1619fff8b0ceffc5866ffe2c333ff16197ff8b0caffc5864ffe2c323ff1618fff8b
  | 8 => 0x146ffc58a2ffe2c513ff16287ff8b142ffc58a0ffe2c503ff1627fff8b13effc589effe2c4f3ff16277ff8b13affc589cffe2c4e3ff1626fff8b136ffc589affe2c4d3ff16267ff8b132ffc5898ffe2c4c3ff1625fff8b12effc5896ffe2c4b3ff16257ff8b12affc5894ffe2c4a3ff1624fff8b126ffc5892ffe2c493ff16247ff8b122ffc5890ffe2c483ff1623fff8b11effc588effe2c473ff16237ff8b11affc588cffe2c463ff1622fff8b116ffc588affe2c453ff16227ff8b112ffc5888ffe2c443ff1621fff8b10effc5886ffe2c433ff16217ff8b10affc5884ffe2c423ff1620fff8b
  | 9 => 0x186ffc58c2ffe2c613ff16307ff8b182ffc58c0ffe2c603ff162ffff8b17effc58beffe2c5f3ff162f7ff8b17affc58bcffe2c5e3ff162efff8b176ffc58baffe2c5d3ff162e7ff8b172ffc58b8ffe2c5c3ff162dfff8b16effc58b6ffe2c5b3ff162d7ff8b16affc58b4ffe2c5a3ff162cfff8b166ffc58b2ffe2c593ff162c7ff8b162ffc58b0ffe2c583ff162bfff8b15effc58aeffe2c573ff162b7ff8b15affc58acffe2c563ff162afff8b156ffc58aaffe2c553ff162a7ff8b152ffc58a8ffe2c543ff1629fff8b14effc58a6ffe2c533ff16297ff8b14affc58a4ffe2c523ff1628fff8b
  | 10 => 0x1c6ffc58e2ffe2c713ff16387ff8b1c2ffc58e0ffe2c703ff1637fff8b1beffc58deffe2c6f3ff16377ff8b1baffc58dcffe2c6e3ff1636fff8b1b6ffc58daffe2c6d3ff16367ff8b1b2ffc58d8ffe2c6c3ff1635fff8b1aeffc58d6ffe2c6b3ff16357ff8b1aaffc58d4ffe2c6a3ff1634fff8b1a6ffc58d2ffe2c693ff16347ff8b1a2ffc58d0ffe2c683ff1633fff8b19effc58ceffe2c673ff16337ff8b19affc58ccffe2c663ff1632fff8b196ffc58caffe2c653ff16327ff8b192ffc58c8ffe2c643ff1631fff8b18effc58c6ffe2c633ff16317ff8b18affc58c4ffe2c623ff1630fff8b
  | 11 => 0x206ffc5902ffe2c813ff16407ff8b202ffc5900ffe2c803ff163ffff8b1feffc58feffe2c7f3ff163f7ff8b1faffc58fcffe2c7e3ff163efff8b1f6ffc58faffe2c7d3ff163e7ff8b1f2ffc58f8ffe2c7c3ff163dfff8b1eeffc58f6ffe2c7b3ff163d7ff8b1eaffc58f4ffe2c7a3ff163cfff8b1e6ffc58f2ffe2c793ff163c7ff8b1e2ffc58f0ffe2c783ff163bfff8b1deffc58eeffe2c773ff163b7ff8b1daffc58ecffe2c763ff163afff8b1d6ffc58eaffe2c753ff163a7ff8b1d2ffc58e8ffe2c743ff1639fff8b1ceffc58e6ffe2c733ff16397ff8b1caffc58e4ffe2c723ff1638fff8b
  | 12 => 0x246ffc5922ffe2c913ff16487ff8b242ffc5920ffe2c903ff1647fff8b23effc591effe2c8f3ff16477ff8b23affc591cffe2c8e3ff1646fff8b236ffc591affe2c8d3ff16467ff8b232ffc5918ffe2c8c3ff1645fff8b22effc5916ffe2c8b3ff16457ff8b22affc5914ffe2c8a3ff1644fff8b226ffc5912ffe2c893ff16447ff8b222ffc5910ffe2c883ff1643fff8b21effc590effe2c873ff16437ff8b21affc590cffe2c863ff1642fff8b216ffc590affe2c853ff16427ff8b212ffc5908ffe2c843ff1641fff8b20effc5906ffe2c833ff16417ff8b20affc5904ffe2c823ff1640fff8b
  | 13 => 0x286ffc5942ffe2ca13ff16507ff8b282ffc5940ffe2ca03ff164ffff8b27effc593effe2c9f3ff164f7ff8b27affc593cffe2c9e3ff164efff8b276ffc593affe2c9d3ff164e7ff8b272ffc5938ffe2c9c3ff164dfff8b26effc5936ffe2c9b3ff164d7ff8b26affc5934ffe2c9a3ff164cfff8b266ffc5932ffe2c993ff164c7ff8b262ffc5930ffe2c983ff164bfff8b25effc592effe2c973ff164b7ff8b25affc592cffe2c963ff164afff8b256ffc592affe2c953ff164a7ff8b252ffc5928ffe2c943ff1649fff8b24effc5926ffe2c933ff16497ff8b24affc5924ffe2c923ff1648fff8b
  | 14 => 0x2c6ffc5962ffe2cb13ff16587ff8b2c2ffc5960ffe2cb03ff1657fff8b2beffc595effe2caf3ff16577ff8b2baffc595cffe2cae3ff1656fff8b2b6ffc595affe2cad3ff16567ff8b2b2ffc5958ffe2cac3ff1655fff8b2aeffc5956ffe2cab3ff16557ff8b2aaffc5954ffe2caa3ff1654fff8b2a6ffc5952ffe2ca93ff16547ff8b2a2ffc5950ffe2ca83ff1653fff8b29effc594effe2ca73ff16537ff8b29affc594cffe2ca63ff1652fff8b296ffc594affe2ca53ff16527ff8b292ffc5948ffe2ca43ff1651fff8b28effc5946ffe2ca33ff16517ff8b28affc5944ffe2ca23ff1650fff8b
  | 15 => 0x306ffc5982ffe2cc13ff16607ff8b302ffc5980ffe2cc03ff165ffff8b2feffc597effe2cbf3ff165f7ff8b2faffc597cffe2cbe3ff165efff8b2f6ffc597affe2cbd3ff165e7ff8b2f2ffc5978ffe2cbc3ff165dfff8b2eeffc5976ffe2cbb3ff165d7ff8b2eaffc5974ffe2cba3ff165cfff8b2e6ffc5972ffe2cb93ff165c7ff8b2e2ffc5970ffe2cb83ff165bfff8b2deffc596effe2cb73ff165b7ff8b2daffc596cffe2cb63ff165afff8b2d6ffc596affe2cb53ff165a7ff8b2d2ffc5968ffe2cb43ff1659fff8b2ceffc5966ffe2cb33ff16597ff8b2caffc5964ffe2cb23ff1658fff8b
  | 16 => 0x346ffc59a2ffe2cd13ff16687ff8b342ffc59a0ffe2cd03ff1667fff8b33effc599effe2ccf3ff16677ff8b33affc599cffe2cce3ff1666fff8b336ffc599affe2ccd3ff16667ff8b332ffc5998ffe2ccc3ff1665fff8b32effc5996ffe2ccb3ff16657ff8b32affc5994ffe2cca3ff1664fff8b326ffc5992ffe2cc93ff16647ff8b322ffc5990ffe2cc83ff1663fff8b31effc598effe2cc73ff16637ff8b31affc598cffe2cc63ff1662fff8b316ffc598affe2cc53ff16627ff8b312ffc5988ffe2cc43ff1661fff8b30effc5986ffe2cc33ff16617ff8b30affc5984ffe2cc23ff1660fff8b
  | 17 => 0x386ffc59c2ffe2ce13ff16707ff8b382ffc59c0ffe2ce03ff166ffff8b37effc59beffe2cdf3ff166f7ff8b37affc59bcffe2cde3ff166efff8b376ffc59baffe2cdd3ff166e7ff8b372ffc59b8ffe2cdc3ff166dfff8b36effc59b6ffe2cdb3ff166d7ff8b36affc59b4ffe2cda3ff166cfff8b366ffc59b2ffe2cd93ff166c7ff8b362ffc59b0ffe2cd83ff166bfff8b35effc59aeffe2cd73ff166b7ff8b35affc59acffe2cd63ff166afff8b356ffc59aaffe2cd53ff166a7ff8b352ffc59a8ffe2cd43ff1669fff8b34effc59a6ffe2cd33ff16697ff8b34affc59a4ffe2cd23ff1668fff8b
  | 18 => 0xa56ffc5d2affe2e953ff174a7ff8ba52ffc5d28ffe2e943ff1749fff8ba4effc5d26ffe2e933ff17497ff8ba4affc5d24ffe2e923ff1748fff8ba46ffc5d22ffe2e913ff17487ff8ba42ffc5d20ffe2e903ff1747fff8ba3effc5d1effe2e8f3ff17477ff8ba3affc5d1cffe2e8e3ff1746fff8ba36ffc5d1affe2e8d3ff17467ff8ba32ffc5d18ffe2e8c3ff1745fff8ba2effc5d16ffe2e8b3ff17457ff8ba2affc5d14ffe2e8a3ff1744fff8ba26ffc5d12ffe2e893ff17447ff8ba22ffc5d10ffe2e883ff1743fff8ba1effc5d0effe2e873ff17437ff8ba1affc5d0cffe2ce23ff1670fff8b
  | 19 => 0xa96ffc5d4affe2ea53ff17527ff8ba92ffc5d48ffe2ea43ff1751fff8ba8effc5d46ffe2ea33ff17517ff8ba8affc5d44ffe2ea23ff1750fff8ba86ffc5d42ffe2ea13ff17507ff8ba82ffc5d40ffe2ea03ff174ffff8ba7effc5d3effe2e9f3ff174f7ff8ba7affc5d3cffe2e9e3ff174efff8ba76ffc5d3affe2e9d3ff174e7ff8ba72ffc5d38ffe2e9c3ff174dfff8ba6effc5d36ffe2e9b3ff174d7ff8ba6affc5d34ffe2e9a3ff174cfff8ba66ffc5d32ffe2e993ff174c7ff8ba62ffc5d30ffe2e983ff174bfff8ba5effc5d2effe2e973ff174b7ff8ba5affc5d2cffe2e963ff174afff8b
  | 20 => 0xad6ffc5d6affe2eb53ff175a7ff8bad2ffc5d68ffe2eb43ff1759fff8baceffc5d66ffe2eb33ff17597ff8bacaffc5d64ffe2eb23ff1758fff8bac6ffc5d62ffe2eb13ff17587ff8bac2ffc5d60ffe2eb03ff1757fff8babeffc5d5effe2eaf3ff17577ff8babaffc5d5cffe2eae3ff1756fff8bab6ffc5d5affe2ead3ff17567ff8bab2ffc5d58ffe2eac3ff1755fff8baaeffc5d56ffe2eab3ff17557ff8baaaffc5d54ffe2eaa3ff1754fff8baa6ffc5d52ffe2ea93ff17547ff8baa2ffc5d50ffe2ea83ff1753fff8ba9effc5d4effe2ea73ff17537ff8ba9affc5d4cffe2ea63ff1752fff8b
  | 21 => 0xb16ffc5d8affe2ec53ff17627ff8bb12ffc5d88ffe2ec43ff1761fff8bb0effc5d86ffe2ec33ff17617ff8bb0affc5d84ffe2ec23ff1760fff8bb06ffc5d82ffe2ec13ff17607ff8bb02ffc5d80ffe2ec03ff175ffff8bafeffc5d7effe2ebf3ff175f7ff8bafaffc5d7cffe2ebe3ff175efff8baf6ffc5d7affe2ebd3ff175e7ff8baf2ffc5d78ffe2ebc3ff175dfff8baeeffc5d76ffe2ebb3ff175d7ff8baeaffc5d74ffe2eba3ff175cfff8bae6ffc5d72ffe2eb93ff175c7ff8bae2ffc5d70ffe2eb83ff175bfff8badeffc5d6effe2eb73ff175b7ff8badaffc5d6cffe2eb63ff175afff8b
  | 22 => 0x1f4bfc58f85fe2c7a2ff163c97f8b1e0bfc58ee5fe2c6f6ff163377f8b191bfc58b0dfe2c576ff162b57f8b12cbfc588edfe2c442ff162097f8b0e7bfc586d5fe2c33aff161977f8b0c6bfc585bdfe2c26aff160d97f8b05ebfc582ddfe2c146ff160677f8bada7fc5d2c3fe2e8e5ff16704ff8b37a7fc59afbfe2ccf1ff1664cff8b2ca7fc591ebfe2c8a5ff1641eff8b2047fc58f8bfe2c7a1ff1637cff8b1927fc58ae3fe2c509ff161b4ff8b0ce7fc585c3fe2c179ff16096ff8bb22ffc5d90ffe2ec83ff1763fff8bb1effc5d8effe2ec73ff17637ff8bb1affc5d8cffe2ec63ff1762fff8b
  | 23 => 0x369f7c59a07be2cb63df1654fef8b265f7c591cfbe2c803df163efef8b1baf7c58c6fbe2c2ffdf16167ef8b387efc59b577e2cd07bf165c3df8b2c8efc595477e2c92bbf163f1df8b1bbefc58c7f7e2c607bf16183df8b0b5efc59c46fe2cdaf7f16685bf8b2a9dfc591d6fe2c80b7f16379bf8b183dfc599e1fe2c7a0ff161b47f8b0ce3fc5d805fe2ebaaff1756f7f8ba91bfc5d3ddfe2e8e2ff167037f8b33cbfc599bdfe2ccceff1662d7f8b300bfc597c5fe2cbc6ff165d37f8b2e2bfc596d5fe2cb26ff165437f8b298bfc592fdfe2c8f2ff164457f8b20ebfc5901dfe2c7e6ff163ef7f8b
  | 24 => 0x292ff8591affc2c7ebfe163e1ff0b1b4ff858c37fc2c5e7fe162c5ff0b0cfff85855ffc2c23bfe175e5fe8baddff45d66ffa2ea67fd16707fe8b320ff45984ffa2cbeffd16587fe8b293ff45941ffa2c93ffd1646dfe8b210ff458fdffa2c7cffd1636dfe8b188ff458b87fa2c593fd161b9fe8b0baff45856ffa2c277fd1611ffe8b384fec599eff62cb17fb16547fd8b237fec58c57f62c5effb1615ffd8b385fdc59b3fee2ccfbf71658dfb8b2a4fdc591c7ee2c7f3f716317fb8b17dfdc59b47de2ccffef1658ff78b2a6fbc58ff7de2c6e3ef162fff78b0b1fbc58fbdbe2ce1bdf166fdef8b
  | 25 => 0x11dbfcd8885fe6c412ff361cf7f9b0dabfcd8675fe6c32eff3618d7f9b0c4bfcd85bdfe6c26aff360d97f9b05ebfcd82ddfe6c146ff360677f9b027bfcdd6d3fe6ea7dff37532ff9ba977fcdd413fe6e98dff374b0ff9ba447fcdd1cbfe6ce09ff366f4ff9b35f7fcd99fbfe6ccf1ff3664cff9b31e7fcd984bfe6cb4dff36594ff9b23d7fcd914bfe6c83dff36408ff9b1f17fcd8f43fe6c6f9ff36364ff9b1927fcd8ae3fe6c565ff36284ff9b0da7fcd867bfe6c339ff36170ff9b08b7fcd82f3fe6c12dff36032ff9b1f0bf85d6dffc2eb2ffe17531ff0b366ff85993ffc2cc7ffe16585ff0b
  | 26 => 0xb00bfcdd755fe6eb66ff375ab7f9bad0bfcdd67dfe6eb32ff375977f9bab7bfcdd48dfe6ea06ff374f77f9ba6abfcdd31dfe6e986ff374b77f9ba43bfcdd1c5fe6ce06ff366b17f9b349bfcd99e5fe6ccdeff3666b7f9b333bfcd98b5fe6cc3eff3661b7f9b30abfcd9845fe6cc02ff365f17f9b2f1bfcd974dfe6cb8aff365b57f9b2c9bfcd950dfe6ca62ff365037f9b268bfcd92fdfe6c8f2ff364697f9b222bfcd9075fe6c80eff363f37f9b1f7bfcd8fa5fe6c7caff363e17f9b1e8bfcd8f25fe6c782ff363bd7f9b1dcbfcd8dedfe6c66eff363237f9b161bfcd8aedfe6c56aff362597f9b
  | 27 => 0x2a3fecd91bff66c62bfb362f7fd9b0affecd9c2fee6cd9ff73667dfb9b2c6fdcd9527ee6c8e3f7363f9fb9b18bfdcd8befee6ccfdef366d1f79b33ffbcd963fde6ca9bef363fdf79b1b8fbcd8bffde6c2c7ef363ef6f9b386f7cd9bf7be6cda7df36681ef9b2d8f7cd953fbe6c997df36473ef9b200f7cd8fbfbe6c6ebdf3631bef9b0bff7cd859fbe6ce1fbf366d5df9b341efcd970f7e6cb23bf36551df9b24aefcd8fc77e6c6efbf3631fdf9b181efcd860f7e6c2d7bf36711bf9b36bdfcd9a16fe6caa77f36475bf9b202dfcd8de6fe6c60f7f374c67f9b33c3fcd8f41fe6c368ff3619c7f9b
  | 28 => 0x2d4ff8d9617fc6ca4bfe364afff1b235ff8d90d7fc6c7ebfe363e3ff1b1f0ff8d8da7fc6c64ffe3630dff1b179ff8d8b17fc6c33ffe36157ff1b08eff8d80cffc6cc25fd375e5fe9baddff4dd66ffa6ea67fd374d5fe9ba46ff4dd1d7fa6e8e7fd3746ffe9ba2eff4dd157fa6ce0ffd366e9fe9b335ff4d9907fa6cc2ffd36613fe9b308ff4d97dffa6cb0ffd36527fe9b283ff4d927ffa6c8dbfd36447fe9b210ff4d8fdffa6c7cffd363bdfe9b1b6ff4d8c47fa6c5c3fd362c9fe9b13aff4d873ffa6c373fd36189fe9b0baff4d856ffa6c277fd3611ffe9b027ff4d9c27f66ccf7fb3658bfd9b
  | 29 => 0x31ffc60187fe300bfff1805dff8c02dffc60167fe300afff18055ff8c029ffc60147fe3009fff1804dff8c025ffc60127fe3008fff18045ff8c021ffc60107fe3007fff1803dff8c01dffc600e7fe3006fff18035ff8c019ffc600c7fe3005fff1802dff8c015ffc600a7fe3004fff18025ff8c011ffc60087fe3003fff1801dff8c00dffc60067fe3002fff1867dfb2b1f0bf95984bfaaccfdef563ef6faba633fd599e1feac7a0ff561b47fab0ce3fd599f7ec6c7c2fe37603ff1bb00ff8dd7bffc6eb6ffe37597ff1babbff8dd4c7fc6e913fe366cdff1b33eff8d993ffc6cc7ffe365d7ff1b
  | 30 => 0xcff4602f1fe3017aff180b77f8c051bfc601f5fe300ceff180bcff8c04b7fc65117fe32887ff19441ff8ca1fffc650f7fe32877ff19439ff8ca1bffc650d7fe32867ff180bdff8c05dffc602e7fe3016fff180b5ff8c059ffc602c7fe3015fff180adff8c055ffc602a7fe3014fff180a5ff8c051ffc60287fe3013fff1809dff8c04dffc60267fe3012fff18095ff8c049ffc60247fe3011fff1808dff8c045ffc60227fe3010fff18085ff8c041ffc60207fe300ffff1807dff8c03dffc601e7fe300efff18075ff8c039ffc601c7fe300dfff1806dff8c035ffc601a7fe300cfff18065ff8c
  | 31 => 0x48ffce023ffe7011bff3808bff9c044ffce021ffe7010bff38083ff9c040ffce01fffe700fbff3807bff9c03cffce01dffe700ebff38073ff9c038ffce01bffe700dbff3806bff9c034ffce019ffe700cbff38063ff9c030ffce017ffe700bbff3805bff9c02cffce015ffe700abff38053ff9c028ffce013ffe7009bff3804bff9c024ffce011ffe7008bff38043ff9c020ffce00fffe7007bff3803bff9c01cffce00dffe7006bff38033ff9c018ffce00bffe7005bff3802bff9c014ffce009ffe7004bff38023ff9c010ffce007ffe7003bff3801bff9c00cffce005ffe70043fe1803dfe8c
  | _ => 0
def ns1_Data2_ : Nat → Nat
  | 0 => 0x3ebfd6019dfeb009eff59444ffac05e7fd6025bfeb0065ff59433ff1c019ff8e0087fc7286bfd3804ffe9c01eff4e0067fa7286ffb39439fb9ca1dfbce50f7be7287fbf39441bf9c05e3fce510dfe7017aff380b77f9c051bfce01f5fe700ceff3804f7f9ca227fce02f3fe7012dff38032ff9ca22ffce510ffe72883ff3943fff9ca1effce50effe72873ff39437ff9ca1affce50cffe7017bff380bbff9c05cffce02dffe7016bff380b3ff9c058ffce02bffe7015bff380abff9c054ffce029ffe7014bff380a3ff9c050ffce027ffe7013bff3809bff9c04cffce025ffe7012bff38093ff9c
  | 1 => 0x2f1fef2867fe58033ff2c010ff9650d7fab009ffd5803dfeac00cff5650dff6b2873f75943bf7aca1ef7d650ff7eb28837f580bc7faca21bfd602f5feb016eff580a37fac
  | _ => 0
def ns1_Data (i : Nat) : Nat :=
  match i/32 with
  | 0 => ns1_Data0_ (i % 32)
  | 1 => ns1_Data1_ (i % 32)
  | 2 => ns1_Data2_ (i % 32)
  | _ => 0
def ns1_ (i : Nat) : Nat := (ns1_Data (i/64) >>> (29*(i % 64))) &&& 536870911
def ns2_Data0_ : Nat → Nat
  | 0 => 0x5ca4603d842d2a301ec21365180f6108c07a27b084603c93d8423006d1ec22372254ee1112a96a7708a133dd3b8444a9da1dc22858e34ee1112a3e07708a108dc378446f3229bc223707dcde114231b85f088e05802f8449221f17c210f8e1cbe111b83f05f08a128dc1f845092628fc224950f87e1087c7103f088c40cf1f842348678fc2256c07af1111288787c884643093e44454c545aa2250132ed5109963ef6a888a1039b5444ae80f5aa222a407ad51076003d6a884cb45b3d4426599e1ea222590f0dd108783ee6e8890905e374444c21e0fa211a4c247d1112867c79888958943ac423219f9d62225e250bb111bcc8e6b8864733c35c44702c116e22260cf8771112f12a57888951f82bc444c44a8de211a4cfc6f1113112c2f88a0fa0e3e03d085071b81e83d180f20f42341e5d07a124601d83d08c4a95c1e84a2546e0f4254202f07
  | 1 => 0x6d805e1fc4b6502f0fe25b101787f12d7a0bc3f896b205e1fc4b4382f0fe259d01787f12cc60bc3f8965605e1fc4b1f02f0fe258b01787f12c3c0bc3f895fd05e1fc4af102f0fe256c41787f12b1c0bc3f8958405e1fc4abc02f0fe255501787f12a9c0bc3f8951d05e1fc4a8b02f0fe2540c1787f129f20bc3f894ce05e1fc4a5082f0fe251a41787f128c60bc3f8941405e1fc49cf02f0fe24e5c1787f127100bc3f8936b05e1fc49a102f0fe24aa41787f124740bc3f8920205e1fc48de02f0fe2460c1787f131880963f8946904b1fc4a3480c8fe25328b1bd41115114f7a08a144cbbd042658f85e82229c07af41071a03d7a0846043c7d04265163f98228607dedc109943ef6e08a0e8dc3f0426522d9f8210f0f74fc1087871a7e08a0e1f03f0421e0f81f82283e370fa1141e98a7d088c10cf3e842320679f422371180f610c488c07b08
  | 2 => 0x6151831fc499e0c18fe247a060c7f128d22b83f898c40da1fc4a3186d0fe24e203687f126d61b43f893420da1fc495486d0fe248e83687f124041b43f891bc0da1fc48c186d0fe251a43387f1271019c3f8936b0ce1fc49a10670fe24aa43387f1247419c3f892020ce1fc48de0670fe2460c3387f139fe0bc3f89cd305e1fc4e6002f0fe272141787f138ce0bc3f89c3d05e1fc4e1882f0fe26e9c1787f136840bc3f899e205e1fc4ce882f0fe266cc1787f133020bc3f8995305e1fc4c8c82f0fe263201787f131300bc3f8987f05e1fc4c3a82f0fe2615c1787f1308c0bc3f8982b05e1fc4c0582f0fe25f901787f12fae0bc3f897cd05e1fc4be402f0fe25f041787f12f6e0bc3f897ad05e1fc4bc602f0fe25e181787f12efe0bc3f8976005e1fc4ba602f0fe25cf41787f12e280bc3f8970905e1fc4b7e02f0fe25bd41787f12dda0bc3f89
  | 3 => 0x56605e2fc4aa982f17e25534178bf12a900bc5f8953d05e2fc4a8a82f17e25408178bf129f00bc5f894cd05e2fc4a6002f17e252e8178bf128ce0bc5f8946205e2fc4a0982f17e25010178bf127c00bc5f893b105e2fc49ce82f17e24e1c178bf126d40bc5f8934105e2fc497082f17e24b20178bf125500bc5f8924a05e2fc48fc02f17e246ec178bf1231e0bc5f8918105e2fc486082f17e242d4178bf12c700765f897870162fc4c4c21f0fe254e8dac7f1317a6783f8938833c1fc49b599e0fe24d08cf07f126785523f8994523a1fc4b9b11d0fe258e08e87f1292a4743f8933c23a1fc4cb09010fe25e1c8087f12cd24043f894d52021fc499e1010fe262607c47f131f23d03f893881e81fc49b58f40fe24d087a07f125523d03f8923a1e81fc49010f40fe263c46f07f12bfe3783f893a61bc1fc49c60de0fe24cf06f07f123d03783f89
  | 4 => 0x86c05e2fc4c3302f17e26148178bf130980bc5f8984505e2fc4c1e02f17e260c0178bf130540bc5f8982505e2fc4c0c82f17e26034178bf130140bc5f8980205e2fc4bfc82f17e25fc4178bf12fe00bc5f897eb05e2fc4bf482f17e25f9c178bf12fba0bc5f897d605e2fc4be382f17e25f00178bf12f6c0bc5f8979e05e2fc4bc582f17e25e14178bf12ef20bc5f8976605e2fc4bad82f17e25d60178bf12ea40bc5f8974b05e2fc4ba382f17e25d10178bf12e780bc5f8972c05e2fc4b8982f17e25bec178bf12dd80bc5f896e405e2fc4b6f02f17e25b40178bf12d860bc5f896bc05e2fc4b4b02f17e25a40178bf12d140bc5f8967b05e2fc4b3982f17e25954178bf12c920bc5f8964305e2fc4b1e82f17e258ac178bf12c3a0bc5f8961205e2fc4af482f17e25768178bf12ba80bc5f895a405e2fc4ac682f17e255f4178bf12aee0bc5f89
  | 5 => 0x2c80da2fc495406d17e24928368bf123f01b45f891bb0da2fc48c786d17e24604368bf132e819c5f893b10ce2fc49c386717e24da8338bf1268219c5f892e10ce2fc496406717e24aa0338bf1249419c5f891f80ce2fc48dd86717e2463c338bf1230219c5f8933c0c12fc48f406097e24368304bf1219c1825f896200b52fc4b0c85a97e256402d4bf1267816a5f891e80b52fc486d05a97e243382d4bf139fc0bc5f89cdf05e2fc4e6e02f17e27348178bf1397e0bc5f89c8405e2fc4e3582f17e271a8178bf138cc0bc5f89c4f05e2fc4e2102f17e270f0178bf138600bc5f89c2205e2fc4deb82f17e26f04178bf1372c0bc5f89b8505e2fc4dab82f17e26d38178bf136600bc5f89b2a05e2fc4cf082f17e26740178bf133700bc5f899b205e2fc4cc502f17e265e0178bf132bc0bc5f8995205e2fc4c8782f17e2625c178bf130fc0bc5f89
  | 6 => 0x20005e37c48fb82f1be246e8178df1231a0bc6f890bf05e37c485982f1be258540e4df128b60726f8933c03937c49fd00a1be251a519e3f128d23f11f8989743e2fc4c5e19e17e24e1ccf0bf126d46785f8934133c2fc499e17097e259b0b20bf12a145905f893fa2c82fc499e16417e24cf0aa0bf132ae4945f8994a24a2fc4c7012517e24cf0928bf126824445f8943e1f82fc499e0fc17e248a47e0bf131f03d05f897f11e82fc49f00f417e24e1c7a0bf126d43d05f893411e82fc49708f417e24b207a0bf125503d05f8924a1e82fc48fc0f417e257fc6ecbf1274c3765f8938c1bb2fc499e0dd97e247a06ecbf128da31e5f8944d18f2fc49fe8c797e24cf063cbf123d031e5f8933c1812fc48f40c097e2519c570bf123f02b85f8934115a2fc4c6186d17e25690368bf128c41b45f893870da2fc49b506d17e24d04368bf125c21b45f89
  | 7 => 0x74305e37c4b9102f1be25c64178df12e240bc6f8970805e37c4b7d02f1be25bd0178df12dd60bc6f896e305e37c4b6e82f1be25b5c178df12d920bc6f896bb05e37c4b5882f1be25a98178df12d2a0bc6f8968905e37c4b4302f1be259e8178df12ce40bc6f8966205e37c4b1e02f1be258a8178df12c460bc6f8961c05e37c4afe02f1be25764178df12ba60bc6f895ac05e37c4ad302f1be25630178df12b060bc6f8957a05e37c4ab502f1be25594178df12a980bc6f8953c05e37c4a8e02f1be25450178df12a1e0bc6f8950105e37c4a7b82f1be253cc178df129bc0bc6f894a005e37c4a4b02f1be25198178df128c20bc6f8944205e37c4a0182f1be24f9c178df127be0bc6f893c605e37c49d802f1be24ea8178df127380bc6f8938605e37c49bf02f1be24da4178df126800bc6f892d805e37c495382f1be24994178df124720bc6f89
  | 8 => 0xcb805e37c4e4582f1be2720c178df138fa0bc6f89c7c05e37c4e3282f1be27144178df1389c0bc6f89c4b05e37c4e2082f1be270ec178df138480bc6f89c0e05e37c4e0402f1be26f58178df137a00bc6f89bce05e37c4de382f1be26e98178df1369a0bc6f89b4105e37c4d9c82f1be26780178df1339e0bc6f899b105e37c4cc482f1be26600178df132ee0bc6f8995d05e37c4c8c02f1be26358178df1318e0bc6f8989605e37c4c3e82f1be261d0178df130d60bc6f8986505e37c4c3082f1be26158178df130a20bc6f8984b05e37c4c1d82f1be260d0178df1305e0bc6f8982105e37c4c0082f1be25fbc178df12fc60bc6f897d505e37c4be302f1be25efc178df12f6a0bc6f897ac05e37c4bd382f1be25e90178df12f420bc6f8979105e37c4bc502f1be25e10178df12efc0bc6f8977805e37c4bb382f1be25d7c178df12eae0bc6f89
  | 9 => 0x5ff1ba37c49d30dd1be24e306e8df126783746f891e81ba37c48fb8c91be263c8634df128da31a6f8944d18d37c49fe8c69be24cf0634df123d031a6f8933c16a37c49a00b09be247dc508df131841b46f896230da37c4a3086d1be24e18368df126fc1b46f893690da37c49a006d1be24b60368df1254e1b46f892650da37c491c86d1be24800368df123ee1b46f891ba0da37c48c686d1be265cc338df1292c19c6f893b00ce37c49c30671be24df8338df126d219c6f893400ce37c496c0671be24a9c338df124ca19c6f892390ce37c49000671be247dc338df1237419c6f8918d0ce37c499e05f9be247a02fcdf121b417e6f890ce0bf37c48fb85c1be265ec2ccdf12c401666f896190b337c4ac80599be24cf02ccdf123d01666f890da0b337c48670599be24cf0254df139fa0bc6f89cd105e37c4e6602f1be272f8178df139740bc6f89
  | 10 => 0x1f718397c4c4b21f1be262b0df8df12e3e6fc6f894f137e37c4a221bf1be2516cda4df135c66786f8946633c37c49c319e1be24df8cf0df126d26786f8934033c37c499e1951be24cf0c88df126805b46f898de2d837c4a8516c1be24cf0b60df1267854e6f898de26537c4a851329be24cf0994df131de4726f8973623937c4b1c11c9be252548e4df126784726f8998d20037c4bc39001be259a4800df129aa4006f8933c20037c4d1c8fb9be2642c7dcdf131aa3ee6f896971f737c4ac78fb9be250f87dcdf127403ee6f893821f737c49bd0fb9be24d7c7dcdf126783ee6f892ca1f737c491e8fb9be248a47dcdf124083ee6f898961f137c48fb8f89be263dc7a0df127be3d06f893861e837c49bf0f41be24da47a0df126803d06f892d81e837c49538f41be249947a0df124723d06f892001e837c48fb8f41be247dc6f8df131063746f89
  | 11 => 0x5e805e3bc4af082f1de25760178ef12ba40bc778958b05e3bc4aa902f1de2552c178ef12a260bc77894f605e3bc4a6e82f1de25330178ef1297e0bc778946505e3bc4a0102f1de24f98178ef126d00bc778933f05e3bc496382f1de24a98178ef123fc0bc77891b805e3bc48bf82f1de242c4178ef1312a07c7789584583c7c4a33a3353e24f80f7e9f127627614f894661f8a7c4e278fbd3e263507de9f1319c3ef4f897f01f7a7c4beb0fbd3e256347de9f129743ef4f894671f7a7c49ce8fbd3e24e1c7de9f126d43ef4f893411f7a7c49708fbd3e24b207de9f125503ef4f8924a1f7a7c48fc0fbd3e247dc6ee9f123ee31f4f891f7181a7c48fb860d3e247dc2d69f128d28cd2f898cf1f797c4beb8fbcbe256387de5f128d23ef2f8939e1f797c49c40fbcbe24dac7de5f126843ef2f892a91f797c491d0fbcbe248087de5f123ee3792f89
  | 12 => 0x1e80b13bc486d0589de243382c4ef1267e1347789cfc05e3bc4e6802f1de272f4178ef138c80bc7789c3a05e3bc4e1782f1de26f54178ef1374a0bc7789b5605e3bc4ce702f1de266c0178ef132ec0bc778995c05e3bc4ca882f1de2645c178ef1321c0bc77898ec05e3bc4c6302f1de26254178ef130e60bc778984805e3bc4c2202f1de260a4178ef130120bc77897f805e3bc4bf702f1de25f88178ef12fb80bc77897d405e3bc4be602f1de25f14178ef12f7c0bc77897ab05e3bc4bc482f1de25df4178ef12eca0bc778975e05e3bc4bab02f1de25d44178ef12e940bc778974205e3bc4b9d82f1de25be4178ef12de60bc77896ea05e3bc4b6102f1de25ae8178ef12d600bc778969405e3bc4b4282f1de259e4178ef12ce20bc778966e05e3bc4b2a02f1de25920178ef12c840bc778962905e3bc4b0202f1de257ec178ef12bd80bc7789
  | 13 => 0x5841fecbc4a33a32d5e251947e2af128d28cb378989543e3bc4d8019f9de262eccf0ef126d0678778933f33c3bc499f96d1de266b0b1cef12cd858e778950a2c73bc49fd1639de24cf0b1cef1267854c778933f2223bc4cb68ff1de25e1c7f8ef12cd23fc77894d51fe3bc499e0ff1de262547c0ef131ec3d077893681e83bc499f8f41de24b1c7a0ef1254c3d077891fe1e83bc4ca18dc1de257fc6e0ef1274c370778938c1b83bc499e0dc1de247a06e0ef126782fe77891e817f3bc499f8b09de24cfc568ef135f01b477894650da3bc49b406d1de24cfc368ef125ea1b477892c70da3bc495306d1de247f8368ef123701b477891a20da3bc48bf86d1de265c8338ef12cdc19c77893680ce3bc499f8671de24b1c338ef1254c19c77891fe0ce3bc48dc0671de245fc338ef1335616277896200b13bc4b0c8589de256402c4ef126781627789
  | 14 => 0x73a05e3dc4b8882f1ee25c1c178f712de40bc7b896dc05e3dc4b6b02f1ee25b20178f712d820bc7b896af05e3dc4b4202f1ee259e0178f712ce00bc7b8966105e3dc4b2382f1ee25904178f712c360bc7b8960305e3dc4afd02f1ee25780178f712bae0bc7b895b005e3dc4ac102f1ee255d8178f712aa20bc7b8953905e3dc4a8d82f1ee25438178f712a000bc7b894f505e3dc4a6582f1ee252f8178f71293e0bc7b8946005e3dc4a0902f1ee25004178f7127ca0bc7b8939305e3dc49c282f1ee24d9c178f71267c0bc7b892c605e3dc495202f1ee248e0178f7123f80bc7b8918b05e3dc48be82f1ee254e412cf712c92c91c789648183d3c4a33232d9e2634c7decf1319a3ef67897ee1f7b3c4bea0fbd9e2562c7decf128ca3ef67893681f7b3c499f8fbd9e24b1c7decf1254c3ef67891fe1f7b3c48fb8dc59e247dc5fecf123ee1636789
  | 15 => 0x44d18b3dc49fe8c59ee24cf062cf7123d03167b8933c17d3dc48f40be9ee24cf8584f71267c2b47b894600da3dc49c286d1ee24d9c368f71267c1b47b892c60da3dc495206d1ee248e0368f7123f81b47b8918b0da3dc48be86d1ee254e4338f71270a19c7b893670ce3dc499f0671ee24b18338f71254819c7b892380ce3dc48fe0671ee2462c338f7122fa19c7b89ccf05e3dc4e5e02f1ee27208178f7138720bc7b89c2e05e3dc4dd202f1ee26d54178f7136980bc7b89b4005e3dc4cc402f1ee265fc178f7132500bc7b8991605e3dc4c8682f1ee261c8178f7130c80bc7b8985005e3dc4c1702f1ee260a0178f7130400bc7b8981805e3dc4c0402f1ee26000178f712fee0bc7b897e105e3dc4be582f1ee25f10178f712f7a0bc7b897b405e3dc4bce82f1ee25e40178f712f060bc7b8977705e3dc4bb202f1ee25d74178f712ea00bc7b89
  | 16 => 0x17b05e3ec485782f1f62630412cfb128c80967d894640193ec48f0058dce2591c60f5713152a736b89647406b5c4c6f9c2dae26500d9ed7131dc67d6b898a02a4b5c4c4491c5ae265947f2d71270a3ef6b893671f7b5c499f0fbdae24b187ded71255c3ef6b892a41f7b5c491c0fbdae247f07ded7132fa3176b891f718bb5c48fb8bedae247802ced712c8e0a36b893b001eb5c4ac22c166e248e87f33712b0ab055b898aa539adc48dd86356e254e46f27712a74a727b8943e33e3dc49c299e1ee24d9ccf0f71267c6787b8933e2da3dc4b361631ee25428b18f7127f458c7b8933c2c63dc499e1521ee25cd88e0f712c704707b894952383dc499e11c1ee24cf8888f712f0e3f87b896691fc3dc4a6a8fe1ee24cf07f0f712a723d07b893851e83dc49b38f41ee24cf87a0f71258c3d07b892a41e83dc491c0f41ee247f07a0f7128da3167b89
  | 17 => 0x86a05e3ec4c3182f1f626154178fb1309e0bc7d8984305e3ec4c1d02f1f6260b4178fb1304e0bc7d8981f05e3ec4c0b82f1f625ffc178fb12fec0bc7d897ed05e3ec4bed82f1f625f4c178fb12f840bc7d897ba05e3ec4bce02f1f625e4c178fb12f040bc7d8977605e3ec4bb182f1f625d3c178fb12e920bc7d8973905e3ec4b8302f1f625be0178fb12de20bc7d896d505e3ec4b6382f1f625b00178fb12d720bc7d896ae05e3ec4b4f82f1f625a4c178fb12cee0bc7d8964605e3ec4b2002f1f6258ec178fb12c340bc7d8960205e3ec4af382f1f62577c178fb12bac0bc7d895d105e3ec4ad782f1f6255d4178fb12aa00bc7d8951a05e3ec4a8902f1f625434178fb129fe0bc7d894dc05e3ec4a4f02f1f625190178fb128be0bc7d8941105e3ec49cd82f1f624e10178fb1267a0bc7d892c505e3ec495182f1f6248dc178fb123140bc7d89
  | 18 => 0x6382373ec4a4a91b9f624cf08dcfb131283e27d894641e83ec49c20f41f624cf47a0fb1258a3d07d892a31e83ec491b8f41f6265a4628fb128da3147d8944d18a3ec49fe8c51f624cf0628fb123d03147d8945b17b3ec499e0bd9f6247a05ecfb128c82b87d898c10da3ec4a2f86d1f624e10368fb1267a1b47d892c50da3ec495186d1f6248dc368fb123141b47d8917b0da3ec4cb88671f624e10338fb1267a19c7d892c50ce3ec49518671f6248dc338fb1231419c7d8917b0ce3ec4ca48579f6258802bcfb12c3215e7d895900af3ec499e0579f6247a02bcfb121b415e7d890ce0af3ec4e7d82f1f627338178fb139020bc7d89c3805e3ec4e1682f1f626f50178fb136a80bc7d89b4b05e3ec4d9f82f1f62680c178fb133be0bc7d8998705e3ec4cbf02f1f6265d4178fb132b60bc7d8995005e3ec4c8602f1f626314178fb131280bc7d89
  | 19 => 0x44c05e3f44a1e02f1fa25028178fd127c80bc7e893ba05e3f449cd02f1fa24e44178fd127060bc7e8930905e3f4497d82f1fa24b0c178fd125060bc7e8923605e3f448fd82f1fa246d8178fd123100bc7e890ad05e3f4484782f1fa250f016cfd128780a27e8943c03e3f44a1e0199fa25854078fd128b603c7e8933c01e3f44a2d8061fa2591d91bd31258c2f7e989582237ecc4a9c857de62592191bcb1258e2f7e589465464bac4b24b2373625199192db131a43ef6d898cc1f7b6c4bf68fbdb625f4c7dedb128c83ef6d8939b1f7b6c49c20fbdb624cf47dedb1258a3ef6d892a31f7b6c491b8fbdb6247dc62adb123ee2f76d891f70afb6c4a33a32576251907e2bb128d28c93d8989443e3ec4c5d19e1f624e10cf0fb1267a6787d8988d2c53ec4b361629f625428b14fb127f458a7d8933c2c53ec499e1519f6262908dcfb12e6c46e7d89
  | 20 => 0x84005e3f44c1c82f1fa260b0178fd1303c0bc7e8981605e3f44bff02f1fa25fd4178fd12fd80bc7e897e005e3f44bed02f1fa25f28178fd12f700bc7e897b205e3f44bd502f1fa25e6c178fd12f2a0bc7e8977c05e3f44bb802f1fa25db4178fd12eb80bc7e8975505e3f44ba702f1fa25d04178fd12e660bc7e8973105e3f44b9582f1fa25c40178fd12e0a0bc7e8970305e3f44b7482f1fa25b84178fd12db60bc7e896d405e3f44b6302f1fa25ae0178fd12d240bc7e8966005e3f44b2982f1fa25930178fd12c740bc7e8960105e3f44af302f1fa256e4178fd12b5c0bc7e8958a05e3f44ac082f1fa255d0178fd12ad20bc7e8956205e3f44aa202f1fa254b8178fd12a320bc7e8950c05e3f44a7f02f1fa253e8178fd129e80bc7e894eb05e3f44a6d82f1fa2531c178fd1298c0bc7e894bd05e3f44a4a02f1fa25178178fd128b00bc7e89
  | 21 => 0x3830da3f4498486d1fa24bec368fd125861b47e892830da3f4491b06d1fa247ec368fd1236c1b47e891880da3f44d790671fa24e0c338fd1261219c7e892fb0ce3f449618671fa24a0c338fd1246c19c7e891fb0ce3f448db0671fa24620338fd126781747e896200ad3f44b0c8569fa256402b4fd1267815a7e891e80ad3f4486d0569fa243382b4fd126121347e8933c08f3f448f40479fa2436823cfd1219c11e7e89ce405e3f44e5b82f1fa27288178fd139000bc7e89c7505e3f44e3182f1fa27180178fd1389a0bc7e89c4905e3f44e2002f1fa2707c178fd138320bc7e89c0005e3f44dfa82f1fa26f68178fd137a60bc7e89bb005e3f44dd182f1fa26e64178fd1372a0bc7e89b8405e3f44da982f1fa26d28178fd1368c0bc7e89b3e05e3f44d9782f1fa26cac178fd135e40bc7e8987c05e3f44c3482f1fa26150178fd1309c0bc7e89
  | 22 => 0x46908f9f44a3480f4fa251a40327d128b68b07e8988b43c3f44a7e21e1fa250f90f0fd135e46787e89add33c3f44ade99e1fa25160cf0fd127066787e8933c3203f44d801849fa24cf0c24fd12bee5f67e8933c2fb3f4498496d1fa259b0b0cfd12a145867e893fa2c33f4499e1619fa24cf0a4cfd128b65067e8933c2833f44b9b11b1fa258e08d8fd1292a46c7e8933c2363f449849111fa24cf0840fd12f0e3f67e896691fb3f44a6a8fd9fa24cf07ecfd126783e67e8943c1f03f44d790f41fa251607a0fd127063d07e893091e83f4497d8f41fa24b0c7a0fd125063d07e8924f1e83f4491b0f41fa247ec7a0fd12bfe36c7e893a61b63f449c60db1fa24cf06d8fd123d036c7e8946d1883f44a268c41fa24ff4620fd126783107e891e81883f4499e0b21fa24c24584fd126122b47e8943c0e73f44d7906d1fa26300368fd128bc1b47e89
  | 23 => 0x38d01ebd4486300f5ea254e4032f51287867cfa892c7283f344a66a6675a253393336d1267e11ef689583581e7449b5132f3a25338da75d127be7bd6e893b03aeb744e268fbdba26bc87dedd135ba3ef6e89acd1f7b744d4c8fbdba263447dedd1313e3ef6e897ec1f7b744b810fbdba256f47dedd12b143ef6e894b91f7b7449d60fbdba24ea47dedd127343ef6e893831f7b7449900fbdba24c247dedd125f63ef6e892c31f7b7449498fbdba24a0c7dedd1249e3ef6e892361f7b7449080fbdba247ec7dedd128cc3e76e891f71f3b7448fb8db5ba247dc622dd123ee2e16e891f7164b7448fb86e5ba247dc2eadd123ee15b6e891f709db744a33047dba247dc23edd128cc03d6e893df01eb7449d800f5ba247dc07add128cc0196e893df00cb7449d80065ba247dc032dd12b08b039e894ce4cdcf4491d0fde7a24da860f3d128d23e73e89
  | 24 => 0x39905e3f849c682f1fc24d98178fe125840bc7f0923505e3f848fd02f1fc247c0178fe123680bc7f0918605e3f848bc82f1fc24588178fe1219e0bc7f090ab05e3f84a6282d9fc2637012cfe1313a0967f093dd04b3f849c68259fc247c012cfe131b807c7f094c50333f84a1f00c1fc250f8058fe1287c0227f0990a0103f84c6e0081fc25728040fe129b20207f090da0103f84a658bdfe225918b0fd912b0246fdc894cd17bee44a320f9df22519023ef9128c803d7c8946400cbe44a66265fca24ec007ad5129966d3ea892c6283f5449b3932faa24ec007bd51299a997da8936a17ded44a67265eea24d9c60f7513150a737a898924cbbd44a67a65dea2532c792f51236c18d7a894cb05ebd44a6582ddea2532c146f51299607d7a894cb033bd44bfa00f5ea25e5007af512c2803d7a8953901ebd44a4600f5ea24ec007af51275e03d7a89
  | 25 => 0x81505e3f84c0382f1fc25f64178fe12f920bc7f097b305e3f84bd482f1fc25e68178fe12f100bc7f0977b05e3f84bba82f1fc25d88178fe12ea80bc7f0974805e3f84ba002f1fc25c54178fe12dfa0bc7f096f705e3f84b6d02f1fc25b30178fe12d060bc7f0965f05e3f84b2902f1fc25914178fe12c7e0bc7f0962805e3f84b1282f1fc25888178fe12c200bc7f0960005e3f84afc82f1fc25794178fe12bbc0bc7f095d005e3f84ae702f1fc2572c178fe12b8c0bc7f095c205e3f84ad682f1fc2568c178fe12b0e0bc7f0958005e3f84aa502f1fc254f8178fe12a6e0bc7f0951f05e3f84a8c02f1fc2542c178fe129e40bc7f094ec05e3f84a6d02f1fc2535c178fe129940bc7f094c405e3f84a5e02f1fc252e0178fe1293a0bc7f0949c05e3f84a1802f1fc250b8178fe128200bc7f0940005e3f849f182f1fc24f74178fe127500bc7f09
  | 26 => 0x5ca0cf3f84ad28679fc2536433cfe127a219e7f093ca0cf3f849e48679fc24cf033cfe125b419e7f092220cf3f848f40679fc2458433cfe122b419e7f090da0cf3f84c6b8671fc24e34338fe126cc19c7f092c20ce3f8491a8671fc247e8338fe123e019c7f091b40ce3f848c30671fc245e4338fe122c419c7f090cf0ce3f848f805c1fc258802acfe12c321567f095900ab3f8499e0559fc247a02acfe121b41567f090ce0ab3f8486784d1fc24368238fe139ae0bc7f09cc605e3f84e5d82f1fc272c0178fe1392a0bc7f09c6205e3f84e2c82f1fc270b0178fe1384c0bc7f09c2005e3f84e0a02f1fc27014178fe137fc0bc7f09bee05e3f84de902f1fc26efc178fe137440bc7f09b5205e3f84da482f1fc26cf4178fe1366a0bc7f0987b05e3f84c3882f1fc261a0178fe130c40bc7f0985305e3f84c2102f1fc260e0178fe1303a0bc7f09
  | 27 => 0x3961f03f849c10f81fc24de87c0fe126be3e07f0933c1f03f849930f81fc24b287c0fe1247a3e07f092291f03f849078f81fc248107c0fe123e23e07f0988e1e83f849ee8f41fc24d987a0fe125843d07f092351e83f848fd0f41fc247c07a0fe123e037c7f095ff1b43f849d30da1fc24e306d0fe126783687f091e81b43f848f80c91fc251b4618fe1289a30c7f093fd1863f8499e0c31fc247a0618fe126782f27f091e81793f8499e0b11fc247a0588fe123e02b87f091f01423f84dff06d1fc26b6c368fe135961b47f09a980da3f84c6e06d1fc25bf4368fe12c441b47f095a30da3f84a7606d1fc25314368fe128ec1b47f094600da3f84a1706d1fc24d98368fe1264e1b47f0931f0da3f8496106d1fc24a48368fe1246a1b47f091fa0da3f848f806d1fc246d0368fe1230c1b47f091790da3f848b106d1fc26c0033cfe12c4819e7f09
  | 28 => 0x99c1f09f84c928f84fc262607c27e12fae3e13f0958e1f09f84a348f84fc24e787c27e127103e13f0936b1f09f849a10f84fc24aa47c27e124743e13f092021f09f848f80de4fc247c060e7e127103e2bf098dc4c53f84a5aa1f1fc252c10f8fe1316c7ba7f0943e3b43f84c749c69fc26228cf0fe126cc6787f0966c2c23f84a851611fc24fe8b08fe126785847f097362353f84b1c11a9fc252548d4fe1267846a7f097871fa3f84b348fd1fc253547e8fe126783f47f095911f13f84a5a8f89fc2528c7c4fe127ba3e27f0938d1f13f84d928f81fc26b687c0fe134b03e07f09a391f03f84cc18f81fc2642c7c0fe131ca3e07f098dd1f03f84c6e0f81fc262cc7c0fe1312a3e07f096971f03f84b1c8f81fc257707c0fe12b243e07f0958f1f03f84a628f81fc252907c0fe1287c3e07f0943d1f03f84a1e0f81fc250987c0fe127403e07f09
  | 29 => 0x4b81f7b7849d40fbdbc24e647dede126cc3ef6f092c21f7b78491a8fbdbc247e87dede1389c3e16f0999a1f0b784c918f85bc262587c2de12fde3e16f097d51f0b784ac60f85bc251987c2de127543e16f0939c1f0b7849c30f85bc24df87c2de126d23e16f093401f0b78496c0f85bc24a9c7c2de124ca3e16f092391f0b7849000f85bc247dc7c2de123e03756f091f71b4b7848f80c6dbc247dc61ade123ee2f36f091f70cfb7848f805fdbc247c02cede123ee1576f096452ca77849f01eed7c24ec4e36be1389e3e15f0999b1f0af84c920f857c2625c7c2be12fe03e15f097d61f0af84ac68f857c252e87c2be128ce3e15f0939d1f0af849c38f857c24da87c2be126823e15f092e11f0af849640f857c24aa07c2be124943e15f091f81f0af848f80ddd7c247c063ebe123e03035f091f00c1af848f805ad7c25619601be1270e3e2df09
  | 30 => 0x8e61fcbd849c28f85ec24d9c7c2f61267c3e17b092c61f0bd849570f85ec24a907c2f61253a3e17b092381f0bd848fe0f85ec265f062ef6123e03177b0998617dbd848f80bedec2518036af6123e00c77b0946005bbd849ee81bdec251800cef61271a03d7b094c54607d84a301afbec251807c5f61270a3e2fb0946015c7d84a3006d3ec25180365f6128c01a4fb0946005e7d84a3002ebec2518012df6128c006afb097460107d84b24322f9c24b1c5e7ce128c467fd7095801feeb84a3199fedc262547c0ee133323e177098951f0bb84bf70f85dc25f507c2ee12b163e177094651f0bb849b40f85dc24cfc7c2ee1258e3e177092a61f0bb848ff0f85dc247c06e2ee123e02ff77091f00b1bb84c4a8f83dc2607412dee1312a020f709463461d7849ef9eedbc24ec0e36de131a03ef6f098cb1f7b784ae30fbdbc2547c7dede129e43ef6f09
  | 31 => 0x4290dcbf04a1286e5f824f74372fc1271a1b97e091f00dcbf048f805d5f8247c02b6fc123e013b7e091f008fbf04a6502f5f82532816efc129940a37e094ca03ebf04a65019df824f7407afc1271a03d7e091f001ebf04ade0065f8252bc032fc128520197e0942500cbf04a0b8065f824f74032fc1271a0197e091f000cbf04a1e0f83f82433c23dfc1287811cfe094ca04b7f04a1e0083f82518117ff2128c48bfdd099981f0be84c910f85f4262507c2fa12fda3e17d097d31f0be84a320f85f424e6c7c2fa127083e17d0933d1f0be849628f85f424a8c7c2fa1246e3e17d091f018abe848f80bddf4247c02befa128c067ff309742010f984b23b22fac25185183d61258c2f3eb09582580ed84a3123076c24e1ccfbb61246a3f9db09463460dd849c419f6ec25180368f61314ea737b0989d460bd84c961b3dec264f8b1af6131104717b09
  | _ => 0
def ns2_Data1_ : Nat → Nat
  | 0 => 0x46145ef704a651b4fb825914b0fdc126cc4cbee094ca04ef704a65021fb8253280e7dc128c2019ee09581580ef04a66a65778248d47efbc126d42f3de094ce4cadf049b30c1ef8250f07c0fc1299e9957e098b73ddbf049ef1eedf8252bceb2fc1282e7597e098e338dbf049d71c6df8274687c2fc1389a3e17e09b2c1f0bf04d790f85f826b747c2fc1359a3e17e09a991f0bf04d000f85f8267287c2fc133763e17e099a01f0bf04c908f85f825fb07c2fc12d6e3e17e096b51f0bf04af98f85f82571c7c2fc12b143e17e094b91f0bf04a428f85f8250f07c2fc127583e17e093a91f0bf049cd0f85f824e0c7c2fc126403e17e093091f0bf0497d8f85f824b0c7c2fc125263e17e092831f0bf049278f85f8248d87c2fc124203e17e091fb1f0bf048f98f85f825328792fc123e036d7e091f0188bf048f80b85f8247c0592fc1295e1b97e09
  | 1 => 0x33c00e3fc50f40071fe28368038ff1419c01c7f8a33c00d3fc50f40069fe28368034ff1419c01a7f8a05e00d3fc519e0061fe287a0030ff141b40187f8a0ce00c3fc519e0059fe287a002cff141b40167f8a0ce00b3fc502f0059fe28e3407af4328783e07e194600da3d8cc4a8f81dc64ec007ad5328be8bdfc094ca17bfe04a2f8067f024e3407af412c1ac19fa098914cbfd04a65a657e8252111f7f4131388c1fa0946045efd04a4da25fe824facfabf4126cc2fbfa09367179fd04e3a00f7e82714c07bf41367803dfa0960c01efd04ad580f7e82526c07bf41290803dfa0946001efd04a2700f7e824fa807bf41278803dfa0938d01efd04e108087e827044043f41381a021fa09b51010fd04ba08087e825834043f412b74021fa094cb010fd04a3e8087e82512c043f4127ee021fa093eb010fd0480f0087e825180033f412998995f609
  | 2 => 0xce01b3fc502f00d9fe28cf0068ff143d00347f8a0da01a3fc506700d1fe28178068ff156000327f8a33c0193fc516d00c9fe28888064ff143d00327f8a1610193fc50ad00c9fe28368064ff1419c0327f8a09a0193fc502f00c9fe28cf0060ff143d00307f8a0da0183fc506700c1fe28cf005cff143d002e7f8a0da0173fc506700b9fe2817805cff1467802c7f8a1e80163fc506d00b1fe28338058ff1467802a7f8a1e80153fc506d00a9fe28338054ff140bc02a7f8a33c0143fc50f400a1fe28368050ff1419c0287f8a33c0133fc50f40099fe2836804cff1419c0267f8a05e0133fc519e0091fe287a0048ff141b40247f8a0ce0123fc519e0089fe287a0044ff141b40227f8a0ce0113fc502f0089fe290f8040ff146780207f8a1e80103fc506d0081fe28338040ff1467801e7f8a1e800f3fc506d0079fe2833803cff140bc01e7f8a
  | 3 => 0x3a60283fc51c60141fe28cf00a0ff143d00507f8a0da0283fc50670141fe2a8e409cff1467804e7f8a1e80273fc506d0139fe2833809cff140bc04e7f8a33c0263fc50f40131fe28368098ff1419c04c7f8a33c0253fc50f40129fe28368094ff1419c04a7f8a05e0253fc519e0121fe287a0090ff141b40487f8a0ce0243fc519e0119fe287a008cff141b40467f8a0ce0233fc502f0119fe28cf0088ff143d00447f8a0da0223fc50670111fe28cf0084ff143d00427f8a0da0213fc50670109fe28178084ff146780407f8a1e80203fc506d0101fe28338080ff1467803e7f8a1e801f3fc506d00f9fe2833807cff140bc03e7f8a33c01e3fc50f400f1fe28368078ff1419c03c7f8a33c01d3fc50f400e9fe28368074ff1419c03a7f8a05e01d3fc519e00e1fe287a0070ff141b40387f8a0ce01c3fc519e00d9fe287a006cff141b40367f8a
  | 4 => 0x2040333fc50f88199fe287a00ccff1437c0667f8a1920333fc50ae0199fe285080ccff141b40667f8a0ce0333fc505c0199fe281780ccff140960667f8a33c0323fc50f40191fe283680c8ff1419c0647f8a05e0323fc529d0189fe28cf00c4ff143d00627f8a0da0313fc50670189fe297100c0ff146780607f8a1e80303fc506d0181fe283380c0ff1467805e7f8a1e802f3fc506d0179fe283380bcff14f0e05c7f8a66902e3fc526a8171fe28cf00b8ff143d005c7f8a0da02e3fc50670171fe2916c0b4ff1467805a7f8a1e802d3fc506d0169fe283380b4ff147480587f8a33c02c3fc50f40161fe283680b0ff1419c0587f8a33c02b3fc50f40159fe283680acff1419c0567f8a71f02a3fc52788151fe291100a8ff146780547f8a1e802a3fc506d0151fe283380a8ff146780527f8a1e80293fc506d0149fe283380a4ff14bfe0507f8a
  | 5 => 0x59003c3fc519e01e1fe287a00f0ff141b40787f8a0ce03c3fc519e01d9fe287a00ecff141b40767f8a0ce03b3fc519e01d1fe287a00e8ff141b40747f8a0ce03a3fc519e01c9fe287a00e4ff141b40727f8a0ce0393fc529501c1fe28cf00e0ff143d00707f8a0da0383fc506701c1fe28cf00dcff143d006e7f8a0da0373fc506701b9fe297340d8ff1467806c7f8a1e80363fc506d01b1fe283380d8ff1467806a7f8a2f10353fc50f401a9fe2866c0d4ff141b406a7f8a0ce0353fc502f01a9fe28cf00d0ff143d00687f8a0da0343fc506701a1fe281780d0ff1576e0667f8aada0333fc552c0199fe2a8e40ccff1506c0667f8a7f20333fc53340199fe297280ccff14b360667f8a53a0333fc522d8199fe291040ccff147040667f8a37a0333fc51af8199fe28cf00ccff1464c0667f8a2ca0333fc511e8199fe288a40ccff1441e0667f8a
  | 6 => 0xce0443fc519e0219fe287a010cff141b40867f8a0ce0433fc53500211fe2951c108ff146780847f8a1e80423fc506d0211fe28338108ff146780827f8a2da0413fc51110209fe287a0104ff142c20827f8a15a0413fc506d0209fe28338104ff140bc0827f8a33c0403fc50f40201fe28368100ff1419c0807f8a05e0403fc519e01f9fe287a00fcff141b407e7f8a0ce03f3fc502f01f9fe2ab680f8ff154b007c7f8aa3903e3fc534b81f1fe2963c0f8ff1487c07c7f8a3a003e3fc51c101f1fe28de80f8ff146be07c7f8a33c03e3fc519301f1fe28b280f8ff1447a07c7f8a22903e3fc510781f1fe288100f8ff143e207c7f8a1e803e3fc50df01f1fe286480f8ff142b807c7f8a14203e3fc506d01f1fe283380f8ff1417007c7f8a05e03e3fc502581f1fe28cf00f4ff143d007a7f8a0da03d3fc506701e9fe298800f0ff14c320787f8a
  | 7 => 0x23c04b3fc51110259fe2880c12cff143f20967f8a1f404b3fc50f80259fe287a012cff143c00967f8a1dc04b3fc50de8259fe2866c12cff143220967f8a16104b3fc50ad0259fe284b012cff1423a0967f8a11004b3fc50820259fe2839c12cff141b40967f8a0ce04b3fc50630259fe282dc12cff141340967f8a06c04b3fc502f0259fe2816c12cff146780947f8a1e804a3fc506d0251fe28338128ff140bc0947f8a37a0493fc519e0249fe287a0124ff141b40927f8a0ce0493fc502f0249fe28cf0120ff143d00907f8a0da0483fc50670241fe28178120ff1467808e7f8a1e80473fc506d0239fe2833811cff148da08c7f8a44d0463fc51fe8231fe28cf0118ff143d008c7f8a0da0463fc50670231fe28cf0114ff143d008a7f8a0da0453fc50670229fe29cd8110ff14c700887f8a4950443fc519e0221fe287a0110ff141b40887f8a
  | 8 => 0x1e80513fc50df0289fe28648144ff142840a27f8a0da0513fc50670289fe282e0144ff140bc0a27f8a33c0503fc50f40281fe28368140ff1419c0a07f8a05e0503fc530a8279fe28cf013cff143d009e7f8a0da04f3fc50670279fe299b0138ff14a1409c7f8a3fa04e3fc519e0271fe287a0138ff141b409c7f8a0ce04e3fc519e0269fe287a0134ff141b409a7f8a0ce04d3fc52720261fe28cf0130ff143d00987f8a0da04c3fc50670261fe2af7c12cff156000967f8aaea04b3fc55488259fe2a9ec12cff14dfc0967f8a62404b3fc53098259fe2972812cff14b4a0967f8a4ed04b3fc526c8259fe2922412cff1485e0967f8a3d104b3fc51e50259fe28f2412cff147020967f8a33c04b3fc51998259fe28c5812cff146000967f8a2f804b3fc51788259fe28ba412cff145c40967f8a2da04b3fc51648259fe28a8412cff144be0967f8a
  | 9 => 0xda05a3fc506702d1fe28178168ff146780b27f8a2220593fc50f402c9fe28568164ff141b40b27f8a0ce0593fc502f02c9fe28cf0160ff143d00b07f8a0da0583fc506702c1fe28178160ff146780ae7f8a2290573fc50f402b9fe2857015cff141b40ae7f8a0ce0573fc502f02b9fe28cf0158ff143d00ac7f8a0da0563fc506702b1fe28178158ff146780aa7f8a1e80553fc506d02a9fe28338154ff14bee0a87f8a33c0543fc50f402a1fe28368150ff1419c0a87f8a33c0533fc516d0299fe287a014cff142c20a67f8a0da0533fc50670299fe2817814cff146780a47f8a1e80523fc506d0291fe28338148ff140bc0a47f8abea0513fc551c8289fe29f44144ff14c2a0a27f8a5dd0513fc522d8289fe28fd8144ff147040a27f8a37a0513fc51af8289fe28cf0144ff145940a27f8a23d0513fc51148289fe28810144ff143e20a27f8a
  | 10 => 0x6f05e3fc503702f1fe281b4178ff140d80bc7f8a06b05e3fc503502f1fe281a4178ff140d00bc7f8a06705e3fc503302f1fe28194178ff140c80bc7f8a06305e3fc503102f1fe28184178ff140c00bc7f8a05f05e3fc519e02e9fe2897c174ff143d00ba7f8a19b05d3fc50ae82e9fe28368174ff1419c0ba7f8a05e05d3fc519e02e1fe287a0170ff141b40b87f8a0ce05c3fc502f02e1fe2b26c16cff155b40b67f8aa5805b3fc551c82d9fe2a18016cff14cde0b67f8a65005b3fc530a82d9fe296a016cff14b2a0b67f8a53a05b3fc526c82d9fe28e0816cff146f40b67f8a35f05b3fc519e02d9fe28c9816cff145940b67f8a23d05b3fc511482d9fe2883c16cff144080b67f8a1f105b3fc50f402d9fe286f816cff143240b67f8a15c05b3fc50a102d9fe2836816cff1419c0b67f8a0b805b3fc502f02d9fe28cf0168ff143d00b47f8a
  | 11 => 0xaf05e3fc505702f1fe282b4178ff141580bc7f8a0ab05e3fc505502f1fe282a4178ff141500bc7f8a0a705e3fc505302f1fe28294178ff141480bc7f8a0a305e3fc505102f1fe28284178ff141400bc7f8a09f05e3fc504f02f1fe28274178ff141380bc7f8a09b05e3fc504d02f1fe28264178ff141300bc7f8a09705e3fc504b02f1fe28254178ff141280bc7f8a09305e3fc504902f1fe28244178ff141200bc7f8a08f05e3fc504702f1fe28234178ff141180bc7f8a08b05e3fc504502f1fe28224178ff141100bc7f8a08705e3fc504302f1fe28214178ff141080bc7f8a08305e3fc504102f1fe28204178ff141000bc7f8a07f05e3fc503f02f1fe281f4178ff140f80bc7f8a07b05e3fc503d02f1fe281e4178ff140f00bc7f8a07705e3fc503b02f1fe281d4178ff140e80bc7f8a07305e3fc503902f1fe281c4178ff140e00bc7f8a
  | 12 => 0xef05e3fc507702f1fe283b4178ff141d80bc7f8a0eb05e3fc507502f1fe283a4178ff141d00bc7f8a0e705e3fc507302f1fe28394178ff141c80bc7f8a0e305e3fc507102f1fe28384178ff141c00bc7f8a0df05e3fc506f02f1fe28374178ff141b80bc7f8a0db05e3fc506d02f1fe28364178ff141b00bc7f8a0d705e3fc506b02f1fe28354178ff141a80bc7f8a0d305e3fc506902f1fe28344178ff141a00bc7f8a0cf05e3fc506702f1fe28334178ff141980bc7f8a0cb05e3fc506502f1fe28324178ff141900bc7f8a0c705e3fc506302f1fe28314178ff141880bc7f8a0c305e3fc506102f1fe28304178ff141800bc7f8a0bf05e3fc505f02f1fe282f4178ff141780bc7f8a0bb05e3fc505d02f1fe282e4178ff141700bc7f8a0b705e3fc505b02f1fe282d4178ff141680bc7f8a0b305e3fc505902f1fe282c4178ff141600bc7f8a
  | 13 => 0x12f05e3fc509702f1fe284b4178ff142580bc7f8a12b05e3fc509502f1fe284a4178ff142500bc7f8a12705e3fc509302f1fe28494178ff142480bc7f8a12305e3fc509102f1fe28484178ff142400bc7f8a11f05e3fc508f02f1fe28474178ff142380bc7f8a11b05e3fc508d02f1fe28464178ff142300bc7f8a11705e3fc508b02f1fe28454178ff142280bc7f8a11305e3fc508902f1fe28444178ff142200bc7f8a10f05e3fc508702f1fe28434178ff142180bc7f8a10b05e3fc508502f1fe28424178ff142100bc7f8a10705e3fc508302f1fe28414178ff142080bc7f8a10305e3fc508102f1fe28404178ff142000bc7f8a0ff05e3fc507f02f1fe283f4178ff141f80bc7f8a0fb05e3fc507d02f1fe283e4178ff141f00bc7f8a0f705e3fc507b02f1fe283d4178ff141e80bc7f8a0f305e3fc507902f1fe283c4178ff141e00bc7f8a
  | 14 => 0x16f05e3fc50b702f1fe285b4178ff142d80bc7f8a16b05e3fc50b502f1fe285a4178ff142d00bc7f8a16705e3fc50b302f1fe28594178ff142c80bc7f8a16305e3fc50b102f1fe28584178ff142c00bc7f8a15f05e3fc50af02f1fe28574178ff142b80bc7f8a15b05e3fc50ad02f1fe28564178ff142b00bc7f8a15705e3fc50ab02f1fe28554178ff142a80bc7f8a15305e3fc50a902f1fe28544178ff142a00bc7f8a14f05e3fc50a702f1fe28534178ff142980bc7f8a14b05e3fc50a502f1fe28524178ff142900bc7f8a14705e3fc50a302f1fe28514178ff142880bc7f8a14305e3fc50a102f1fe28504178ff142800bc7f8a13f05e3fc509f02f1fe284f4178ff142780bc7f8a13b05e3fc509d02f1fe284e4178ff142700bc7f8a13705e3fc509b02f1fe284d4178ff142680bc7f8a13305e3fc509902f1fe284c4178ff142600bc7f8a
  | 15 => 0x1af05e3fc50d702f1fe286b4178ff143580bc7f8a1ab05e3fc50d502f1fe286a4178ff143500bc7f8a1a705e3fc50d302f1fe28694178ff143480bc7f8a1a305e3fc50d102f1fe28684178ff143400bc7f8a19f05e3fc50cf02f1fe28674178ff143380bc7f8a19b05e3fc50cd02f1fe28664178ff143300bc7f8a19705e3fc50cb02f1fe28654178ff143280bc7f8a19305e3fc50c902f1fe28644178ff143200bc7f8a18f05e3fc50c702f1fe28634178ff143180bc7f8a18b05e3fc50c502f1fe28624178ff143100bc7f8a18705e3fc50c302f1fe28614178ff143080bc7f8a18305e3fc50c102f1fe28604178ff143000bc7f8a17f05e3fc50bf02f1fe285f4178ff142f80bc7f8a17b05e3fc50bd02f1fe285e4178ff142f00bc7f8a17705e3fc50bb02f1fe285d4178ff142e80bc7f8a17305e3fc50b902f1fe285c4178ff142e00bc7f8a
  | 16 => 0x1ef05e3fc50f702f1fe287b4178ff143d80bc7f8a1eb05e3fc50f502f1fe287a4178ff143d00bc7f8a1e705e3fc50f302f1fe28794178ff143c80bc7f8a1e305e3fc50f102f1fe28784178ff143c00bc7f8a1df05e3fc50ef02f1fe28774178ff143b80bc7f8a1db05e3fc50ed02f1fe28764178ff143b00bc7f8a1d705e3fc50eb02f1fe28754178ff143a80bc7f8a1d305e3fc50e902f1fe28744178ff143a00bc7f8a1cf05e3fc50e702f1fe28734178ff143980bc7f8a1cb05e3fc50e502f1fe28724178ff143900bc7f8a1c705e3fc50e302f1fe28714178ff143880bc7f8a1c305e3fc50e102f1fe28704178ff143800bc7f8a1bf05e3fc50df02f1fe286f4178ff143780bc7f8a1bb05e3fc50dd02f1fe286e4178ff143700bc7f8a1b705e3fc50db02f1fe286d4178ff143680bc7f8a1b305e3fc50d902f1fe286c4178ff143600bc7f8a
  | 17 => 0x22f05e3fc511702f1fe288b4178ff144580bc7f8a22b05e3fc511502f1fe288a4178ff144500bc7f8a22705e3fc511302f1fe28894178ff144480bc7f8a22305e3fc511102f1fe28884178ff144400bc7f8a21f05e3fc510f02f1fe28874178ff144380bc7f8a21b05e3fc510d02f1fe28864178ff144300bc7f8a21705e3fc510b02f1fe28854178ff144280bc7f8a21305e3fc510902f1fe28844178ff144200bc7f8a20f05e3fc510702f1fe28834178ff144180bc7f8a20b05e3fc510502f1fe28824178ff144100bc7f8a20705e3fc510302f1fe28814178ff144080bc7f8a20305e3fc510102f1fe28804178ff144000bc7f8a1ff05e3fc50ff02f1fe287f4178ff143f80bc7f8a1fb05e3fc50fd02f1fe287e4178ff143f00bc7f8a1f705e3fc50fb02f1fe287d4178ff143e80bc7f8a1f305e3fc50f902f1fe287c4178ff143e00bc7f8a
  | 18 => 0x26f05e3fc513702f1fe289b4178ff144d80bc7f8a26b05e3fc513502f1fe289a4178ff144d00bc7f8a26705e3fc513302f1fe28994178ff144c80bc7f8a26305e3fc513102f1fe28984178ff144c00bc7f8a25f05e3fc512f02f1fe28974178ff144b80bc7f8a25b05e3fc512d02f1fe28964178ff144b00bc7f8a25705e3fc512b02f1fe28954178ff144a80bc7f8a25305e3fc512902f1fe28944178ff144a00bc7f8a24f05e3fc512702f1fe28934178ff144980bc7f8a24b05e3fc512502f1fe28924178ff144900bc7f8a24705e3fc512302f1fe28914178ff144880bc7f8a24305e3fc512102f1fe28904178ff144800bc7f8a23f05e3fc511f02f1fe288f4178ff144780bc7f8a23b05e3fc511d02f1fe288e4178ff144700bc7f8a23705e3fc511b02f1fe288d4178ff144680bc7f8a23305e3fc511902f1fe288c4178ff144600bc7f8a
  | 19 => 0x2af05e3fc515702f1fe28ab4178ff145580bc7f8a2ab05e3fc515502f1fe28aa4178ff145500bc7f8a2a705e3fc515302f1fe28a94178ff145480bc7f8a2a305e3fc515102f1fe28a84178ff145400bc7f8a29f05e3fc514f02f1fe28a74178ff145380bc7f8a29b05e3fc514d02f1fe28a64178ff145300bc7f8a29705e3fc514b02f1fe28a54178ff145280bc7f8a29305e3fc514902f1fe28a44178ff145200bc7f8a28f05e3fc514702f1fe28a34178ff145180bc7f8a28b05e3fc514502f1fe28a24178ff145100bc7f8a28705e3fc514302f1fe28a14178ff145080bc7f8a28305e3fc514102f1fe28a04178ff145000bc7f8a27f05e3fc513f02f1fe289f4178ff144f80bc7f8a27b05e3fc513d02f1fe289e4178ff144f00bc7f8a27705e3fc513b02f1fe289d4178ff144e80bc7f8a27305e3fc513902f1fe289c4178ff144e00bc7f8a
  | 20 => 0x2ef05e3fc517702f1fe28bb4178ff145d80bc7f8a2eb05e3fc517502f1fe28ba4178ff145d00bc7f8a2e705e3fc517302f1fe28b94178ff145c80bc7f8a2e305e3fc517102f1fe28b84178ff145c00bc7f8a2df05e3fc516f02f1fe28b74178ff145b80bc7f8a2db05e3fc516d02f1fe28b64178ff145b00bc7f8a2d705e3fc516b02f1fe28b54178ff145a80bc7f8a2d305e3fc516902f1fe28b44178ff145a00bc7f8a2cf05e3fc516702f1fe28b34178ff145980bc7f8a2cb05e3fc516502f1fe28b24178ff145900bc7f8a2c705e3fc516302f1fe28b14178ff145880bc7f8a2c305e3fc516102f1fe28b04178ff145800bc7f8a2bf05e3fc515f02f1fe28af4178ff145780bc7f8a2bb05e3fc515d02f1fe28ae4178ff145700bc7f8a2b705e3fc515b02f1fe28ad4178ff145680bc7f8a2b305e3fc515902f1fe28ac4178ff145600bc7f8a
  | 21 => 0x32f05e3fc519702f1fe28cb4178ff146580bc7f8a32b05e3fc519502f1fe28ca4178ff146500bc7f8a32705e3fc519302f1fe28c94178ff146480bc7f8a32305e3fc519102f1fe28c84178ff146400bc7f8a31f05e3fc518f02f1fe28c74178ff146380bc7f8a31b05e3fc518d02f1fe28c64178ff146300bc7f8a31705e3fc518b02f1fe28c54178ff146280bc7f8a31305e3fc518902f1fe28c44178ff146200bc7f8a30f05e3fc518702f1fe28c34178ff146180bc7f8a30b05e3fc518502f1fe28c24178ff146100bc7f8a30705e3fc518302f1fe28c14178ff146080bc7f8a30305e3fc518102f1fe28c04178ff146000bc7f8a2ff05e3fc517f02f1fe28bf4178ff145f80bc7f8a2fb05e3fc517d02f1fe28be4178ff145f00bc7f8a2f705e3fc517b02f1fe28bd4178ff145e80bc7f8a2f305e3fc517902f1fe28bc4178ff145e00bc7f8a
  | 22 => 0x36f05e3fc51b702f1fe28db4178ff146d80bc7f8a36b05e3fc51b502f1fe28da4178ff146d00bc7f8a36705e3fc51b302f1fe28d94178ff146c80bc7f8a36305e3fc51b102f1fe28d84178ff146c00bc7f8a35f05e3fc51af02f1fe28d74178ff146b80bc7f8a35b05e3fc51ad02f1fe28d64178ff146b00bc7f8a35705e3fc51ab02f1fe28d54178ff146a80bc7f8a35305e3fc51a902f1fe28d44178ff146a00bc7f8a34f05e3fc51a702f1fe28d34178ff146980bc7f8a34b05e3fc51a502f1fe28d24178ff146900bc7f8a34705e3fc51a302f1fe28d14178ff146880bc7f8a34305e3fc51a102f1fe28d04178ff146800bc7f8a33f05e3fc519f02f1fe28cf4178ff146780bc7f8a33b05e3fc519d02f1fe28ce4178ff146700bc7f8a33705e3fc519b02f1fe28cd4178ff146680bc7f8a33305e3fc519902f1fe28cc4178ff146600bc7f8a
  | 23 => 0x43305e3fc521902f1fe290b4178ff148580bc7f8a42805e3fc520b02f1fe29038178ff147fa0bc7f8a3fc05e3fc51fd82f1fe28fe8178ff147f20bc7f8a3f805e3fc51fa82f1fe28fd0178ff147e60bc7f8a3f205e3fc51f882f1fe28fc0178ff147de0bc7f8a3ee05e3fc51f682f1fe28f70178ff147b60bc7f8a3da05e3fc51ec82f1fe28f60178ff147ae0bc7f8a3d605e3fc51ea82f1fe28f50178ff147a60bc7f8a3d205e3fc51dc82f1fe28ee0178ff1476e0bc7f8a3b605e3fc51d582f1fe28e7c178ff147100bc7f8a38705e3fc51c302f1fe28e14178ff147080bc7f8a38305e3fc51c102f1fe28e04178ff147000bc7f8a37f05e3fc51bf02f1fe28df4178ff146f80bc7f8a37b05e3fc51bd02f1fe28de4178ff146f00bc7f8a37705e3fc51bb02f1fe28dd4178ff146e80bc7f8a37305e3fc51b902f1fe28dc4178ff146e00bc7f8a
  | 24 => 0x59005e3fc52be02f1fe295b4178ff14ace0bc7f8a55b05e3fc52ad02f1fe29564178ff14ab00bc7f8a55705e3fc52ab02f1fe294d4178ff14a600bc7f8a52c05e3fc528b82f1fe292dc178ff1495a0bc7f8a4ac05e3fc525582f1fe292a8178ff149520bc7f8a4a805e3fc525382f1fe29294178ff149320bc7f8a49005e3fc524782f1fe29238178ff1491a0bc7f8a48c05e3fc524582f1fe29228178ff148f20bc7f8a47505e3fc523a02f1fe291cc178ff148e40bc7f8a47105e3fc523802f1fe291bc178ff148dc0bc7f8a46905e3fc523402f1fe2919c178ff148cc0bc7f8a46505e3fc523202f1fe29170178ff148ae0bc7f8a45605e3fc522a82f1fe29150178ff148a60bc7f8a45205e3fc522882f1fe29110178ff1487c0bc7f8a43b05e3fc521d02f1fe290e4178ff148700bc7f8a43705e3fc521b02f1fe290d4178ff148680bc7f8a
  | 25 => 0xa3a05e3fc551c82f1fe2a8e0178ff1546e0bc7f8aa3605e3fc551a82f1fe2a8d0178ff154660bc7f8aa3205e3fc551882f1fe2a8c0178ff1545e0bc7f8aa2e05e3fc551682f1fe2a8b0178ff154560bc7f8aa2a05e3fc551482f1fe2a8a0178ff1544e0bc7f8aa2605e3fc551282f1fe2a890178ff154460bc7f8aa2205e3fc551082f1fe2a880178ff1543e0bc7f8aa1e05e3fc550e82f1fe2a870178ff154360bc7f8aa1a05e3fc550c82f1fe29fcc178ff14f0e0bc7f8a76e05e3fc535682f1fe29ab0178ff14d560bc7f8a6aa05e3fc535482f1fe29a94178ff14d480bc7f8a6a305e3fc535102f1fe29a84178ff14d300bc7f8a68c05e3fc534082f1fe2993c178ff14c700bc7f8a63605e3fc531a82f1fe298d0178ff14c660bc7f8a63205e3fc531882f1fe298c0178ff14bfe0bc7f8a5f205e3fc52f882f1fe296a8178ff14b520bc7f8a
  | 26 => 0xa7a05e3fc553c82f1fe2a9e0178ff154ee0bc7f8aa7605e3fc553a82f1fe2a9d0178ff154e60bc7f8aa7205e3fc553882f1fe2a9c0178ff154de0bc7f8aa6e05e3fc553682f1fe2a9b0178ff154d60bc7f8aa6a05e3fc553482f1fe2a9a0178ff154ce0bc7f8aa6605e3fc553282f1fe2a990178ff154c60bc7f8aa6205e3fc553082f1fe2a980178ff154be0bc7f8aa5e05e3fc552e82f1fe2a970178ff154b60bc7f8aa5a05e3fc552c82f1fe2a960178ff154ae0bc7f8aa5605e3fc552a82f1fe2a950178ff154a60bc7f8aa5205e3fc552882f1fe2a940178ff1549e0bc7f8aa4e05e3fc552682f1fe2a930178ff154960bc7f8aa4a05e3fc552482f1fe2a920178ff1548e0bc7f8aa4605e3fc552282f1fe2a910178ff154860bc7f8aa4205e3fc552082f1fe2a900178ff1547e0bc7f8aa3e05e3fc551e82f1fe2a8f0178ff154760bc7f8a
  | 27 => 0xaba05e3fc555c82f1fe2aae0178ff1556e0bc7f8aab605e3fc555a82f1fe2aad0178ff155660bc7f8aab205e3fc555882f1fe2aac0178ff1555e0bc7f8aaae05e3fc555682f1fe2aab0178ff155560bc7f8aaaa05e3fc555482f1fe2aaa0178ff1554e0bc7f8aaa605e3fc555282f1fe2aa90178ff155460bc7f8aaa205e3fc555082f1fe2aa80178ff1553e0bc7f8aa9e05e3fc554e82f1fe2aa70178ff155360bc7f8aa9a05e3fc554c82f1fe2aa60178ff1552e0bc7f8aa9605e3fc554a82f1fe2aa50178ff155260bc7f8aa9205e3fc554882f1fe2aa40178ff1551e0bc7f8aa8e05e3fc554682f1fe2aa30178ff155160bc7f8aa8a05e3fc554482f1fe2aa20178ff1550e0bc7f8aa8605e3fc554282f1fe2aa10178ff155060bc7f8aa8205e3fc554082f1fe2aa00178ff154fe0bc7f8aa7e05e3fc553e82f1fe2a9f0178ff154f60bc7f8a
  | 28 => 0xafa05e3fc557c82f1fe2abe0178ff155ee0bc7f8aaf605e3fc557a82f1fe2abd0178ff155e60bc7f8aaf205e3fc557882f1fe2abc0178ff155de0bc7f8aaee05e3fc557682f1fe2abb0178ff155d60bc7f8aaea05e3fc557482f1fe2aba0178ff155ce0bc7f8aae605e3fc557282f1fe2ab90178ff155c60bc7f8aae205e3fc557082f1fe2ab80178ff155be0bc7f8aade05e3fc556e82f1fe2ab70178ff155b60bc7f8aada05e3fc556c82f1fe2ab60178ff155ae0bc7f8aad605e3fc556a82f1fe2ab50178ff155a60bc7f8aad205e3fc556882f1fe2ab40178ff1559e0bc7f8aace05e3fc556682f1fe2ab30178ff155960bc7f8aaca05e3fc556482f1fe2ab20178ff1558e0bc7f8aac605e3fc556282f1fe2ab10178ff155860bc7f8aac205e3fc556082f1fe2ab00178ff1557e0bc7f8aabe05e3fc555e82f1fe2aaf0178ff155760bc7f8a
  | 29 => 0xbad05e3fc55d602f1fe2aeac178ff157200bc7f8ab8305e3fc55c102f1fe2adf0178ff156f60bc7f8ab7a05e3fc55bc82f1fe2ade0178ff156ee0bc7f8ab7605e3fc55ba82f1fe2add0178ff156e60bc7f8ab7205e3fc55b882f1fe2adc0178ff156d80bc7f8ab6605e3fc55b282f1fe2aca0178ff1564e0bc7f8ab2205e3fc559082f1fe2ac80178ff1563e0bc7f8ab1e05e3fc558e82f1fe2ac70178ff156360bc7f8ab1a05e3fc558c82f1fe2ac60178ff1562e0bc7f8ab1605e3fc558a82f1fe2ac50178ff156260bc7f8ab1205e3fc558882f1fe2ac40178ff1561e0bc7f8ab0e05e3fc558682f1fe2ac30178ff156160bc7f8ab0a05e3fc558482f1fe2ac20178ff1560e0bc7f8ab0605e3fc558282f1fe2ac10178ff156060bc7f8ab0205e3fc558082f1fe2ac00178ff155fe0bc7f8aafe05e3fc557e82f1fe2abf0178ff155f60bc7f8a
  | 30 => 0xda0d53fc506d06a1fe2836834cff141b41a47f8a0da0d13fc506d0681fe2836833cff1577c19c7f8aa810ce3fc55110671fe2a884338ff1544019c7f8aa1f0ce3fc550f0671fe2a874338ff1543819c7f8aa1b0ce3fc550d0671fe2a864338ff14b2e19c7f8a5960ce3fc52ca8671fe29650338ff14b2619c7f8a55e0ce3fc529c0671fe294ac338ff1484e19c7f8a3b20ce3fc51710671fe28584338ff1419c19a7f8a0ce0cc3fc530a8659fe28cf032cff1419c1967f8a0ce0ca3fc50670649fe28338320ff1419c18e7f8a0ce0c63fc50670629fe28338310ff14c321707f8a6200b73fc505c05b9fe28570268ff1419c1187f8a0da07e3fc529d0361fe287a01b0ff1419c0d87f8acc305e3fc565382f1fe2b27c178ff159240bc7f8ac7805e3fc562e82f1fe2b154178ff1588a0bc7f8abe105e3fc55e282f1fe2af10178ff157740bc7f8a
  | 31 => 0x5551e83fc52110f41fe28f887a0ff143d03ce7f8a1e81e63fc50f40f29fe2916c790ff146783c87f8a1e81e43fc50f40f19fe287a0788ff143d03c27f8a1e81e03fc50f40ef9fe287a0778ff1474c37c7f8a38c1bd3fc50df0de9fe28cf06ccff1489a3247f8a46d1913fc50c90c89fe28cf0574ff142c22ba7f8a16115c3fc50af8ae1fe2858456cff143d02b47f8a15f15a3fc50ae0ad1fe2856c568ff146782707f8a1e812c3fc50f408f1fe28cf0444ff146782087f8ac160da3fc554106d1fe2a888368ff154421b47f8aa200da3fc550f86d1fe2a878368ff1543a1b47f8aa1c0da3fc550d86d1fe2a868368ff154321b47f8a3d10da3fc51e806d1fe28f3c368ff1479c1b47f8a3cd0da3fc51e606d1fe28f2c368ff147941b47f8a3c90da3fc51e406d1fe28d7c368ff142b81b47f8a0da0d93fc506d06c1fe2836835cff141b41ac7f8a
  | _ => 0
def ns2_Data2_ : Nat → Nat
  | 0 => 0xa2033c3fc550f99e1fe2a878cf0ff1543a6787f8aa1c33c3fc550d99e1fe2a868cf0ff154326787f8a3c333c3fc51e119e1fe28f04cf0ff147806787f8a3bf33c3fc51df19e1fe28ef4cf0ff147786787f8a3bb33c3fc51c719e1fe28cf0cecff146786747f8a33c3393fc519e19c1fe28cf0cdcff1467866c7f8a33c3353fc52e69931fe297dcc00ff147485f07f8a5c42e93fc52851651fe299b0b24ff145945927f8a4e42a13fc529514c1fe292548f4ff14e6c4787f8a23d23c3fc53501079fe2951c838ff14cd24087f8a4d52033fc51021019fe290f87c4ff1487c3e07f8a1f11f03fc55c58f41fe2a96c7a0ff154443d07f8aa211e83fc55100f41fe2a87c7a0ff1543c3d07f8aa1d1e83fc550e0f41fe2a86c7a0ff154343d07f8aa191e83fc52cf8f41fe296787a0ff14b3a3d07f8a59c1e83fc52cd8f41fe296687a0ff14b323d07f8a
  | 1 => 0x2a90519fc511d028cfe288081467f143780a33f8a1830519fc50fc823cfe291a41027f14fae07d3f8a58e03e9fc523481f4fe28e780fa7f1471007d3f8a36b03e9fc51a101f4fe28aa40fa7f1447407d3f8a20203e9fc50de01f4fe2860c0fa7f142c207b3f8a3880339fc51b5819cfe28d080ce7f145520673f8a23a0339fc5101019cfe286f00ce7f143060673f8a1f90319fc50fc8134fe285840627f147106bebf8a23d23a5fc51021012fe286f86f17f148d20bcbf8a38805e5fc51b582f2fe28d081797f145520bcbf8a23a05e5fc510102f2fe286f01797f143060bcbf8a46304b5fc51c4025afe28dac12d7f14684096bf8a2a904b5fc511d025afe2880812d7f14378096bf8a18304b5fc55af5751fe2ac02b68ff154734707f8ab5ea1c3fc538f9c11fe293c4e04ff147047027f8ab3733c3fc552199e1fe2a888cf0ff154426787f8a
  | 2 => 0xb505e6fc52d2025b7e2918812dbf1470e096df8a36a04b6fc51a0825b7e28b8412dbf14590096df8a2a804b6fc5125025b7e287e012dbf14376096df8a18f04b6fc50c0825b7e2830412dbf1416a096df8a3410356fc510200b37e291a41787f147100bc3f8a36b05e1fc51a102f0fe28aa41787f144740bc3f8a20205e1fc50de02f0fe2860c1787f1488c6d73f8a4e123a9fc511e11d4fe2935080a7f144064053f8a38b1bc9fc50de8de4fe2912460e7f146d62593f8a1831049fc523484d4fe291a417a7f147100bd3f8a36b05e9fc51a102f4fe28aa417a7f144740bd3f8a20205e9fc50de02f4fe2860c17a7f143f20bb3f8aad905b9fc51c402dcfe28dac16e7f146840b73f8a32c05b9fc519202dcfe28aa416e7f144740b73f8a20205b9fc50e902dcfe286f016e7f143060b73f8a09905b9fc51c4028cfe28dac1467f146840a33f8a
  | 3 => 0x2a8051afc5125028d7e287e0146bf143760a35f8a18f051afc50c0828d7e28304146bf1416a0a35f8a1f8049afc562781f57e29fc00fabf14fac07d5f8a58d03eafc525d01f57e2919c0fabf1473a07d5f8a38703eafc51b501f57e28d040fabf145c207d5f8a2c803eafc515401f57e289280fabf143f007d5f8a1bb03eafc50c781f57e286040fabf1418207d5f8a0b503eafc511e01dd7e29fc40cebf147c00675f8a387033afc51b5019d7e28d040cebf145c20675f8a2c8033afc5154019d7e289280cebf143f00675f8a1bb033afc50c7819d7e286040cebf141820675f8a0b5033afc51c39afb7e28b28b21bf14b0c494df8a1be1bb6fc50c90c7b7e282e02d5bf148ce0bcdf8a38705e6fc51b502f37e28d04179bf145c20bcdf8a2c805e6fc515402f37e28928179bf143f00bcdf8a1bb05e6fc50c782f37e28604179bf141820bcdf8a
  | 4 => 0x38705e2fc51b502f17e28d04178bf145c20bc5f8a2c805e2fc515402f17e28928178bf143f00bc5f8a1bb05e2fc50c782f17e28604178bf141820bc5f8a0b505e2fc5171170d7e28b24b22bf14b0a4955f8a3161f8afc50fc8fc57e287e07debf143f03ed5f8a1f81f4afc50fc0f857e28f80782bf1437a3775f8a19118fafc51b509657e28604412bf1476218d5f8a0b70b5afc523384d57e287e026abf148ce0bd5f8a38705eafc51b502f57e28d0417abf145c20bd5f8a2c805eafc515402f57e2892817abf143f00bd5f8a1bb05eafc50c782f57e2860417abf141820bd5f8a0b505eafc51d882dd7e28e1c16ebf146d40b75f8a34105bafc517082dd7e28b2016ebf145500b75f8a24a05bafc50fc02dd7e286ec16ebf1431e0b75f8a18105bafc506082dd7e282d416ebf1470e0a35f8a36a051afc51a0828d7e28b84146bf145900a35f8a
  | 5 => 0x15d014b7c50fb809dbe287dc04adf143ee0236f8a1f7010b7c50fb807dbe287dc03adf143ee01b6f8a1f700cb7c50fb805dbe28e08df9df1470c6beef8a2d82ca77c5165132bbe288f48e5df14408400ef8a1be1ba77c50c90c6bbe282e02cddf148cc0bcef8a38605e77c51bf02f3be28da4179df146800bcef8a2d805e77c515382f3be28994179df144720bcef8a20005e77c50fb82f3be286e8179df1431a0bcef8a0bf05e77c505982f3be28d00175df14c46096ef8a46104b77c51c3025bbe28df812ddf146d2096ef8a34004b77c516c025bbe28a9c12ddf144ca096ef8a23904b77c5100025bbe287dc12ddf14374096ef8a18d04b77c505f825bbe282cc12ddf14678072ef8a2ca01477c51c41c3e7e28dacdab3f146846839f8a2a92a8cfc52c212567e286f06ef3f143063039f8a23a03bcfc511d01767e288e80933f148ce0bc5f8a
  | 6 => 0xbf03eb7c505981f5be287dc0f6df143ee0796f8a1f703bb7c50fb81d5be28cf00e6df143ee0736f8a1e4039b7c50ae81cdbe284100e6df141960736f8a051039b7c50fb81c5be287dc0dedf143ee06d6f8a1f7035b7c50fb81a5be28f7c0cedf1470c0676f8a37e033b7c51b4819dbe28d000cedf145b00676f8a2a7033b7c5132819dbe288e40cedf144000676f8a1f7033b7c50dd019dbe286340cedf1417e0676f8a0b3033b7c50fb8195be287dc0c6df143ee0616f8a1f702fb7c50fb8175be287dc0b6df143ee0596f8a1f702bb7c50fb8155be287dc0a6df143ee0516f8a1f7027b7c50fb8135be287dc096df143ee0496f8a1f7023b7c50fb8115be287dc086df143ee0416f8a1f701fb7c50fb80f5be287dc076df143ee0396f8a1f701bb7c50fb80d5be287dc066df143ee0316f8a1f7017b7c50fb80b5be287dc056df143ee0296f8a
  | 7 => 0x1f7057b7c50fb82b5be287dc156df143ee0a96f8a1f7053b7c50fb8295be2ab8c146df155aa0a36f8a386051b7c51bf028dbe28da4146df146800a36f8a32a051b7c5191028dbe28b60146df1454e0a36f8a265051b7c511c828dbe28800146df143ee0a36f8a1ba051b7c50c6828dbe285a8146df1417e0a36f8a0b3051b7c504a828dbe287dc142df143ee09f6f8a1f704eb7c50fb826dbe287dc132df143ee0976f8a1f704ab7c50fb824dbe287dc122df143ee08f6f8a1f7046b7c50fb822dbe287dc112df143ee0876f8a1f7042b7c50fb820dbe29198102df143ee0816f8a1f703fb7c562701f5be29fbc0fadf14faa07d6f8a58c03eb7c523301f5be28ea80fadf1473807d6f8a38603eb7c51bf01f5be28da40fadf1468007d6f8a2d803eb7c515381f5be289940fadf1447207d6f8a20003eb7c50fb81f5be286e80fadf1431a07d6f8a
  | 8 => 0x3ad1f7b7c519b8fbdbe287e47dedf143f03ef6f8a1f71f6b7c50fb8fadbe287dc7d2df143ee3e76f8a1f71f2b7c50fb8f85be28f7c782df143ee3836f8a38a1bab7c50de8dd5be291b0636df1432231b6f8a1f716cb7c51b48965be287dc442df143ee20b6f8a1f70ecb7c51d80635be287dc30edf143ee16d6f8a4fd0b3b7c505b859dbe2919826adf143ee1356f8a46605eb7c51c302f5be28df817adf146d20bd6f8a34005eb7c516c02f5be28a9c17adf144ca0bd6f8a23905eb7c510002f5be287dc17adf143740bd6f8a18d05eb7c505f82f5be282cc17adf143ee0bb6f8a1f705cb7c524b02ddbe28ec016edf1470c0b76f8a37e05bb7c51b482ddbe28d0016edf145b00b76f8a2a705bb7c513282ddbe288e416edf144000b76f8a1f705bb7c50dd02ddbe2863416edf1417e0b76f8a0b305bb7c50fb82d5be287dc166df143ee0b16f8a
  | 9 => 0x200055e7c50c0821f3e28b200b79f14472049cf8a388386d7c51b59b4ebe28d08d035f1455254faf8a23a239d7c51011006be286f06eb5f144ca307af8a183043d7c50c181cebe29198178df1470c0bc6f8a37e05e37c51b482f1be28d00178df145b00bc6f8a2a705e37c513282f1be288e4178df144000bc6f8a1f705e37c50dd02f1be28634178df1417e0bc6f8a0b305e37c519e01c9be291e8dfadf147026fd6f8a5f8369b7c520316c5be28b68b62df1480c4cb6f8a4e6239b7c511e11cdbe2934c802df144064016f8ab911f7b7c55308fbdbe2a8887dedf154423ef6f8aa201f7b7c550f8fbdbe2a8787dedf1543a3ef6f8aa1c1f7b7c550d8fbdbe2a8687dedf154323ef6f8a4211f7b7c52100fbdbe2907c7dedf1483c3ef6f8a41d1f7b7c520e0fbdbe2906c7dedf148343ef6f8a4191f7b7c520c0fbdbe2905c7dedf1476a3ef6f8a
  | 10 => 0xb103ebbc51b4019dde28cfc0ceef1458e067778a2a6033bbc50ff019dde286e00ceef142fe067778a0b1033bbc550c99fbde29424b1def1459458ef78a5411fe7bc51020ff3de28e946e1ef1437c370f78a5c10b17bc505c058bde29194179ef146d00bcf78a33f05e7bc516382f3de28a98179ef143fc0bcf78a1b805e7bc50bf82f3de282c4179ef1467e0baf78aaf804b7bc554f825bde28da012def1467e096f78a2f504b7bc5163825bde28a9812def1452a096f78a25204b7bc510a025bde287f812def143ec096f78a1b804b7bc50d1025bde285fc12def142e6096f78a0be04b7bc5058825bde2828c12def1467e080f78a15c0377bc519f81abde28570049ef14096024f78a1f81f7a7c51c39c373e28da8da79f14682681cf8a2a82a7e7c5324932f3e2960c92b9f143f03efcf8a1bb1bae7c50c78c6f3e283042ff9f1416a167cf8a
  | 11 => 0x1bb1b8ebc50c08bff5e282d42c7af143fc0abd78a1fe016ebc51b59b46de28d08cff6f1455254db78a2021fedbc50de0dc6de2860c5ff6f148ca0bc778a36805e3bc519f82f1de28b1c178ef1454c0bc778a1fe05e3bc50dc02f1de285fc178ef141620bc778a2c92c7bbc51018ff5de286f46e2ef146d0259778a17f104bbc505b858dde2919426aef148ca0bd778a36805ebbc519f82f5de28b1c17aef1454c0bd778a1fe05ebbc50dc02f5de285fc17aef141620bd778a66e05bbbc51b402ddde28cfc16eef1458e0b7778a2a605bbbc50ff02ddde286e016eef142fe0b7778a0b105bbbc51b4028dde28cfc146ef1458e0a3778a2a6051bbc50ff028dde286e0146ef142fe0a3778a0b1051bbc53f701f5de29f500faef14b1607d778a46503ebbc51b401f5de28cfc0faef1458e07d778a2a603ebbc50ff01f5de286e00faef142fe07d778a
  | 12 => 0x1fc03ebdc50c581f5ee285f40faf7140c607d7b8a1e003cbdc506301ddee287800e6f7143c006f7b8a539033bdc51c2819dee28d9c0cef71467c0677b8a2c6033bdc5152019dee288e00cef7143f80677b8a18b033bdc50be819dee294e40c6f71418c0517b8a0c601ebdc51c29afbee28b28b19f71447a470fb8a2041fc7dc519f0f8bee2864862df71470a0bcfb8a36705e7dc519f02f3ee28b18179f7145480bcfb8a23805e7dc50fe02f3ee2862c179f7142fa0bcfb8a33e05d7dc5230025bee28e1412df7146ce096fb8a33e04b7dc5163025bee28a9012df714470096fb8a1fc04b7dc50c5825bee285f412df71467c06afb8a369368f3c51a019ff9e28a9ca9bcf14c904cbe78a2001fef3c50dd0dc79e282cc2c7cf1458e0a5e78a2c702df3c5163810f9e28b1c053cf146d46d1d78a34133febc5164163f5e28aa0a9baf144943fdd78a
  | 13 => 0x18317dddc51c282f1ee28d9c178f71467c0bc7b8a2c605e3dc515202f1ee288e0178f7143f80bc7b8a18b05e3dc50be82f1ee296ece16f714cea6cf7b8a69133ebdc53859635ee28b24b1af714a6c5497b8a60e238bdc511e11c5ee28fb07f2f7144063f97b8a64b18bbdc50c88c5dee2913c5f6f7146ce2597b8a17d104bdc529c8365ee28e1417af7146ce0bd7b8a33e05ebdc516302f5ee28a9017af7144700bd7b8a1fc05ebdc50c582f5ee285f417af714a720b77b8a38505bbdc51b382ddee28cf816ef71458c0b77b8a2a405bbdc511c02ddee287f016ef7143160b77b8a17d05bbdc51c2828dee28d9c146f71467c0a37b8a2c6051bdc5152028dee288e0146f7143f80a37b8a18b051bdc50be828dee2abd80faf7155a007d7b8a38503ebdc51b381f5ee28cf80faf71458c07d7b8a2ae03ebdc515201f5ee28a740faf71447007d7b8a
  | 14 => 0x91033bec50fa018df6287d00aefb142b40537d8a1f401cbec50ad0075f628e10d7dfb1459458afd8a23d2377ec50c90c53f6282e02bdfb148c80bcfd8a38405e7ec519e82f3f628b14179fb145460bcfd8a23705e7ec50c502f3f6285ec179fb1415e0bcfd8a45f04b7ec51c2025bf628cf412dfb1458a096fd8a2a304b7ec511b825bf62862812dfb142f6096fd8a0af04b7ec51b41b3fce28cfccfbe71458e58df38a2a62a4f9c50ff0fe7ce285fc5f7e71470c70beb8a369367f5c51a019f7ae28a9ca93d714c8e4cbeb8a239238f5c51000fe7ae2863462fd71458c0a5eb8a2c602df5c5163010fae28b18053d71470e70bdb8a36a367edc51a099f76e28b20b1bb714550549db8a58224aedc50c78c5f6e286045f7b7143f80abdb8a1fc044edc50fe00b76e28e20e1777146d66cfbb8a34233eddc51549526ee288e88e377144043f9bb8a
  | 15 => 0x17b05e3ec505782f1f628e24b16fb1459258b7d8a666237bec511e11bdf6291a862afb143223157d8a44717bbec50bd8825f62987c2befb1416e15f7d8a46409abec523202f5f628e1017afb1467a0bd7d8a2c505ebec515182f5f6288dc17afb143140bd7d8a17b05ebec505782f5f628e1016efb1467a0b77d8a2c505bbec515182ddf6288dc16efb143140b77d8a17b05bbec505782ddf628e10146fb1467a0a37d8a2c5051bec5151828df6288dc146fb143140a37d8a17b051bec5057828df629190102fb14fda07d7d8a7d303ebec523201f5f628e6c0fafb1470807d7d8a33d03ebec516281f5f628a8c0fafb1446e07d7d8a18a03ebec50bd81f5f6282bc0fafb143e806b7d8aacf033bec51c2019df628cf40cefb146500677d8a321033bec5162819df628a8c0cefb1446e0677d8a208033bec50c5019df6285ec0cefb1415e0677d8a
  | 16 => 0x20401e7f450df00f3fa28648079fd1417003cfe8a08f0197f4521e0083fa2ab68031fd154b0018fe8a43c00c7f451c10063fa28d7c031fd1464c018fe8a2ca00c7f4511e8063fa2883c031fd14408018fe8a1be00c7f450c90063fa282e0031fd14096018fe8a385384fcc519f19efe628b18b17f314548547f98a238237fcc50c58c57e6285f45eff31467e67bf58a2c72c5fac5153151fd6285fc5efeb1416215ff58a386384f6c51a019efb628a9ca8fdb14c8c4cbed8a239237f6c50c68c57b6282cc2bfdb142f609ded8a17b043f6c50bd81cfb628e1ce13bb1468267bdd8a2c82c5eec5154151f76289288dfbb1431e315dd8a18117beec505a857f76288dc0efbb1446e049dd8a388384dec51a119eef628aa4a8f7b1447446fbd8a18317bdec523202f1f628e10178fb1467a0bc7d8a2c505e3ec515182f1f6288dc178fb143140bc7d8a
  | 17 => 0xce00cbf450658065fa28318032fd1416e0197e8a09a00cbf450360065fa28178032fd140b60197e8a05100cbf450198065fa2abcab69fd147066befe8aa3a3097f4550c984bfa28b28b0dfd1447a46cfe8a2041fb7f4521e0f8bfa286f86d9fd14324310fe8a43c0dc7f4505c056bfa2abc8179fd147060bcfe8a30905e7f4517d82f3fa28b0c179fd145060bcfe8a23605e7f450fd82f3fa286d8179fd143100bcfe8a0ad05e7f4504782f3fa28c24175fd157fe096fe8aaf204b7f4522f025bfa28e0c12dfd14612096fe8a2fb04b7f45161825bfa28a0c12dfd1449e096fe8a23604b7f45108025bfa287ec12dfd143e6096fe8a1b604b7f450c4025bfa285c012dfd142c8096fe8a0ba04b7f45056825bfa2827412dfd1411e096fe8a3090407f4518481abfa290f0079fd1470403cfe8a35f01e7f4519e00f3fa28b28079fd1447a03cfe8a
  | 18 => 0x15a01ebf4509600f5fa2847407afd1422003d7e8a10401ebf4507380f5fa2836807afd1419c03d7e8a0cb01ebf4506300f5fa282dc07afd1413403d7e8a06c01ebf4502f00f5fa2816c07afd140a203d7e8a03e01ebf4501980f5fa2ac00032fd155d40197e8aab700cbf455488065fa2a9ec032fd154700197e8a4fc00cbf451c08065fa28cf0032fd1466e0197e8a33300cbf4518b0065fa28c00032fd145f00197e8a2f100cbf451748065fa28b88032fd145b40197e8a2c900cbf451508065fa28a60032fd144be0197e8a23c00cbf451110065fa28838032fd144060197e8a1f900cbf450fb8065fa287d0032fd143e00197e8a1e800cbf450f20065fa28780032fd143b80197e8a1bd00cbf450cd8065fa28644032fd142c20197e8a15d00cbf450ad0065fa284b0032fd1423a0197e8a11000cbf450820065fa2839c032fd141b40197e8a
  | 19 => 0x1b6033bf450c4019dfa285c00cefd142c80677e8a0dc033bf4505d019dfa282b40cefd1413a0677e8a08f033bf4560180f5fa2ac0007afd155d403d7e8aab701ebf4554880f5fa2a9ec07afd1547003d7e8a7bb01ebf4538e00f5fa29a2c07afd14c5a03d7e8a61101ebf452ed80f5fa296e007afd14b6e03d7e8a5b601ebf452bd80f5fa295c807afd14a9203d7e8a54001ebf4529080f5fa2945c07afd149f803d7e8a38101ebf4519e00f5fa28cdc07afd1466603d7e8a31601ebf4518000f5fa28be007afd145e203d7e8a2e901ebf4517100f5fa28b6807afd1459203d7e8a2a101ebf4514c00f5fa2897c07afd1447803d7e8a22201ebf4510700f5fa2880c07afd143f203d7e8a1f701ebf450fa00f5fa287c007afd143d003d7e8a1e401ebf450f000f5fa2877007afd1437a03d7e8a19b01ebf450c880f5fa2858407afd142ba03d7e8a
  | 20 => 0x236051bf45108028dfa287ec146fd143e60a37e8a1b6051bf450c4028dfa285c0146fd142c80a37e8a0dc051bf4505d028dfa282b4146fd1413a0a37e8a08f051bf4562681f5fa2abc80fafd155ba07d7e8aacd03ebf4554c81f5fa29fb00fafd14b1407d7e8a4b903ebf451d601f5fa28ea40fafd1473407d7e8a38303ebf4519001f5fa28c240fafd145f607d7e8a2c303ebf4514981f5fa28a0c0fafd1449e07d7e8a23603ebf4510801f5fa287ec0fafd143e607d7e8a1b603ebf450c401f5fa285c00fafd142c807d7e8a0dc03ebf4505d01f5fa282b40fafd1413a07d7e8a08f03ebf455db019dfa2abc80cefd155ba0677e8aacd033bf4554c819dfa291600cefd147bc0677e8a383033bf45190019dfa28c240cefd145f60677e8a2c3033bf45149819dfa28a0c0cefd1449e0677e8a236033bf45108019dfa287ec0cefd143e60677e8a
  | 21 => 0xa9905ebf451c182f5fa28c8017afd146120bd7e8a2fb05ebf4516182f5fa28a4c17afd145060bd7e8a24f05ebf4511b02f5fa2884017afd143f60bd7e8a1f305ebf450db02f5fa2862017afd142e00bd7e8a16405ebf4506e02f5fa282e817afd1415a0bd7e8a09d05ebf4504782f5fa2b26816efd155e40b77e8aadd05bbf4556682ddfa2aa6416efd1475c0b77e8a38305bbf4519002ddfa28c2416efd145f60b77e8a2c305bbf4514982ddfa28a0c16efd1449e0b77e8a23605bbf4510802ddfa287ec16efd143e60b77e8a1b605bbf450c402ddfa285c016efd142c80b77e8a0dc05bbf4505d02ddfa282b416efd1413a0b77e8a08f05bbf455fa028dfa2abc8146fd155ba0a37e8aacd051bf4554c828dfa296f4146fd148b00a37e8a383051bf45190028dfa28c24146fd145f60a37e8a2c3051bf45149828dfa28a0c146fd1449e0a37e8a
  | 22 => 0x34201edf4515480f6fa288e807b7d1440403dbe8a1bc01edf450c180f6fa2860c06f7d14710019be8a36b00cdf451a10066fa28aa40337d14474019be8a20200cdf450de0066fa2860c0337d155e40bc7e8a38305e3f4518482f1fa28bec178fd145860bc7e8a28305e3f4511b02f1fa287ec178fd1436c0bc7e8a18805e3f4505682f1fa2823c178fd1467803c7e8ab00af2bf455ad5755fa2aed2b76fd155d55bb7e8aa99a38bf452de99bdfa28c00beefd145925877e8a298293bf45267941dfa288f08dafd144063f77e8a1f91f3bf450fb8f9dfa287d07cefd147583e17e8a1f31f0bf4522c0f25fa28a0c792fd147bc3c17e8a1bd1b6bf450c88c45fa2a88439efd143e61cf7e8a4fc0dcbf450f806e5fa2839c372fd1475c18d7e8a0b70adbf450f984d5fa2945c23efd141ce11f7e8a09a08fbf4557902f5fa2ab7417afd1559a0bd7e8a
  | 23 => 0x2d800cf7451538067ba28994033dd14472019ee8a20000cf7450fb8067ba286e8033dd1431a019ee8a0bf00cf7450598067ba28e1ce0fbd14682613de8a2c82c3ef45266941f7a2960492bbd143f03e7de8a1bb1b6ef450c78c477a283042ebbd1416a15bde8a1fb055ef450fd82277a28da809bbd146d4043de8a6e401eef4531580f77a2952007bbd1470e03dde8a36a01eef451a080f77a28b8407bbd1459003dde8a2a801eef4512500f77a287e007bbd1437603dde8a18f01eef450c080f77a2830407bbd1416a03dde8a1fb016ef451c380677a28da8033bd14682019de8a2e100cef4516400677a28aa0033bd14494019de8a1f800cef450dd80677a2863c033bd14302019de8a0c100cef4505a80677a28e20e0f7d14684613be8a4ce283df4511d11b6fa288087ef7d1437836dbe8a183024df4531600f6fa28e2007b7d146d603dbe8a
  | 24 => 0xb10adfb451b40137da285fc093ed14c5203df68a36801efb4519f80f7da28b1c07bed1454c03df68a1fe01efb450dc00f7da285fc07bed1416203df68a36800cfb4519f8067da28b1c033ed1454c019f68a1fe00cfb450dc0067da285fc033ed14162019f68a1f71f3b7450fb80f5ba287dc032dd1470c707ee8a340309f7451b4941fba28b0c997dd1447246dee8a2001fbf7450fb8f9fba286e86dbdd1431a311ee8a0bf0baf745059856fba28a0c13bdd14506087ee8a283039f745161816fba28da409bdd144ca049ee8a6e301ef74531500f7ba295e807bdd1470c03dee8a37e01ef7451b480f7ba28d0007bdd145b003dee8a2a701ef74513280f7ba288e407bdd1440003dee8a1f701ef7450dd00f7ba2863407bdd1417e03dee8a0b301ef74513280dfba28b0c053dd14ad4019ee8a38600cf7451bf0067ba28da4033dd14680019ee8a
  | 25 => 0x5ba385fd451c29c1fea28fdccfbf51467c613fa8a44b2c6fd45163161fea2932ca0ff514c1a471fa8a238236fd451f58fe7ea287f07eff5148fa317fa8a18b188fd45265816fea28d9c09bf5142fa049fa8a367021fd4557b00f7ea2aabc07bf51553a03dfa8aa8701efd4551700f7ea28e1407bf5146fa03dfa8a36701efd4519f00f7ea28bd007bf5145ca03dfa8a2d601efd4516300f7ea28a9007bf51453a03dfa8a25101efd4511c00f7ea2884807bf51441403dfa8a1fc01efd450e100f7ea2862c07bf5142fa03dfa8a17101efd4509200f7ea2845407bf51421203dfa8a10601efd4507e00f7ea283b407bf51418c03dfa8a0a101efd450be80dfea28e14033f5146ce019fa8a33e00cfd451630067ea28a90033f514470019fa8a1fc00cfd450c58067ea285f4033f51467e613f68a2c72c3fb45266141fda287f87efed1437036df68a
  | 26 => 0x1f10187f850f880b3fc287c4045fe1564a020ff0aada0107f8552c0083fc2a8e4041fe14c72020ff0a5dc0107f852c90083fc29314041fe14948020ff0a43e0107f8521e8083fc290f0041fe1484c020ff0a3960107f851c10083fc28de8041fe146be020ff0a33c0107f851930083fc28b28041fe1447a020ff0a2290107f851078083fc28810041fe143e2020ff0a1e80107f850df0083fc28648041fe142b8020ff0a1420107f8506d0083fc28338041fe14170020ff0a05e0107f850258083fc28e10e0ff91467a613fc8a2c52c3fe4511b91b7f228628623f9145062f7fc8a0af0adfe450bd8127f229ee807bf91470803dfc8a33d01efe4516280f7f228a8c07bf91446e03dfc8a18a01efe450bd80f7f2282bc07bf914708019fc8a33d00cfe451628067f228a8c033f91446e019fc8a18a00cfe450bd8067f2282bc033f91418c03d7a8a
  | 27 => 0x43e1f07f850f88f83fc287c47b9fe143e23d6ff0a1be1b47f850c90c33fc2a86433dfe146be19eff0a15c0cf7f8506d067bfc2836433dfe141a619eff0a0d20cf7f8505c055bfc287c4239fe143e2106ff0aadb05e7f8556582f3fc2aa60179fe146cc0bcff0a32705e7f8518f82f3fc28b08179fe145240bcff0a23505e7f850fd02f3fc287c0179fe143680bcff0a18605e7f850bc82f3fc28588179fe1419e0bcff0a0ab05e7f8504702f3fc2833c175fe157fc096ff0aadb04b7f85565825bfc2aa6012dfe14dfa096ff0a62204b7f852d1825bfc293b012dfe1498a096ff0a47604b7f85230025bfc290b812dfe146cc096ff0a32704b7f8518f825bfc28b0812dfe14524096ff0a23504b7f850fd025bfc287c012dfe14368096ff0a18604b7f850bc825bfc2858812dfe1419e096ff0a0ab04b7f85047025bfc2833c101fe1419e06aff0a
  | 28 => 0x1f0025bf850f80125fc287c008efe143e00457f0a1f0021bf850f80105fc287c007efe143e003d7f0a1f001dbf850f800e5fc287c006efe143e00357f0a1f0019bf850f800c5fc287c005efe143e002d7f0a1f0015bf850f800a5fc287c004efe143e00257f0a1f0011bf855750085fc2aa44042fe154f60217f0a591010bf8527e0085fc292d4042fe1495e0217f0a4a3010bf852148085fc29094042fe147ba0217f0a395010bf851c68085fc28e04042fe146000217f0a2f8010bf851748085fc28b88042fe145920217f0a2a1010bf8511e0085fc2880c042fe143e00217f0a1bd010bf850c88085fc284b0042fe142080217f0a0da010bf8505b8085fc281b0042fe140b60217f0a033010bf850f8007dfc287c003afe143e001b7f0a1f000cbf850f8005dfc2ab6ab2dfe1464c63eff0a2ca2c27f8511e91abfc288107e9fe154443e2ff0a
  | 29 => 0x1f0044bf850f8021dfc287c010afe143e00837f0a1f0040bf850f801fdfc2ab6c0fafe14b8c07d7f0a51f03ebf8527901f5fc292e00fafe1475007d7f0a39903ebf851b301f5fc28b080fafe1446a07d7f0a1fa03ebf850f801f5fc286d00fafe1430c07d7f0a17903ebf8506781f5fc282ac0fafe143e007b7f0a1f003cbf850f801ddfc287c00eafe143e00737f0a1f0038bf850f801bdfc287c00dafe143e006b7f0a1f0034bf855da819dfc2ab6c0cefe147ba0677f0a366033bf85193819dfc28c7c0cefe145840677f0a292033bf8511a819dfc287e80cefe143e00677f0a1b4033bf850c3019dfc285e40cefe142c40677f0a0cf033bf85055819dfc282380cefe143e00657f0a1f0031bf850f80185fc287c00befe143e005d7f0a1f002dbf850f80165fc287c00aefe143e00557f0a1f0029bf850f80145fc287c009efe143e004d7f0a
  | 30 => 0x1fa05ebf850f802f5fc286d017afe1430c0bd7f0a17905ebf850b102f5fc2833c17afe141560bd7f0a1f005dbf850f802e5fc2b26416efe155b60b77f0aa9805bbf851c682ddfc28d9816efe1464e0b77f0a31f05bbf8516102ddfc28a4816efe1446a0b77f0a1fa05bbf850f802ddfc286d016efe1430c0b77f0a17905bbf850b102ddfc2833c16efe141560b77f0a08e05bbf850f802d5fc287c0166fe143e00b17f0a1f0057bf850f802b5fc287c0156fe143e00a97f0a1f0053bf850f80295fc2afcc146fe146cc0a37f0a327051bf85161028dfc288d4146fe143f40a37f0a1f0051bf850da028dfc28618146fe142f20a37f0a162051bf85067828dfc282ac146fe1411c0a37f0a1f0050bf850f8027dfc287c013afe143e009b7f0a1f004cbf850f8025dfc287c012afe143e00937f0a1f0048bf850f8023dfc287c011afe143e008b7f0a
  | 31 => 0xa611f0bf855110f85fc2a8847c2fe154403e17f0aa1f1f0bf8550f0f85fc2a8747c2fe154383e17f0aa1b1f0bf8550d0f85fc2a8647c2fe1496a3e17f0a4b41f0bf852598f85fc292c87c2fe149623e17f0a4b01f0bf852578f85fc292b87c2fe1490c3e17f0a43e1f0bf8520b8f85fc28ed07c2fe147583e17f0a1f91f0bf850fc0f85fc287dc7c2fe143ec3e17f0a1f51f0bf850fa0f85fc287cc7c2fe143e43e17f0a1f11f0bf850f80f7dfc287c07bafe143e03db7f0a1f01ecbf850f80f5dfc287c07aafe143e03d37f0a3dd1e0bf850f80e0dfc286f46d2fe1432230d7f0a1f016cbf850f80aa5fc28d984b2fe143e022b7f0a1f0106bf850bc8825fc287c03b2fe143e01d17f0a1f00dcbf8506d067dfc28e3431afe143e01877f0a1f00b6bf8505b855dfc287c026afe143e011d7f0a1f0083bf851b302f5fc28b0817afe1446a0bd7f0a
  | _ => 0
def ns2_Data3_ : Nat → Nat
  | 0 => 0x1f81f0af851b51b377c28b20b0bbe14b00495df0a1f81f0ef850dd8da77c2863c61bbe143022f3df0a4620cfef8505a855f7c288d40efbe1446a05ddf0a235024ef851c380cf7c28e1c043be146d4021df0a341010ef8517080877c28b20043be14550021df0a24a010ef850fc00877c286ec043be1431e021df0a181010ef8506080877c282d4043be146d66cdbf0a23a235df851010fd6fc286f06d37e143062f3bf0a4630cfdf851c400cefc28e200437e146d6021bf0a342010df851548086fc288e80437e14404021bf0a1bc010df850c18086fc290f87c0fe143e23e07f0a0da0cf3f851b302f1fc28b08178fe1446a0bc7f0a1fa05e3f850f802f1fc286d0178fe1430c0bc7f0a17905e3f850b102f1fc2833c178fe141560bc7f0a1f004b3f8506d0081fc2abaab6efe145925857f0a23c235bf851018fd5fc2b0ac7c2fe155763e17f0a
  | 1 => 0x2c6010fd851570087ec28a90043f61453a021fb0a241010fd8511c0087ec28828043f6143f8021fb0a1cd010fd850c58087ec285f4043f6142b6021fb0a147010fd850920087ec283f0043f6141c0021fb0a0d4010fd850318087ec28104043f6146d06cdf70a2c72c2fb850ff0fd7dc286e06d3ee142fe2f3f70a33f0cffb85058855fdc28cfc063ee1467e02df70a368010fb8519f8087dc28b1c043ee1454c021f70a1fe010fb850dc0087dc285fc043ee14162021f70a1f71f0b7851b49b37bc29914997de1447246bef0a2001faf7850fb8f87bc286e86d3de1431a30def0a4610cff785059855fbc285e413bde142f2087ef0a179039f7851a000c7bc28e18043de146fc021ef0a369010f7851a00087bc28b60043de1454e021ef0a265010f78511c8087bc28800043de143ee021ef0a1ba010f7850c68087bc282fc043de14166021ef0a
  | 2 => 0x1fa00cff050f80067f8286d0033fc14362019fe0a1ab00cff050c30067f8285e4033fc142c4019fe0a12200cff0508a8067f828418033fc141f0019fe0a0e900cff050678067f8282ac033fc1411c019fe0a2c52c2fe8511b91aff42862861bfa142f62f3fd0a45f0cffe85057855ff428cf405bfa14708021fd0a33d010fe851628087f428a8c043fa1446e021fd0a18a010fe850bd8087f4282bc043fa148c0096fb0a5ab367fd851b39b37ec2a888cfbf61493658dfb0a2c62c2fd8530611c7ec288e08d7f6147d43f9fb0a1fc1fafd852420c5fec2862c61bf61489c2fbfb0a17d179fd85230067fec2918012ff61470a033fb0a33e018fd8519f00b7ec28cf8047f6155ee021fb0aad1010fd8554e0087ec2a938043f61545a021fb0a385010fd851be8087ec28d9c043f6146c4021fb0a35b010fd8519f0087ec28c2c043f6145bc021fb0a
  | 3 => 0x29201eff0511a80f7f8287e807bfc143e003dfe0a1b401eff050c300f7f8285e407bfc142c403dfe0a0cf01eff0505580f7f82823807bfc142f2037fe0a0dc014ff055960087f82abc8043fc155ba021fe0aacd010ff0554c8087f829adc043fc14d6a021fe0a5f3010ff052e38087f829214043fc14878021fe0a3ac010ff051c18087f828c80043fc14612021fe0a2fb010ff051618087f828a4c043fc14506021fe0a24f010ff0511b0087f828840043fc143f6021fe0a1f3010ff050db0087f828620043fc142e0021fe0a164010ff0506e0087f8282e8043fc1415a021fe0a09d010ff050478087f82837003bfc155b6019fe0aacb00cff055548067f82aa60033fc15506019fe0aa2a00cff051bd8067f828d98033fc1464e019fe0a31f00cff051790067f828b8c033fc14584019fe0a29a00cff051490067f8288d4033fc1440a019fe0a
  | 4 => 0xa200da1fcd5100670fe691a41787f347100bc3f9a36b05e1fcd1a102f0fe68aa41787f344740bc3f9a20205e1fcd0de02f0fe6860c1787f347583e17e0a1f31f0bf050f806e5f8287c007afc143e00197e0a43c0107f055cdd6dff82ab76b6ffc15677597fe0aacdacbff0559dd4c7f82aa66a63fc14ad063ffe0a32031fff052251617f828b0cb0bfc14b30525fe0a293292ff05265141ff829af88d7fc1446c46bfe0a4091faff050fd8fd7f828eb07c3fc143e63e1fe0a51e1b4ff050db0da7f82930c61bfc1431030dfe0a493162ff050b20b17f8287c0373fc1422a1b9fe0a1060dcff0522f067ff8293b82affc1415a157fe0a3ac08eff050478477f8293280b7fc1559604ffe0a366026ff050bc8127f828d98087fc155b603dfe0aacb01eff0554c00f7f8298a007bfc14a7e03dfe0a36601eff0519380f7f828c7c07bfc1458403dfe0a
  | 5 => 0xa1d1e83bcd50e86d1de6a874338ef348ca0bc779a36805e3bcd19f82f1de68b1c178ef3454c0bc779a1fe05e3bcd0dc02f1de685fc178ef341620bc779a33f05b3bcd19f81f1de68cfc0ccef341b4024779aa1f1f7a7cd0fc0fbd3e6a8807de5f34684680af9aa63a1e37cd50f19e1be6a8887dcdf3543c3d06f9aa1e0da37cd50f0671be69198178df3470c0bc6f9a37e05e37cd1b482f1be68d00178df345b00bc6f9a2a705e37cd13282f1be688e4178df344000bc6f9a1f705e37cd0dd02f1be68634178df3417e0bc6f9a0b305e37cd19e01c9be6a98e87cbf3543e6785f9aa1f1e82fcd50f86d17e6a87c338bf348ce0bc5f9a38705e2fcd1b502f17e68d04178bf345c20bc5f9a2c805e2fcd15402f17e68928178bf343f00bc5f9a1bb05e2fcd0c782f17e68604178bf341820bc5f9a0b505e2fcd531d100fe6a880cf07f354403d03f9a
  | 6 => 0x1b605e3f4d0c402f1fa685c0178fd341740bc7e9a0ad05e3f4d04e82f1fa6823c178fd346120b67e9a30903e3f4d1848199fa68cf0078fd354c60187e9a33c00c3f4d0f40061fa68368030fd3419c0187e9a33e33d7ccd50d99fbd668cfccf5eb354363ef6d9a34133d6ecd531d0d9f66a86ccf0fb354363d07d9aa1b0da3ecd50d8671f669190178fb347080bc7d9a33d05e3ecd16282f1f668a8c178fb3446e0bc7d9a18a05e3ecd0bd82f1f6682bc178fb3543867ef39a33f33e79cd50e0fbdae68d08cf977356bd4387b9aa63a1c3dcd50e19e1ee6a8707a0f7354381b47b9aa1c0ce3dcd1c282f1ee68d9c178f73467c0bc7b9a2c605e3dcd15202f1ee688e0178f7343f80bc7b9a18b05e3dcd0be82f1ee6a8747decf3543c67ee79a34033f73cd50f99fb5e68d04cfdaf3544067eb79a34233f5bcd531d0e9de6a884cfcef3543a678779a
  | 7 => 0xa63a193f8d50c99e1fc6a8887c0fe3487c3e07f1a1f11f03f8d50c8f41fc6a864368fe341b419e7f1aa190ce3f8d50c82f1fc68d98178fe3464e0bc7f1a2c205e3f8d11a82f1fc687e8178fe343e00bc7f1a1b405e3f8d0c302f1fc685e4178fe342c40bc7f1a0cf05e3f8d05582f1fc68238178fe343e00967f1a0da0103f8d50d984bf268cf4c25f93418c03d7a9aa1c3097d4d19f184bea6a868cfded3543a612f69a33f3097b4d19f8063da6a8687dedd343ee3e76e9a1f701eb74d0fb8065ba6a878c25dd34680612ee9aa1f3096f4d1a0984b7a6a880c257d34684612be9aa63a1a3f4d50d19e1fa6a884c24fd354343d07e9aa1a0da3f4d50d0671fa6abc8178fd354740bc7e9aa2a05e3f4d50d02f1fa68e0c178fd346120bc7e9a2fb05e3f4d16182f1fa68a0c178fd3449e0bc7e9a23605e3f4d10802f1fa687ec178fd343e60bc7e9a
  | 8 => 0x4b00c7fc582f005bfe2c12c02dff1609e05fff8b03d024ffc58188107fe2c11c073ff1667a613fc1a33d00cfe0d50d19f7e868fdccfbf43467c613fa1a33e027fd0d55d80f7e868cf807bf4343e203dfa1a08e01efd0d5230087e868c2c043f4343e6021fa1a0e7010fd0d05d0087e868cf8033f434680613ee1a34000cf70d50d0f85f868eb07c2fc343e63e17e1a1f00dcbf0d0f800f5f8687c0032fc35432612fe1a43c0107f0d50d99f7e468cf8cf7f23468267bdd1aa1b1f0be8d50e99f7cc68cfccfbe63543c67deb1a34033ef58d50f99f76c68d04cfbb63544067dbb1a34233edd8d51099f5ec6a8707c2f63467c0b77b1aa2233e7d8d19f02f3ec68cf8175f6348c0096fb1a34133feb8d1a119fedc6a8747c2ee3543267ef71a33f0187b8d1a11a06bc6a8647dede3543c3e16f1a1f71f0b78d50f8f857c687e07c2be354403e13f1a
  | 9 => 0x1be0287fc582f0143fe2c12c0a1ff160bc04eff8b04b0277fc582f0133fe2c12c099ff160bc04aff8b04b0257fc582f0123fe2c12c091ff160bc046ff8b04b0237fc582f0113fe2c12c089ff160bc042ff8b04b0217fc582f0103fe2c12c081ff160bc03eff8b04b01f7fc582f00f3fe2c12c079ff160bc03aff8b04b01d7fc582f00e3fe2c12c071ff160bc036ff8b04b01b7fc582f00d3fe2c12c069ff17432032ff8b05e0197fc582e80cbfe2c12c065ff16080032ff8b0350197fc582f00c3fe2c12c061ff160bc02eff8b04b0177fc582f00b3fe2c12c059ff160bc02aff8b04b0157fc582f00a3fe2c12c051ff160bc026ff8b04b0137fc582f0093fe2c12c049ff166be022ff8b05e0117fc5825808bfe2c7c4041ff160bc020ff8b04b0107fc582f007bfe2c12c03dff160bc01cff8b04b00e7fc582f006bfe2c12c035ff160bc018ff8b
  | 10 => 0x5e0437fc5825821bfe2c83c109ff160bc084ff8b04b0427fc582f020bfe2c174105ff16096082ff8b05e0407fc58258203fe2c5080fdff160bc07eff8b04b03f7fc582f01f3fe2c12c0f9ff160bc07aff8b04b03d7fc585c01e3fe2c1780f1ff16096078ff8b05e03b7fc582581dbfe2c1780e9ff16096074ff8b05e0397fc582581cbfe2c1780e1ff16096070ff8b05e0377fc582581bbfe2cc980d9ff160bc06cff8b04b0367fc582f01abfe2c1640d5ff1609606aff8b0410357fc582f01a3fe2c12c0d1ff163d0066ff8b05e0337fc5825819bfe2c1780c9ff16096064ff8b05e0317fc5825818bfe2c1780c1ff16096060ff8b05e02f7fc5825817bfe2c8100b9ff160bc05cff8b04b02e7fc582f016bfe2c12c0b5ff160bc058ff8b04b02c7fc582f015bfe2c12c0adff16704054ff8b05e02a7fc58258153fe2c1780a5ff16096052ff8b
  | 11 => 0x5e04e7fc582f026bfe2c178131ff17504096ff8ba2204b7fc5d10825bfe2e88012dff1743e096ff8ba1e04b7fc5d0e825bfe2e87012dff17436096ff8ba1a04b7fc5d0c825bfe2c36812dff161b2096ff8b0d804b7fc586b825bfe2c35812dff161aa096ff8b0d404b7fc5869825bfe2c34812dff161a2096ff8b0d004b7fc5867825bfe2c1f812dff160bc096ff8b05d04b7fc582e025bfe2c16c12dff160b4096ff8b05904b7fc582c025bfe2c15c12dff160ac096ff8b05504b7fc582a025bfe2c14c12dff160a4096ff8b05104b7fc5828025bfe2c13c12dff1609c096ff8b04d04b7fc5826025bfe2c178129ff16096094ff8b2290497fc582f024bfe2c12c125ff166be090ff8b05e0487fc58258243fe2c17811dff1609608eff8b1920467fc582f0233fe2c12c119ff160bc08aff8b04b0457fc591e8223fe2c178111ff16096088ff8b
  | 12 => 0x3e00ebfc58198075fe2c178036ff160b601b7f8b05100dbfc581f006dfe2c0cc036ff160bc0197f8b05b00cbfc58288065fe2c0f8032ff160660197f8b05e00bbfc582d805dfe2c14402eff1607c0177f8b03300bbfc5d6d510bfe2e962875ff17473434ff8badaa197fc5d3182f3fe2e888179ff174420bcff8ba2005e7fc5d0f82f3fe2e878179ff1743a0bcff8ba1c05e7fc5d0d82f3fe2e868179ff174320bcff8b16105e7fc58b002f3fe2c57c179ff162bc0bcff8b15d05e7fc58ae02f3fe2c56c179ff162b40bcff8b14d05e7fc588182f3fe2c3d8179ff161340bcff8b05e05d7fc582f02e3fe2c33816dff160bc0b6ff8b05e05a7fc582f02cbfe2c178161ff166f40aeff8b05e0577fc582f02b3fe2c178155ff160bc0a8ff8b05e0537fc582e829bfe2c178149ff166780a2ff8b05e0517fc582f0283fe2c17813dff1659409cff8b
  | 13 => 0x5e01abfc582d80d5fe2c14406aff1607c0357f8b03301abfc582f00cdfe2c16c066ff160a20337f8b03e019bfc581980cdfe2c178062ff160b60317f8b051018bfc581f00c5fe2c0cc062ff160bc02f7f8b05b017bfc582880bdfe2c0f805eff1606602f7f8b05e016bfc582d80b5fe2c14405aff1607c02d7f8b033016bfc582f00adfe2c16c056ff160a202b7f8b03e015bfc581980adfe2c178052ff160b60297f8b051014bfc581f00a5fe2c0cc052ff160bc0277f8b05b013bfc5828809dfe2c0f804eff160660277f8b05e012bfc582d8095fe2c14404aff1607c0257f8b033012bfc582f008dfe2c16c046ff160a20237f8b03e011bfc5819808dfe2c7c0042ff160bc0217f8b05b010bfc58288085fe2c0f8042ff160660217f8b05e00fbfc582d807dfe2c14403eff1607c01f7f8b03300fbfc582f0075fe2c16c03aff160a201d7f8b
  | 14 => 0x5e026bfc582d8135fe2c14409aff1607c04d7f8b033026bfc5971012dfe2c178096ff160b604b7f8b051025bfc581f012dfe2c0cc096ff160bc0497f8b05b024bfc58288125fe2c0f8092ff160660497f8b05e023bfc582d811dfe2c14408eff1607c0477f8b033023bfc582f0115fe2c16c08aff160a20457f8b03e022bfc58198115fe2c410086ff160bc0437f8b05b021bfc5828810dfe2c0f8086ff160660437f8b05e020bfc582d8105fe2c144082ff1607c0417f8b033020bfc582f00fdfe2c16c07eff160a203f7f8b03e01fbfc581980fdfe2c39c07aff160bc03d7f8b05b01ebfc582880f5fe2c0f807aff1606603d7f8b05e01dbfc582d80edfe2c144076ff1607c03b7f8b03301dbfc582f00e5fe2c16c072ff160a20397f8b03e01cbfc581980e5fe2c4b006eff160bc0377f8b05b01bbfc582880ddfe2c0f806eff160660377f8b
  | 15 => 0x6c031bfc582f018dfe2c16c0c6ff160a20637f8b03e031bfc5819818dfe2cba40c2ff160bc0617f8b05b030bfc58288185fe2c0f80c2ff160660617f8b05e02fbfc582d817dfe2c1440beff1607c05f7f8b03302fbfc59018175fe2c1780baff160b605d7f8b05102ebfc581f0175fe2c0cc0baff163c805b7f8b05e02dbfc582d816dfe2c1440b6ff1607c05b7f8b03302dbfc597c0165fe2c1780b2ff160b60597f8b05102cbfc581f0165fe2c0cc0b2ff160bc0577f8b05b02bbfc5828815dfe2c0f80aeff160660577f8b38102abfc582f0155fe2c16c0aaff160a20557f8b03e02abfc58198155fe2c4740a6ff160bc0537f8b05b029bfc5828814dfe2c0f80a6ff160660537f8b1bd028bfc582f0145fe2c16c0a2ff160a20517f8b03e028bfc58198145fe2e86809eff160bc04f7f8b05b027bfc5828813dfe2c0f809eff1606604f7f8b
  | 16 => 0xa1b033bfc5d0d019dfe2e8640ceff163d00677f8b1e7033bfc58f3019dfe2c7940ceff163c80677f8b1e3033bfc58f1019dfe2c7840ceff163c00677f8b1df033bfc58ef019dfe2c4780ceff160d80677f8b05e033bfc582e819dfe2c1700ceff160b60677f8b05a033bfc582c819dfe2c1600ceff160ae0677f8b056033bfc582a819dfe2c1500ceff160a60677f8b052033bfc5828819dfe2c1400ceff1609e0677f8b04e033bfc5826819dfe2c1300ceff160960677f8b04a033bfc5824819dfe2c1200ceff1608e0677f8b046033bfc5822819dfe2c1100ceff160860677f8b042033bfc5820819dfe2c1000ceff1607e0677f8b03e033bfc581e819dfe2c0f00ceff160760677f8b03a033bfc581c819dfe2c0e00ceff1606e0677f8b036033bfc581a819dfe2c0d00ceff160bc0657f8b05b032bfc58288195fe2c0f80caff160660657f8b
  | 17 => 0x4603ebfc582281f5fe2c1100faff1608607d7f8b04203ebfc582081f5fe2c1000faff1607e07d7f8b33303dbfc582f01edfe2c16c0f6ff160a207b7f8b03e03dbfc585b81e5fe2c1780f2ff160b60797f8b05103cbfc581f01e5fe2cc580eeff160bc0777f8b05b03bbfc582881ddfe2c0f80eeff160bc0757f8b05b03abfc582881d5fe2c0f80eaff162200737f8b05e039bfc582d81cdfe2c1440e6ff1607c0737f8b298038bfc582f01c5fe2c16c0e2ff160a20717f8b03e038bfc58ee01bdfe2c1780deff160b606f7f8b051037bfc581f01bdfe2c1780daff160b606d7f8b051036bfc581f01b5fe2c8880d6ff160bc06b7f8b05b035bfc582881adfe2c0f80d6ff162580697f8b05e034bfc582d81a5fe2c1440d2ff1607c0697f8ba5b033bfc5d11019dfe2e8840ceff174400677f8ba1f033bfc5d0f019dfe2e8740ceff174380677f8b
  | 18 => 0x5e042bfc582d8215fe2c14410aff163360837f8b05e041bfc582d820dfe2c144106ff161340817f8b05e040bfc582d8205fe2c144102ff160bc07f7f8b05b03fbfc582881fdfe2e9840faff1744407d7f8ba2103ebfc5d1001f5fe2e87c0faff1743c07d7f8ba1d03ebfc5d0e01f5fe2e86c0faff1743407d7f8ba1903ebfc58fc81f5fe2c7e00faff163ee07d7f8b1f603ebfc58fa81f5fe2c7d00faff163e607d7f8b1f203ebfc58f801f5fe2c7040faff162d807d7f8b0ec03ebfc586181f5fe2c2d80faff1613407d7f8b05e03ebfc582e81f5fe2c1700faff160b607d7f8b05a03ebfc582c81f5fe2c1600faff160ae07d7f8b05603ebfc582a81f5fe2c1500faff160a607d7f8b05203ebfc582881f5fe2c1400faff1609e07d7f8b04e03ebfc582681f5fe2c1300faff1609607d7f8b04a03ebfc582481f5fe2c1200faff1608e07d7f8b
  | 19 => 0xcb051bfc582f028dfe2c174146ff160b80a37f8b05b051bfc582d028dfe2c164146ff160b00a37f8b057051bfc582b028dfe2c154146ff160a80a37f8b053051bfc5829028dfe2c178142ff160b60a17f8b051050bfc5865827dfe2c17813eff160b609f7f8b05104fbfc59648275fe2c17813aff160b609d7f8b05104ebfc582f026dfe2c16c136ff160a209b7f8b2a104cbfc582f0265fe2c16c132ff160a20997f8b0da04bbfc582f025dfe2c16c12eff160a20977f8b05e04abfc582d8255fe2c14412aff160bc0937f8b05b049bfc582b824dfe2c144126ff160bc0917f8b05b048bfc58288245fe2c17811eff160b608f7f8b051047bfc58c88235fe2c17811aff160b608d7f8b051046bfc582f022dfe2c16c116ff160a208b7f8b23c044bfc582f0225fe2c16c112ff160a20897f8b05e043bfc582d821dfe2c14410eff1641c0857f8b
  | 20 => 0xa1b05bbfc5d0d02ddfe2e86416eff1619c0b77f8b0cd05bbfc586602ddfe2c32c16eff161940b77f8b0c905bbfc586402ddfe2c31c16eff1618c0b77f8b0c505bbfc586202ddfe2c23016eff160d80b77f8b05e05bbfc582e82ddfe2c17016eff160bc0b57f8b05b05abfc597882cdfe2c178166ff160b60b37f8b05e058bfc582d82c5fe2c17815eff160b60af7f8b05e056bfc582d82b5fe2c178156ff160b60ab7f8b300054bfc582f02a5fe2c16c152ff164be0a77f8b05e053bfc582d829dfe2c41014aff160bc0a57f8b05b052bfc5d21828dfe2e888146ff174420a37f8ba20051bfc5d0f828dfe2e878146ff1743a0a37f8ba1c051bfc5d0d828dfe2e868146ff174320a37f8b33c051bfc599d828dfe2cce8146ff166720a37f8b338051bfc599b828dfe2ccd8146ff1666a0a37f8b1e4051bfc58d9828dfe2c4e0146ff162220a37f8b
  | 21 => 0x5e0203fc582f00f9fe2c178078ff160bc03a7f8b05e01c3fc582f00d9fe2c178068ff160bc0327f8b05e0183fc582f00b9fe2c178058ff160bc02a7f8b05e0143fc582f0099fe2c178048ff160bc0227f8b05e0103fc582f0079fe2c178038ff160bc01a7f8b05e00c3fc582f0059fe2e8e288aff174f74417f8bab7a1ebfc5d7550e5fe2ea4686eff174714357f8bb00a19bfc5d3182f5fe2e88817aff174420bd7f8ba2005ebfc5d0f82f5fe2e87817aff1743a0bd7f8ba1c05ebfc5d0d82f5fe2e86817aff174320bd7f8b16105ebfc58b002f5fe2c57c17aff162bc0bd7f8b15d05ebfc58ae02f5fe2c56c17aff162b40bd7f8b14d05ebfc588182f5fe2c3d817aff161340bd7f8b2da05dbfc582f02edfe2cb88172ff160bc0b97f8ba8105bbfc5d1102ddfe2e88416eff174400b77f8ba1f05bbfc5d0f02ddfe2e87416eff174380b77f8b
  | 22 => 0x5e05a3fc582f02c9fe2c178160ff160bc0ae7f8b05e0563fc582f02a9fe2c178150ff160bc0a67f8b05e0523fc599e0289fe2c178144ff160bc0a07f8b05e04f3fc582f0271fe2c178134ff160bc0987f8b0da04b3fc582f0259fe2c16c12cff160bc0947f8b05e0493fc582f0241fe2c17811cff160bc08c7f8b05e0453fc582f0221fe2c17810cff160bc0847f8b05e0413fc582f0201fe2c1780fcff160bc07c7f8b04b03e3fc582f01e9fe2c1780f0ff160bc0767f8b05e03a3fc582f01c9fe2c1780e0ff160bc06e7f8b05e0363fc582f01a9fe2c1780d0ff163d00667f8b05e0333fc58258199fe2c1780c8ff160bc0627f8b05e0303fc582f0179fe2c1780b8ff160bc05a7f8b05e02c3fc582f0159fe2c1780a8ff160bc0527f8b05e0283fc582f0139fe2c178098ff160bc04a7f8b05e0243fc582f0119fe2c178088ff160bc0427f8b
  | 23 => 0x3b02fefc582a81777e2c1100bbbf16494057df8b1bb028efc5970812f7e2c154093bf1609a049df8b044024efc581781277e2c604087bf166d4037df8b341019efc582c80b77e2c11405bbf1607602ddf8b02e016efc581200b77e2ce1c047bf1618201fdf8b2a800befc582a823efe2c8e81137f160aa063bf8b03d031dfc59010176fe2c6f00a37f1609e04dbf8b031026dfc58c1810efe2cdac06f7f16684033bf8b05d018dfc582380c6fe2c0980637f16710023bf8b2a900bdfc5d3182f1fe2e888178ff174420bc7f8ba2005e3fc5d0f82f1fe2e878178ff1743a0bc7f8ba1c05e3fc5d0d82f1fe2e868178ff174320bc7f8b16105e3fc58b002f1fe2c57c178ff162bc0bc7f8b15d05e3fc58ae02f1fe2c56c178ff162b40bc7f8b14d05e3fc588182f1fe2c3d8178ff161340bc7f8b05e05d3fc582f02e1fe2c33816cff160bc0b67f8b
  | 24 => 0x2a400bfdc58258093de2cb1c13bef1608e087f78b0b103cfbc582381bfde2c7f80bbef1608a057f78b03702bfbc58dc0147de2c5fc087ef16086041f78b02b020fbc59b400dfde2ccfc067ef16096025f78b020012fbc5953005fde2c7dc0fadf160a20736f8b2d805df7c58290277be2c63411bdf16472089ef8b052043f7c5827821fbe2c13410fdf163ee07def8b0b303cf7c582901cfbe2c1440e7df1609e073ef8b20002ef7c5827016fbe2c1340b7df1608605bef8b03902df7c59bf0157be2c6e80a3df164ca04def8b02d022f7c5827010fbe2c10c087df16072043ef8b36901bf7c59a000cfbe2c14c053df1609c029ef8b043014f7c581c80a7be2c088053df1670c023ef8b0bf00ff7c5953805fbe2c7e00fabf1659009ddf8b05504defc58c782377e2c154117bf163f007ddf8b0b503cefc582b81df7e2c1540efbf16088077df8b
  | 25 => 0x2900cff458140067fa2c09c033fd1604c019fe8b02500cff458120067fa2c08c033fd16044019fe8b02100cff458100067fa2c07c033fd1603c019fe8b01d00cff4580e0067fa2c06c033fd16034019fe8b01900cff4580c0067fa2c05c033fd1602c019fe8b01500cff4580a0067fa2c04c033fd16024019fe8b01100cff458080067fa2c03c033fd1601c019fe8b00d00cff4580f005ffa2c03002ffd1658a09dfd8b18a046fec591b8227f62c2bc0f3fb1606205bfd8b03102bfec5817815ff62c0c40a7fb162f6043fd8b02d01cfec599e80cff62ce10047fb1606a01dfd8b02b00efec580e0077f62ca8c02ffb1658c09dfb8b18b046fdc591c0227ee2c0f40e7f71607a06ffb8b03b037fdc58fe0177ee2c0ec0a7f7162fa043fb8b03901efdc581480f7ee2cd9c06ff71667c033fb8b385011fdc58208087ee2c0dc043f71603c021fb8b
  | 26 => 0x30600cff459828067fa2cc10033fd16606019fe8b30200cff459660067fa2c8ac033fd16352019fe8b15000cff4586e0067fa2c200033fd160bc019fe8b05d00cff4582e0067fa2c16c033fd160b4019fe8b05900cff4582c0067fa2c15c033fd160ac019fe8b05500cff4582a0067fa2c14c033fd160a4019fe8b05100cff458280067fa2c13c033fd1609c019fe8b04d00cff458260067fa2c12c033fd16094019fe8b04900cff458240067fa2c11c033fd1608c019fe8b04500cff458220067fa2c10c033fd16084019fe8b04100cff458200067fa2c0fc033fd1607c019fe8b03d00cff4581e0067fa2c0ec033fd16074019fe8b03900cff4581c0067fa2c0dc033fd1606c019fe8b03500cff4581a0067fa2c0cc033fd16064019fe8b03100cff458180067fa2c0bc033fd1605c019fe8b02d00cff458160067fa2c0ac033fd16054019fe8b
  | 27 => 0x3401eff4581980f7fa2c0c807bfd1606203dfe8b03001eff4581780f7fa2c0b807bfd1605a03dfe8b02c01eff4581580f7fa2c0a807bfd1605203dfe8b02801eff4581380f7fa2c09807bfd1604a03dfe8b02401eff4581180f7fa2c08807bfd1604203dfe8b02001eff4580f80f7fa2c078077fd16048039fe8b01e01cff4581300dffa2c08406ffd1603c037fe8b01e01aff4598480cffa2c078067fd1603c031fe8b24f017ff4580f00bffa2c07805bfd1642002bfe8b01e015ff4580f00a7fa2c27404ffd1603c027fe8b01e012ff459c1808ffa2c078047fd161b8021fe8b01e010ff4585d007ffa2c07803ffd1603c01dfe8b17000dff4580f006ffa2e8e8033fd17444019fe8ba2100cff45d100067fa2e87c033fd1743c019fe8ba1d00cff45d0e0067fa2e86c033fd17434019fe8ba1900cff459848067fa2cc20033fd1660e019fe8b
  | 28 => 0xa1f01eff45d0f00f7fa2e87407bfd1743803dfe8ba1b01eff45d0d00f7fa2e86407bfd161d003dfe8b0e701eff4587300f7fa2c39407bfd161c803dfe8b0e301eff4587100f7fa2c38407bfd161c003dfe8b0df01eff4586f00f7fa2c37407bfd161b803dfe8b0db01eff4584780f7fa2c17807bfd160ba03dfe8b05c01eff4582d80f7fa2c16807bfd160b203dfe8b05801eff4582b80f7fa2c15807bfd160aa03dfe8b05401eff4582980f7fa2c14807bfd160a203dfe8b05001eff4582780f7fa2c13807bfd1609a03dfe8b04c01eff4582580f7fa2c12807bfd1609203dfe8b04801eff4582380f7fa2c11807bfd1608a03dfe8b04401eff4582180f7fa2c10807bfd1608203dfe8b04001eff4581f80f7fa2c0f807bfd1607a03dfe8b03c01eff4581d80f7fa2c0e807bfd1607203dfe8b03801eff4581b80f7fa2c0d807bfd1606a03dfe8b
  | 29 => 0x1d010ff8580e0087fc2c06c043fe16034021ff0b019010ff8580c0087fc2c05c043fe1602c021ff0b015010ff8580a0087fc2c04c043fe16024021ff0b011010ff85808007ffc2c05803bfe1602001dff0b01000dff8580a0067fc2c040033fe1601c019ff0b01000bff8581c80f7ea2c0a407bf51603c021fa8b1f303ebf4587380f5fa2c17807afd160b603d7e8b05101ebf4581f00f5fa2c0cc07afd160bc0197e8b05b00cbf458288065fa2c0f8032fd160660197e8b04b00c7f45d4cd117fa2eb36887fd175bb439fe8baf2a19ff4597d82a7fa2cb0c13bfd1631008dfe8b236044ff458478207fa2c7cc0fbfd1615a079fe8b16403aff4594981c7fa2cc800dbfd163f605dfe8b28302dff458db0147fa2e88409ffd1604c049fe8b026022ff45812010ffa2c098083fd16048041fe8ba4601eff45d1100f7fa2e88407bfd1744003dfe8b
  | 30 => 0x5d010ff8582e0087fc2c16c043fe160b4021ff0b059010ff8582c0087fc2c15c043fe160ac021ff0b055010ff8582a0087fc2c14c043fe160a4021ff0b051010ff858280087fc2c13c043fe1609c021ff0b04d010ff858260087fc2c12c043fe16094021ff0b049010ff858240087fc2c11c043fe1608c021ff0b045010ff858220087fc2c10c043fe16084021ff0b041010ff858200087fc2c0fc043fe1607c021ff0b03d010ff8581e0087fc2c0ec043fe16074021ff0b039010ff8581c0087fc2c0dc043fe1606c021ff0b035010ff8581a0087fc2c0cc043fe16064021ff0b031010ff858180087fc2c0bc043fe1605c021ff0b02d010ff858160087fc2c0ac043fe16054021ff0b029010ff858140087fc2c09c043fe1604c021ff0b025010ff858120087fc2c08c043fe16044021ff0b021010ff858100087fc2c07c043fe1603c021ff0b
  | 31 => 0xe00cff058208087ec2c0dc043f61603c021fb0b1f003ebf858f80085fc2c16c042fe160660217f0b0cf04b7f858f88083fc2c178041fe16096020ff0ba98a22ff85d65d10ffc2eb6e873fe1658409dff0b0cf04bff858c30237fc2c8d4113fe1611c081ff0b1f003eff8585581e7fc2c5880ebfe16524071ff0b31f036ff858fd0177fc2c6d00a3fe162f2043ff0b32701dff859b300dffc2e888067fe16032031ff0b019016ff8580c00a7fc2c06004bfe1602c025ff0b019011ff85d5d8087fc2e888043fe17442021ff0ba20010ff85d0f8087fc2e878043fe1743a021ff0ba1c010ff85d0d8087fc2e868043fe17432021ff0b1f1010ff858f80087fc2c7bc043fe163dc021ff0b1ed010ff858f60087fc2c7ac043fe163d4021ff0b1e9010ff858aa0087fc2c454043fe1620c021ff0b0e8010ff8586e0087fc2c20c043fe160bc021ff0b
  | _ => 0
def ns2_Data4_ : Nat → Nat
  | 0 => 0x5e03d3fcd82f01e1fe6c1780ecff360bc0747f9b05e0393fcd82f01c1fe6c1780dcff360bc06c7f9b05e0353fcd82f01a1fe6e8880ccff363d00667f9b05e0333fcd8258199fe6c1780c8ff360bc0627f9b05e0303fcd82f0179fe6c1780b8ff360bc05a7f9b05e02c3fcd82f0159fe6c1780a8ff360bc0527f9b05e0283fcdd110139fe6c17809cff360bc04c7f9b05e0253fcd82f0121fe6c17808cff360bc0447f9b05e0213fcd82f0101fe6c17807cff360bc03c7f9b05e01d3fcd82f00e1fe6c17806cff360bc0347f9ba210193fcd82f00c9fe6c16c064ff3607c0327f9b0330193fcd82f00c1fe6c17805cff360bc02c7f9b05e0153fcd82f00a1fe6c17804cff360bc0247f9b05e0113fcd82f0081fe6c17803cff360bc01c7f9b05e00d3fcd82f0061fe6c17802cff3603c021fa0b0dc010ff0580f0087f82c050033fc16020019fe0b
  | 1 => 0xa6305e3fcdd1102f1fe6e884178ff374400bc7f9ba1f05e3fcdd0f02f1fe6e874178ff374380bc7f9ba1b05e3fcdd0d02f1fe6e864178ff362c20bc7f9b16005e3fcd8af82f1fe6c578178ff362ba0bc7f9b15c05e3fcd8ad82f1fe6c568178ff3629a0bc7f9b10305e3fcd87b02f1fe6c268178ff360bc0ba7f9b05e05c3fcdd1102d9fe6c33816cff360bc0b67f9b05e05a3fcd82f02c9fe6c178160ff360bc0ae7f9b05e0563fcd82f02a9fe6c178150ff360bc0a67f9b05e0523fcdd110289fe6ccf0144ff360bc0a27f9b05e0503fcd82f0279fe6c178138ff360bc09a7f9b05e04c3fcdd108259fe6c36812cff360bc0967f9b05b04b3fcd82f0251fe6c178124ff360bc0907f9b05e0473fcd82f0231fe6c178114ff360bc0887f9b05e0433fcd82f0211fe6c178104ff360bc0807f9b05e03f3fcdd1101f1fe6c1780f8ff3609607c7f9b
  | 2 => 0xa1d05ebbcdd0e82ddde6e874146ef3743a07d779ba1d033bbcdd0e813dde6e962875ef3744543af79ba1d05e7bcdd0e825bde6c12c129ef3743a032f79b33f0197bcd8258093de6e87e87b9f3744143daf9ba1e05e37cdd5bd0f5be6e88687adf3743c0bd6f9ba1e05bb7cdd0f028dbe6e8780fadf363ee07d6f9b051039b7cdd0f019dbe6e87809edf3744543cef9ba1e05e77cdd0f025bbe6e878065df36680032ef9ba20a1fcfcdd0f82f17e6e88687ebf3743e0bd5f9ba1f05bafcdd0f828d7e6e87c0fabf363f007d5f9ba1f033afcdd0f813d7e6e88a87dbf3743e0bcdf9ba1f04b6fcdd0f80cb7e6cd04065bf374400bc3f9ba7ba209fcdd10d104fe6e88017a7f374400b73f9ba200519fcdd1001f4fe6e8800ce7f3744004f3f9ba22a205fcdd1002f2fe6e88012d7f37440032bf9b3420195fcdd1c5111fe6eb6a884ff374454427f9b
  | 3 => 0x30800cbf4d82f0065fa6c16c032fd360a20197e9b03e00cbf4d8198065fa6c09c032fd37533444fe9ba39a1a7f4dd1150d3fa6e868179fd37434096fe9ba220277f4dd1100f3fa6e868065fd36612032fe9ba2200c7f4d9848063fa6c178031fd36096018fe9b01900c7f4dd0e50dfe66e87686feb3743d437ed9ba1fa1beecdd1050def66e86c178fb375234377d9ba21a1bbecdd0d82f5f66e86c16efb374360a37d9ba1b03ebecdd0d819df66e86c09efb37445436fd9ba1b05e7ecdd0d825bf66e86c065fb3667a032fd9ba1da1cf9cdd0f50e7ae6e87e873b737441439bb9ba1c05e3dcdd7550e5ee6e886872f7374380bd7b9ba1c05bbdcdd0e028dee6e8700faf7374380677b9ba1c027bdcd81f0085ee6e88a871f7374380bcfb9ba1c04b7dcdd0e00cbee6ccf8065f73743d43be79ba1fa1debcdd1050eede6e874178ef3744343b779b
  | 4 => 0xa220197f8dd0c80cbfc6c178065fe360ba032ff1b0190187f8dd110083fc6c7c4041fe360bc020ff1b04b0107f8d80c8063fc6e86e86bf93743604ffc9ba1b01efe4dd0d8067f26eb76873f537439435fa9ba1c027fd4dd0e00f7ea6c10007bf53607203dfa9b02901efd4d80f0087ea6e870033f53743b435f69ba1d027fb4dd0e80f7da6e874033ed3743d435ee9ba1e027f74dd0f00f7ba6e878033dd3743f435de9ba1f027ef4dd0f80f77a6e87c033bd37441435be9ba20027df4dd1000f6fa6e8800337d374340bc7e9b05e00c3f4dd66d10dfa6e8e286afd374434357e9ba1a05ebf4dd0d02ddfa6c31016efd374340a37e9b335051bf4dd0d01f5fa6c7cc0fafd374340677e9b1de033bf4dd10813dfa6e86809efd360bc04f7e9ba2101ebf4d87380f5fa6c17807afd360b603d7e9b05101ebf4d81f00f5fa6c0cc07afd374420197e9b
  | 5 => 0x1e019ff0dd0d0087f86c370043fc3604e021fe1b01e010ff0dd0c8067f86c064033fc36028019fe1b01000cff0d8070067f86e86e867fa37436033fd1b33d019fe8dd0d8087f46eb6e873f637439433fb1ba1c019fd8d99f00cfec6e870043f636082021fb1b03e010fd8d81b8087ec6c078043f63602001ffb1ba1da19fb8dd0e80cfdc6ccfc067ee3743a021f71ba1ea19f78dd0f00cfbc6cd00067de3743c021ef1ba1fa19ef8dd0f80cf7c6cd04067be3743e021df1ba20a19df8dd1000cefc6cd080677e37440021bf1ba1905e3f8dd65d10dfc6ec02866fe374434337f1ba1905ebf8dd0c82ddfc6e864146fe3743207d7f1b1f003ebf8dd0c819dfc6e86409efe374420337f1b05b019bf8dd108085fc6c7c0042fe360b60217f1b03e010bf8d8198085fc6ea62889fe375b5432ff1ba22a197f8dd0c82f3fc6e86412dfe3619e096ff1b
  | 6 => 0x78043f4574320bc7f2ba1a05e3f5582f0061faae86c178fb574380bc7baba1d05e3bd5d0f02f1beae87c178bf574400bc3fab01e010fd0dd7950cff86e86a867fc3743204ffe1ba1901eff0dd0d00cff86cc24067fc3604e033fe1b
  | _ => 0
def ns2_Data (i : Nat) : Nat :=
  match i/32 with
  | 0 => ns2_Data0_ (i % 32)
  | 1 => ns2_Data1_ (i % 32)
  | 2 => ns2_Data2_ (i % 32)
  | 3 => ns2_Data3_ (i % 32)
  | 4 => ns2_Data4_ (i % 32)
  | _ => 0
def ns2_ (i : Nat) : Nat := (ns2_Data (i/64) >>> (41*(i % 64))) &&& 2199023255551
def ns3_Data : Nat → Nat
  | 0 => 0x4624600da2d842c12c002f16c21189180178b61070e67c0bc5b082351fc05e2d8444c19f0f80ec2118d18036876108c68c00bc3b0838833e05e1d8419f0b080c0ec2225a2547c0ce1112a3ee3e0670864864505e33841638bc82f19c2225e2547c0ae1112a3f03e0570846233f0da2b8423119f82f15c216007f8178ae1113112a3e0370846333f0da1b8423199f82f0dc20cfc5840606e1113112c3e02f084634610da1784231a3082f0bc20d005840605e103ee15e03d68884cb17b05e3c4432316182f1b2216048dc178b91099a2f60bc5c881f70b101eb1441d89d800f52a20b18a0c178d5106ce4ca0bc6a8861503901e354422d81c80f1aa20cf00e4078d51099c9960bc3a8836718305e1d4416394182f19a21335330178ad1099c9980bc368858358105e27441b513282f13a21338da41785d10b08b020bc1e884ce4cd05e0f4411d0fd82f07a20da860c1783d10c8ec8c0bc69882c617b05e34c42c111b82f16621921918178cb1058e2f60bc658864964605e26c43238c182f0ae2161160817837104743f80bc1b8864964805e23c43240c182f09e216107f81782f10b08b060bc0f88
  | 1 => 0xc10bf05e27c485a85982f13e248001781549f123f03ee0964f8918105e04327c496402f01693e248e41780909f128d28cc0bc2f8938838605e17c49b59b482f0be24d08d001785f1255254e0bc2f8923a23905e17c490110002f0be246f06e81785f124ca3060bc2f8918305e04317c48c182f01c8be251a519c1783f1271070e0bc1f8936b36a05e0fc49a11a082f07e24aa4aa01783f12b084940bc1f891bc1bb05e0fc48c18c082f07e248e81780ec3f124740bc05c1f8923a05e0240fc48f805780f5e0222510f07c0f8108be8bc1b47c0845f45e05e3e040f805880f5c820ec0e3407ad4103e016603d6a081f70ab01eb5041d89c680f568210f0cf87c0f4108c08bc1b47a0889543c1f03b0426626502f1d8222590f07c0dc108783ee3e06e0846145e0da3704230a2f02f1b821914b0c178dc1112e8783e05e0843c1f81f02f042c0ac002f178208d47ec178bc111308783e03e0889433e1f03c8423022f86d1e42118117c178f21112b1283e075088978941f02e8423122f86d1742118917c178ba1112a67c3e0730846033f0da3984230a3006d1ac2191d914178d61058c2f20bc6b08
  | 2 => 0x33c03d03935c496302f0169ae24b18178084d71267807203c6b892c605e01435c49c39c282f16e24da8d9c178b71268267c0bc5b892c82c605e2dc495415202f16e25608928178b71231e3160bc5b8918117d05e2dc48fe02f02a96e247f0178110b7123f80bc02c5b8938838505e1dc49b59b382f0ee24d08cf817877125525480bc3b8923a23805e1dc49010fe02f0ee2460c5f417877128cc8ca0bc678936936805e33c49a019f82f19e24a9ca98178cf12c904ca0bc67892001fe05e33c48dd0dc02f19e242cc2c4178cf1258e0bc0a467892c705e02d33c496382f01099e24b1c178050cf128ce8ca0bc578936a36805e2bc49a099f82f15e24b20b1c178af1255054c0bc578924a1fe05e2bc48dd8dc02f15e246045fc178af1216a1620bc57891fe05e0552bc48fc0fb02595e247f8178058af128d28ca0bc378936b36805e1bc49a119f82f0de24aa4a981786f124043fc0bc37891bc1b805e1bc48c18bf82f0de2519d1981789f1270e70c0bc4f8936a36905e27c49a09a002f13e24aa0a9c1789f12c924ca0bc4f8958324a05e27c48fc0fb82f13e246ec6e81789f1231e31a0bc4f89
  | 3 => 0x4ce28305e1f4491d11b02f0fa248087ec1787d1237836c0bc3e8946908f05e1f448c182f0120fa2460c1780787d123060bc0363e8938538405e3cc499f19e82f1e624b18b14178f3125485460bc798923823705e3cc48c58c502f1e6245f45ec178f3128ca8c80bc758933f33d05e3ac496396282f1d624a98a8c178eb122fe2f60bc75890b10af05e3ac4a3323202f1b624e18e10178db1268067a0bc6d892a72a305e36c4b2313282f1b6248e48dc178db1231a3140bc6d890b30af05e36c48bd82f0271b6245ec17810cdb122f60bc0726d8946746405e2ec49c39c202f17624d04cf4178bb1259058a0bc5d892a82a305e2ec492511b82f1762463c628178bb123022f60bc5d890b50af05e2ec491b82f01d976248dc178090bb128d28c80bc3d8938838405e1ec49a119e82f0f624aa4a8c1787b1247446e0bc3d8918317b05e1ec49b41b382f1ce24cfccf8178e71258e58c0bc73892a62a405e39c48ff0fe02f1ce245fc5f4178e71270c70a0bc6b8936936705e35c49a019f02f1ae24a9ca90178d712c8e4ca0bc6b8923923805e35c49000fe02f1ae2463462c178d71258c0bc0a46b89
  | 4 => 0x33c03901e75449d886300f56a24e14e0c178f51267c6120bc7a892c62c305e3d44a6594182f1ea248e08d8178f5123f83f60bc7a8918b18805e3d449b382f0131ea24d9c178084f51267807203c7a8933c02901e3d4499e00f0081ea24cfcc24178ed1258e5860bc76894cc28305e3b448ff0fd82f1da246e06d8178ed1216215a0bc768946508f05e3b449b402f0131da245fc178090ed123f03ee3e74e891f81f701ea7448fc0fb80653a24e18e0c178dd126806120bc6e8936928305e374496193282f1ba248e48d8178dd124003f60bc6e891ba1b605e37448c68c402f1ba242cc2b4178dd128cc11e0bc6e8928305e04e37448fb8f98259ba24a0c17810cdd125060bc0726e892c305e02d37449b482f0131ba24994178090dd125b00bc03c6e8926505e01e374499e01c80f1ba2499417806cdd125860bc0286e8938738305e2f449a098482f17a24b20b0c178bd1299a5060bc5e8958124a05e2f448dd8db02f17a2463c620178bd1216a15a0bc5e8946708f05e2f448fd82f02a97a247ec178110bd126d40bc04c5e8936a05e0212f448fd82f00b17a24e20e0c1787d126846120bc3e89
  | 5 => 0x89743e1f02f84a1f0fc0f817c2518836833cbe126d46cc0bc5f092c82c205e2f84ac012502f17c2519c7c0178be123f03e00bc5f091bb1b405e2f848c78c302f17c246045e4178be128c419e0bc5f090b50ab05e2f848fc0f802597c248d41780ecbe1246a0bc05c5f0923505e0242f849c382f00c97c24e1c178040be1313087c3e03f094630da0cf1f849b59b302f0fc248e88d41787e124043f40bc3f094691f005e1f848de0da02f0fc2460c5e41787e128c619e0bc3f0938805e0191f848b080c80c0fc24e201780407e122f607203de8890af03e01ebc448ad01480f5e224e10e0c178f91267a6120bc7c892c52c305e3e4491b91b02f1f224628620178f9125062f60bc7c890af0ad05e3e44a3204782f1f2245ec178090f9122f60bc03c7c890b103e01eb9448c181c80f6aa24cf00e4078d51276018c03d6a893b005b01eb54485981f00f5aa247dc0f007ad512bb607203d6a895b703901eb544aa001c80f5aa24cf00e407ad5123ee07203d6a891e403901eb5448ae81c80f5aa244100e407ad51219607203d6a8905103901eb5448fb81b80f5aa247dc0a407ad5123ee03c0216a89
  | 6 => 0x33e1f11f03d84a3006d0679ec24d9cd98178f61258c5840bc7b0923823505e3d848fe0fd02f1ec2462c618178f6122fa2f20bc7b094600cf05e3d84c4ea300259ec2518036812cf6128c00b60967b0946004b0333d8499f02f00c1ec24cf8178058f61267c0bc0227b093cb0da0103d8486d06a0081ec24368104040f6121b406e0207b090da01e0103d84a3119f825b5c2518812c049ae128c667e096b70933f05d0185b84a318258092dc262550f87c0ee1267e1b419e770936836605e3b8496396102f1dc247f87e8178ee128ca3e00bc77091b81b405e3b848bf8bc82f1dc24cfc33c178ee121621560bc77094b11f004b3b848fb0f80259dc262547c00f8ee1267e0bc030770933f05e0163b848f80258091dc262547c0040ee123f03ee3e14f0946346104b57849a002e80c2bc262590f87c0de1287c3ee3e06f094610da0cf37849b49b302f1bc25914994178de1247246a0bc6f092001fa05e3784a330f802f1bc247dc7c0178de123743680bc6f0918d18605e3784a3086782f1bc242cc2ac178de122f20bc09c6f091f71f004b37848bc82f0219bc245e41780e4de126800bc0306f09
  | 7 => 0x20401e0107d048df00f0083e824648078041f41217003c020fa0946004b00c7d0496380a00679824eb07dc7c2dc123ee3e63e16e091f71f001eb704a0b8fb8065b8247dc7c0032dc123ee0280196e0915d01400cb7048fb8070065b82518517812ddc128c2096018ee092ca01400c77049d60fc0f8578247e07cc7c2bc123f03e003d5e091f81f000caf04a1f21e0f81f8250f0eb07c0fc128783e23e07e0943c1f00dc3f04a2f06d0679f824b0cb08178fc129945060bc7e0923623505e3f048fd8fd02f1f8246d86d0178fc1231030c0bc7e0945e0cf05e3f0485685582f1f8247c023c178fc127583e00967e091f31f004b3f04a1e0f801f1f8253f10f0040fc128783e00207e0943c05b0103f04a1e0198081f8247c012c030fc128c08be096f90946245f04b6e84c4a21f0f81f42517c36833cfa1258a5840bc7d0923723505e3e84a320f802f1f424628618178fa122f62f20bc7d0945f0cf05e3e8485785582f1f424cf4178058fa127080bc0207d0946033f04b7984a300258093cc245700dc041e6128c28c0096eb0946246004b6d84a31a30025aec24cf8174061761287c67c3e07b09
  | 8 => 0x20201e010dd048de00f0086e82460c07804374123e01b806f7a092a41f001ebd048f80f780f5e8247c055007af4123e022a03d7a091f010601ebd049c686300f5e824e3416c07af41215607c03d7a091f003c01ebd048f801c80f5e8247c00dc07af4123e005203d7a09c0301e010bd04d7500f0085e826a44078042f4134f603c0217a0962d01e010bd04ac880f0085e825524078042f4129f803c0217a094b501e010bd04a5780f0085e82528c078042f41285203c0217a0942501e010bd049ee80f0085e824e54078042f41271a03c0217a0938101e010bd0498000f0085e824be0078042f4125d203c0217a092e201e010bd0496480f0085e824a84078042f41247803c0217a0920301e010bd048f800f0085e8246f4078042f41232203c0217a0912c01e010bd0488200f0085e824368078042f41216e03c0217a0906c01e010bd0482d80f0085e8240cc078042f4128c08bc096fa0943c3f70107d04a1e19f0083e8250f0104041f41287806e020fa09b2501e0107d04b1c80f0083e8250f0078041f41270403c020fa0935f01e0107d0499e00f0083e824b28078041f41247a03c020fa09
  | 9 => 0x33c03901e354cbdd00f0087e024e10078043f01267a03c021f8092c501e010fc0495180f0087e0248dc078043f01231403c021f80917b01e010fc0485780f0087e024568038032f8128be8bc096fc0945f04b00c7e04b1480f0087c824da0078043e41267e03c021f2092c701e010f90495300f0087c8247f8078043e41237003c021f20917f01e010f90485880f0087c8254fc0e407bd4122f207203dea096e301e010f504b1500f0087a8255e8078043d41270c03c021ea0937e01e010f5049b480f0087a824d00078043d4125b003c021ea092a701e010f50493280f0087a8248e4078043d41240003c021ea091f701e010f5048dd00f0087a824634078043d41217e03c021ea090b301e010f50496300a0067a825b90078043b412c5603c021da0954801e010ed049c380f00876824da8078043b41268203c021da092e101e010ed0496400f00876824aa0078043b41249403c021da091f801e010ed048dd80f0087682463c078043b41230203c021da090c101e010ed0485a80f008768258b0078043741271003c021ba0936b01e010dd049a100f0086e824aa4078043741247403c021ba09
  | 10 => 0x36905e01b37c51a002f00c9be28574178050df140bc0a60286f8a05e04e01437c502f02180a1be281780e4050df140bc0440286f8a38605e01137c505f82f0079be28a9c17802cdf148ce1340bc5f8a2c805e04e2fc502f02a82697e2863c178118bf140bc0aa08a5f8a1f805e03e2fc50fc02581f17e282d41780f0bf142be0bc0765f8a05e05703b2fc502f02a81d97e281781100ecbf140bc07605e5f8a05e05502e2fc502f02201717e289281780acbf143760bc0505f8a2e105e0252fc502f02a81217e28178134090bf140bc0880485f8a05e02f0242fc50c082f01097e28da817806cbf146820bc0325f8a15f05e0162fc502f02c80b17e28178114058bf140bc07602c5f8a05e02e0162fc502f01200b17e28e1c178044bf141820bc01e5f8a2a805e00b2fc523484d02f0fe2817815411c7f144740bc0883f8a16105e03d1fc502f02a8188fe281780f40c47f144040bc05c3f8a1bc05e0281fc502f0278130fe281780c40987f143060bc0423f8a36b05e01b1fc51a102f00c8fe285841780607f140bc0ba0303f8a05e0470181fc502f01300c0fe28e201780447f145520bc0163f8a
  | 11 => 0x17d05e0213dc502f01c80f1ee281780a4078f7146ce0bc0367b8a33e05e0193dc51c282f0089ee2856c178040f7140bc0820207b8a05e0370103dc502f00f0081ee28a9017802cf7148ca1340bc778a2c705e04e3bc502f0238219de287d812c0f8ef141620bc078778a15c05e0373bc502f02381b9de287f81780b8ef140bc08a056778a05e03702b3bc50dc02f0141de285fc178084ef140bc086040778a05e02b0203bc51b402f00d9de28cfc178064ef142b80bc024778a0da04b0123bc502f0258091de2816c12c048ef1409607c024778a04b0330123bc502f0100091de28a9817802cef143f03ee07d4f8a46609a05e37c516c02f02e9be28178148138df1431a0bc08c6f8a23905e04437c502f0290219be2817813c10cdf140bc09a0866f8a1f705e03e37c50fb82581f1be282cc1780f0df142ba0bc0726f8a05e05203937c519e02881c9be281781440e4df140bc09e0726f8a20005e02e37c502f0270169be281781340b4df140bc08605a6f8a05e03902d37c51bf02f0151be286e81780a0df144ca0bc04c6f8a05e02d02237c502f0270109be2817810c084df140bc0720426f8a
  | 12 => 0x18805e0463f4511b02f0221fa2823c178100fd143e609607c7e8a0ad05e03c3f450fd82f0171fa28a0c1780b4fd1436c0bc0507e8a05e0260243f4502f0130111fa28178090084fd140bc04c0407e8a05e0240203f4504782f00f1fa28178174078fd140bc0a403c7e8a33c05101e3f4502f01a80f1fa28178098078fd140bc04203c7e8a05e02401c3f4502f00f00e1fa2817809806cfd140bc0420367e8a30905e0193f451c182f0089fa2a884178030fd154320bc0187e8a30905e00c3f4506d0258061fa2817812c030fd140b60960187e8a04b03e00c3f450258198061fa28178080030fd148c81340bc7d8a2c505e04e3ec50c502f0231f6288dc178110fb1415e0bc0787d8a05e03102d3ec502f0188159f6281780bc0acfb142b40bc0527d8a05e0310293ec50bd82f0109f6281780b4070fb1467a0bc0327d8a38405e0113ec50ad02f0071f6281780d4038fb140bc05601c7d8a05e01c00e3ec515182f0059f6281440f40e6d7140a207203d6b8a2c605e04e3dc50c582f0231ee288e0178110f7140bc07a0727b8a05e03d0373dc502f01d81b9ee287f01780b8f7140bc0760527b8a
  | 13 => 0xce05b0103f8502f02d8081fc2817815c040fe143e00960207f0a0da04b0103f8502d8258081fc28178120040fe143e20660207f0a1e80330103f8502f0198081fc2812c0cc040fe140bc0300207f0a05e0160103f8502f0088081fc28178058038fe140bc02001c7f0a05e01400c3f8502f0070061fc280c40a407bf1140a207203d6a8a0e103901ef54502901c80f7aa281440e407bd51409e07203dea8a03902d01ef54501c81080f7aa280e4078053d51418c0b603d7a8a03e03c01ebd4508801c80f5ea2839c0e407af5140bc07203d7a8a05b03901ebd4502881c80f5ea280f80e407af51407c06e03d7a8a03903301ebd4508e81480f5ea2839c0a407af5140bc05203d7a8a05b02901ebd4502881480f5ea280f80a407af51406605203d7a8a1f001e010bd4507380f0085ea28178078042f5140b603c0217a8a05101e010bd4501f00f0085ea280cc078042f514096024018f68a1f71f303eb7450fb81f00f5ba281440e407add143ee07c0196e8a05103900cb7450fc0f981f57a287e00f807abd143f007c0195e8aaf2a1905e3f4504d04782f1fa28bec178150fd145860bc09c7e8a
  | 14 => 0x1f0041010bd8502d8208085ec287c00dc042f6140b606e0217b0a041033010bd8501b8198085ec287c0078042f6140b603c0217b0a03301e010bd85230067825bec28cf87c4041f6142b60bc020fb0a0d404b0107d850f88208083ec28178104041f6140ba082020fb0a04b0410107d850f881b8083ec281780dc041f61409606e020fb0a0410350107d850f880f0083ec28178078041f61409603c020fb0a33f0cf04b7b850678258093dc2812c060049ee1409602c024f70a04b0120107b850fb8f801f5bc2918433c12dde143f03e007d5f0a4620cf04b6f85231867825afc281740640617e142b819e0bc7f0a1f009a05e3f8516102f0271fc2836833c12cfe1419e0bc0967f0a0cf05b04b3f850c302f0231fc288d4178110fe1487c3e007c7f0a1f005e03e3f850f802581f1fc2833c12c0f8fe141560bc0787f0a16205e03a3f850678258199fc287e81780b8fe143680bc0507f0a17905e0213f851b302f00d9fc28178064060fe140bc03202c7f0a05e0180143f8502f00c0091fc28178058048fe140bc0320227f0a43e1f00103f850f88f80081fc287c0178040fe143e20b60207f0a
  | 15 => 0x2101e010fd0501000f0087e82807c078043f41403c03a021fa0a01e01c010fd0500f00d8087e828078068043f41403c032021fa0a01e018010fd0500f00b8087e828078058043f41403c02a021fa0a01e014010fd0500f0098087e828078048043f41403c022021fa0a01e01000ffd0500f0080077e828078040037f414082020019fa0a03701000cfd0500f0080067e82807804002ff4140a6028019ee0a04e01400cf70502180a0067b8280e4050033dc14044028019ee0a3ac1f003ebf050f98f801f5f8287c00f807afc147583e00217e0a4fc0dc010bf050f806e0085f82837016c042fc141b80660217e0a1f001e010bf0502d80f0085f8280cc078042fc143e007c0197e0a05e01400cbf0502d80a0065f828144050032fc1407c0280197e0a03301400cbf050f80080065f82816c040032fc140a20200197e0a03301000cbf0502f0070065f82816c038032fc140a201c0197e0a03e00e00cbf050198070065f82917833c12dfc148783e2020fe0a43c0dc0107f050678258063f82812c050031fc14096020018fe0a04b00e00c7f0522f867825bf42811c0dc043e61406e056021f30a
  | 16 => 0xdb01e010fd0504780f0087e82820c078043f4140bc03c021fa0a05d01e010fd0502e00f0087e82816c078043f4140b403c021fa0a05901e010fd0502c00f0087e82815c078043f4140ac03c021fa0a05501e010fd0502a00f0087e82814c078043f4140a403c021fa0a05101e010fd0502800f0087e82813c078043f41409c03c021fa0a04d01e010fd0502600f0087e82812c078043f41409403c021fa0a04901e010fd0502400f0087e82811c078043f41408c03c021fa0a04501e010fd0502200f0087e82810c078043f41408403c021fa0a04101e010fd0502000f0087e8280fc078043f41407c03c021fa0a03d01e010fd0501e00f0087e8280ec078043f41407403c021fa0a03901e010fd0501c00f0087e8280dc078043f41406c03c021fa0a03501e010fd0501a00f0087e8280cc078043f41406403c021fa0a03101e010fd0501800f0087e8280bc078043f41405c03c021fa0a02d01e010fd0501600f0087e8280ac078043f41405403c021fa0a02901e010fd0501400f0087e82809c078043f41404c03c021fa0a02501e010fd0501200f0087e82808c078043f41404403c021fa0a
  | 17 => 0xa1f05e00c2f4d51050d02f0fa6a8801780307d354394360bc799aa1da1b05e3acd50f50d82f1b66a87e86c178bb354414360bc3d9aa1da1c05e39cd50f50e02f1ae6a87e870178b7354414380bc3b9aa1ea1d05e33cd50fd0e82f15e6a8828741786f3543f43c0bc4f9aa20a1e05e17cd51050f82f07e680d4038033f81405601c019fc0a01c00e00cfe050f800f0085e82816c078042f41406603c0217a0a0dc041010fd0506e01b8087e82aaec078043f41548c03c021fa0aa2201e010fd0551080f0087e82a880078043f41543e03c021fa0aa1e01e010fd0550e80f0087e82a870078043f41543603c021fa0aa1a01e010fd0550c80f0087e828a90078043f4143e203c021fa0a1f001e010fd050f780f0087e8287b8078043f4143da03c021fa0a1ec01e010fd050f580f0087e8287a8078043f4143d203c021fa0a15401e010fd0508a80f0087e828418078043f4141d003c021fa0a0e701e010fd0507300f0087e828394078043f4141c803c021fa0a0e301e010fd0507100f0087e828384078043f4141c003c021fa0a0df01e010fd0506f00f0087e828374078043f4141b803c021fa0a
  | 18 => 0x50d80f0087e06a874078043e43543c03c021ea1aa1f01e010ed0d51000f0086e86a884078042f4343e003c0217a1a0e701e010bd0d02d80f0085e8680cc078042f43544403c020fa1a1f101e0107d0d57950c82f1f86a86a864178fc354320bc0187e1aa1ba1905e3e8d50e50c82f1ec6a876864178ee3543d4320bc6f1aa1fa1905e2f8d51050c82f0fc6a86e868178f9354360bc0187c9a05103901eb54d50e50d02f1ea6a870178030f53543b4340bc769aa1d05e00c3b4d50f50d02f1ba6a878178030dd3543f4340bc5e9a
  | _ => 0
def ns3_ (i : Nat) : Nat := (ns3_Data (i/64) >>> (53*(i % 64))) &&& 9007199254740991
def ns4_Data : Nat → Nat
  | 0 => 0xbc0a407203c6a8933c05103901e354482f01c81080f1aa245ec1780e4078d1103060bc07203c2a88
  | _ => 0
def ns4_ (i : Nat) : Nat := (ns4_Data (i/64) >>> (65*(i % 64))) &&& 36893488147419103231
def nodeData (i : Nat) : Nat × Nat :=
  if i < 7 then (0,ns0_ (i-0))
  else if i < 4186 then (1,ns1_ (i-7))
  else if i < 12780 then (2,ns2_ (i-4186))
  else if i < 13963 then (3,ns3_ (i-12780))
  else (4,ns4_ (i-13963))
def node (i : Nat) : Node :=
  let (n,z) := nodeData i
  ⟨z &&& 15,(z >>> 4) &&& 7,retained ((z >>> 7) &&& 1023) signals ++ extra n (z >>> 17)⟩
def hint (k t : Nat) (w : List Wire) : Nat :=
  let lane := (hash 7 w k t) % 4096
  let slot := ((hash 43 w k t)+shifts lane) % 16384
  let c := slotCode slot
  4*c
def table : Table := ⟨13968,hint,node⟩
end PEqualNP.Outside.L_meta_3561.Normal

namespace PEqualNP.Outside.L_meta_3561.Normal
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
theorem c0 : span (bulkNode table) 32 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c32 : span (bulkNode table) 32 32 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c64 : span (bulkNode table) 32 64 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c96 : span (bulkNode table) 32 96 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c128 : span (bulkNode table) 32 128 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c160 : span (bulkNode table) 32 160 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c192 : span (bulkNode table) 32 192 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c224 : span (bulkNode table) 32 224 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c256 : span (bulkNode table) 32 256 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c288 : span (bulkNode table) 32 288 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c320 : span (bulkNode table) 32 320 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c352 : span (bulkNode table) 32 352 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c384 : span (bulkNode table) 32 384 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c416 : span (bulkNode table) 32 416 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c448 : span (bulkNode table) 32 448 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c480 : span (bulkNode table) 32 480 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c512 : span (bulkNode table) 32 512 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c544 : span (bulkNode table) 32 544 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c576 : span (bulkNode table) 32 576 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c608 : span (bulkNode table) 32 608 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c640 : span (bulkNode table) 32 640 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c672 : span (bulkNode table) 32 672 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c704 : span (bulkNode table) 32 704 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c736 : span (bulkNode table) 32 736 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c768 : span (bulkNode table) 32 768 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c800 : span (bulkNode table) 32 800 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c832 : span (bulkNode table) 32 832 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c864 : span (bulkNode table) 32 864 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c896 : span (bulkNode table) 32 896 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c928 : span (bulkNode table) 32 928 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c960 : span (bulkNode table) 32 960 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c992 : span (bulkNode table) 32 992 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1024 : span (bulkNode table) 32 1024 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1056 : span (bulkNode table) 32 1056 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1088 : span (bulkNode table) 32 1088 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1120 : span (bulkNode table) 32 1120 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1152 : span (bulkNode table) 32 1152 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1184 : span (bulkNode table) 32 1184 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1216 : span (bulkNode table) 32 1216 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1248 : span (bulkNode table) 32 1248 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1280 : span (bulkNode table) 32 1280 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1312 : span (bulkNode table) 32 1312 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1344 : span (bulkNode table) 32 1344 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1376 : span (bulkNode table) 32 1376 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1408 : span (bulkNode table) 32 1408 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1440 : span (bulkNode table) 32 1440 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1472 : span (bulkNode table) 32 1472 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1504 : span (bulkNode table) 32 1504 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1536 : span (bulkNode table) 32 1536 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1568 : span (bulkNode table) 32 1568 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1600 : span (bulkNode table) 32 1600 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1632 : span (bulkNode table) 32 1632 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1664 : span (bulkNode table) 32 1664 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1696 : span (bulkNode table) 32 1696 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1728 : span (bulkNode table) 32 1728 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1760 : span (bulkNode table) 32 1760 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1792 : span (bulkNode table) 32 1792 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1824 : span (bulkNode table) 32 1824 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1856 : span (bulkNode table) 32 1856 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1888 : span (bulkNode table) 32 1888 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1920 : span (bulkNode table) 32 1920 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1952 : span (bulkNode table) 32 1952 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c1984 : span (bulkNode table) 32 1984 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2016 : span (bulkNode table) 32 2016 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2048 : span (bulkNode table) 32 2048 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2080 : span (bulkNode table) 32 2080 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2112 : span (bulkNode table) 32 2112 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2144 : span (bulkNode table) 32 2144 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2176 : span (bulkNode table) 32 2176 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2208 : span (bulkNode table) 32 2208 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2240 : span (bulkNode table) 32 2240 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2272 : span (bulkNode table) 32 2272 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2304 : span (bulkNode table) 32 2304 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2336 : span (bulkNode table) 32 2336 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2368 : span (bulkNode table) 32 2368 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2400 : span (bulkNode table) 32 2400 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2432 : span (bulkNode table) 32 2432 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2464 : span (bulkNode table) 32 2464 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2496 : span (bulkNode table) 32 2496 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2528 : span (bulkNode table) 32 2528 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2560 : span (bulkNode table) 32 2560 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2592 : span (bulkNode table) 32 2592 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2624 : span (bulkNode table) 32 2624 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2656 : span (bulkNode table) 32 2656 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2688 : span (bulkNode table) 32 2688 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2720 : span (bulkNode table) 32 2720 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2752 : span (bulkNode table) 32 2752 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2784 : span (bulkNode table) 32 2784 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2816 : span (bulkNode table) 32 2816 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2848 : span (bulkNode table) 32 2848 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2880 : span (bulkNode table) 32 2880 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2912 : span (bulkNode table) 32 2912 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2944 : span (bulkNode table) 32 2944 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c2976 : span (bulkNode table) 32 2976 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3008 : span (bulkNode table) 32 3008 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3040 : span (bulkNode table) 32 3040 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3072 : span (bulkNode table) 32 3072 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3104 : span (bulkNode table) 32 3104 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3136 : span (bulkNode table) 32 3136 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3168 : span (bulkNode table) 32 3168 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3200 : span (bulkNode table) 32 3200 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3232 : span (bulkNode table) 32 3232 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3264 : span (bulkNode table) 32 3264 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3296 : span (bulkNode table) 32 3296 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3328 : span (bulkNode table) 32 3328 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3360 : span (bulkNode table) 32 3360 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3392 : span (bulkNode table) 32 3392 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3424 : span (bulkNode table) 32 3424 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3456 : span (bulkNode table) 32 3456 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3488 : span (bulkNode table) 32 3488 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3520 : span (bulkNode table) 32 3520 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3552 : span (bulkNode table) 32 3552 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3584 : span (bulkNode table) 32 3584 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3616 : span (bulkNode table) 32 3616 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3648 : span (bulkNode table) 32 3648 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3680 : span (bulkNode table) 32 3680 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3712 : span (bulkNode table) 32 3712 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3744 : span (bulkNode table) 32 3744 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3776 : span (bulkNode table) 32 3776 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3808 : span (bulkNode table) 32 3808 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3840 : span (bulkNode table) 32 3840 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3872 : span (bulkNode table) 32 3872 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3904 : span (bulkNode table) 32 3904 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3936 : span (bulkNode table) 32 3936 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c3968 : span (bulkNode table) 32 3968 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4000 : span (bulkNode table) 32 4000 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4032 : span (bulkNode table) 32 4032 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4064 : span (bulkNode table) 32 4064 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4096 : span (bulkNode table) 32 4096 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4128 : span (bulkNode table) 32 4128 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4160 : span (bulkNode table) 32 4160 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4192 : span (bulkNode table) 32 4192 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4224 : span (bulkNode table) 32 4224 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4256 : span (bulkNode table) 32 4256 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4288 : span (bulkNode table) 32 4288 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4320 : span (bulkNode table) 32 4320 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4352 : span (bulkNode table) 32 4352 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4384 : span (bulkNode table) 32 4384 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4416 : span (bulkNode table) 32 4416 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4448 : span (bulkNode table) 32 4448 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4480 : span (bulkNode table) 32 4480 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4512 : span (bulkNode table) 32 4512 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4544 : span (bulkNode table) 32 4544 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4576 : span (bulkNode table) 32 4576 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4608 : span (bulkNode table) 32 4608 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4640 : span (bulkNode table) 32 4640 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4672 : span (bulkNode table) 32 4672 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4704 : span (bulkNode table) 32 4704 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4736 : span (bulkNode table) 32 4736 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4768 : span (bulkNode table) 32 4768 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4800 : span (bulkNode table) 32 4800 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4832 : span (bulkNode table) 32 4832 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4864 : span (bulkNode table) 32 4864 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4896 : span (bulkNode table) 32 4896 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4928 : span (bulkNode table) 32 4928 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4960 : span (bulkNode table) 32 4960 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c4992 : span (bulkNode table) 32 4992 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5024 : span (bulkNode table) 32 5024 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5056 : span (bulkNode table) 32 5056 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5088 : span (bulkNode table) 32 5088 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5120 : span (bulkNode table) 32 5120 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5152 : span (bulkNode table) 32 5152 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5184 : span (bulkNode table) 32 5184 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5216 : span (bulkNode table) 32 5216 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5248 : span (bulkNode table) 32 5248 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5280 : span (bulkNode table) 32 5280 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5312 : span (bulkNode table) 32 5312 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5344 : span (bulkNode table) 32 5344 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5376 : span (bulkNode table) 32 5376 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5408 : span (bulkNode table) 32 5408 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5440 : span (bulkNode table) 32 5440 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5472 : span (bulkNode table) 32 5472 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5504 : span (bulkNode table) 32 5504 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5536 : span (bulkNode table) 32 5536 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5568 : span (bulkNode table) 32 5568 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5600 : span (bulkNode table) 32 5600 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5632 : span (bulkNode table) 32 5632 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5664 : span (bulkNode table) 32 5664 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5696 : span (bulkNode table) 32 5696 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5728 : span (bulkNode table) 32 5728 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5760 : span (bulkNode table) 32 5760 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5792 : span (bulkNode table) 32 5792 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5824 : span (bulkNode table) 32 5824 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5856 : span (bulkNode table) 32 5856 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5888 : span (bulkNode table) 32 5888 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5920 : span (bulkNode table) 32 5920 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5952 : span (bulkNode table) 32 5952 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c5984 : span (bulkNode table) 32 5984 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6016 : span (bulkNode table) 32 6016 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6048 : span (bulkNode table) 32 6048 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6080 : span (bulkNode table) 32 6080 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6112 : span (bulkNode table) 32 6112 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6144 : span (bulkNode table) 32 6144 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6176 : span (bulkNode table) 32 6176 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6208 : span (bulkNode table) 32 6208 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6240 : span (bulkNode table) 32 6240 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6272 : span (bulkNode table) 32 6272 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6304 : span (bulkNode table) 32 6304 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6336 : span (bulkNode table) 32 6336 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6368 : span (bulkNode table) 32 6368 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6400 : span (bulkNode table) 32 6400 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6432 : span (bulkNode table) 32 6432 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6464 : span (bulkNode table) 32 6464 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6496 : span (bulkNode table) 32 6496 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6528 : span (bulkNode table) 32 6528 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6560 : span (bulkNode table) 32 6560 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6592 : span (bulkNode table) 32 6592 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6624 : span (bulkNode table) 32 6624 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6656 : span (bulkNode table) 32 6656 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6688 : span (bulkNode table) 32 6688 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6720 : span (bulkNode table) 32 6720 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6752 : span (bulkNode table) 32 6752 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6784 : span (bulkNode table) 32 6784 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6816 : span (bulkNode table) 32 6816 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6848 : span (bulkNode table) 32 6848 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6880 : span (bulkNode table) 32 6880 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6912 : span (bulkNode table) 32 6912 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6944 : span (bulkNode table) 32 6944 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6976 : span (bulkNode table) 32 6976 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7008 : span (bulkNode table) 32 7008 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7040 : span (bulkNode table) 32 7040 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7072 : span (bulkNode table) 32 7072 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7104 : span (bulkNode table) 32 7104 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7136 : span (bulkNode table) 32 7136 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7168 : span (bulkNode table) 32 7168 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7200 : span (bulkNode table) 32 7200 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7232 : span (bulkNode table) 32 7232 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7264 : span (bulkNode table) 32 7264 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7296 : span (bulkNode table) 32 7296 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7328 : span (bulkNode table) 32 7328 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7360 : span (bulkNode table) 32 7360 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7392 : span (bulkNode table) 32 7392 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7424 : span (bulkNode table) 32 7424 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7456 : span (bulkNode table) 32 7456 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7488 : span (bulkNode table) 32 7488 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7520 : span (bulkNode table) 32 7520 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7552 : span (bulkNode table) 32 7552 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7584 : span (bulkNode table) 32 7584 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7616 : span (bulkNode table) 32 7616 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7648 : span (bulkNode table) 32 7648 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7680 : span (bulkNode table) 32 7680 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7712 : span (bulkNode table) 32 7712 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7744 : span (bulkNode table) 32 7744 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7776 : span (bulkNode table) 32 7776 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7808 : span (bulkNode table) 32 7808 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7840 : span (bulkNode table) 32 7840 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7872 : span (bulkNode table) 32 7872 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7904 : span (bulkNode table) 32 7904 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7936 : span (bulkNode table) 32 7936 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7968 : span (bulkNode table) 32 7968 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8000 : span (bulkNode table) 32 8000 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8032 : span (bulkNode table) 32 8032 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8064 : span (bulkNode table) 32 8064 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8096 : span (bulkNode table) 32 8096 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8128 : span (bulkNode table) 32 8128 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8160 : span (bulkNode table) 32 8160 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8192 : span (bulkNode table) 32 8192 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8224 : span (bulkNode table) 32 8224 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8256 : span (bulkNode table) 32 8256 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8288 : span (bulkNode table) 32 8288 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8320 : span (bulkNode table) 32 8320 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8352 : span (bulkNode table) 32 8352 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8384 : span (bulkNode table) 32 8384 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8416 : span (bulkNode table) 32 8416 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8448 : span (bulkNode table) 32 8448 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8480 : span (bulkNode table) 32 8480 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8512 : span (bulkNode table) 32 8512 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8544 : span (bulkNode table) 32 8544 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8576 : span (bulkNode table) 32 8576 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8608 : span (bulkNode table) 32 8608 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8640 : span (bulkNode table) 32 8640 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8672 : span (bulkNode table) 32 8672 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8704 : span (bulkNode table) 32 8704 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8736 : span (bulkNode table) 32 8736 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8768 : span (bulkNode table) 32 8768 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8800 : span (bulkNode table) 32 8800 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8832 : span (bulkNode table) 32 8832 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8864 : span (bulkNode table) 32 8864 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8896 : span (bulkNode table) 32 8896 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8928 : span (bulkNode table) 32 8928 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8960 : span (bulkNode table) 32 8960 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8992 : span (bulkNode table) 32 8992 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9024 : span (bulkNode table) 32 9024 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9056 : span (bulkNode table) 32 9056 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9088 : span (bulkNode table) 32 9088 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9120 : span (bulkNode table) 32 9120 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9152 : span (bulkNode table) 32 9152 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9184 : span (bulkNode table) 32 9184 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9216 : span (bulkNode table) 32 9216 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9248 : span (bulkNode table) 32 9248 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9280 : span (bulkNode table) 32 9280 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9312 : span (bulkNode table) 32 9312 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9344 : span (bulkNode table) 32 9344 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9376 : span (bulkNode table) 32 9376 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9408 : span (bulkNode table) 32 9408 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9440 : span (bulkNode table) 32 9440 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9472 : span (bulkNode table) 32 9472 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9504 : span (bulkNode table) 32 9504 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9536 : span (bulkNode table) 32 9536 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9568 : span (bulkNode table) 32 9568 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9600 : span (bulkNode table) 32 9600 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9632 : span (bulkNode table) 32 9632 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9664 : span (bulkNode table) 32 9664 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9696 : span (bulkNode table) 32 9696 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9728 : span (bulkNode table) 32 9728 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9760 : span (bulkNode table) 32 9760 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9792 : span (bulkNode table) 32 9792 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9824 : span (bulkNode table) 32 9824 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9856 : span (bulkNode table) 32 9856 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9888 : span (bulkNode table) 32 9888 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9920 : span (bulkNode table) 32 9920 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9952 : span (bulkNode table) 32 9952 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9984 : span (bulkNode table) 32 9984 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10016 : span (bulkNode table) 32 10016 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10048 : span (bulkNode table) 32 10048 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10080 : span (bulkNode table) 32 10080 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10112 : span (bulkNode table) 32 10112 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10144 : span (bulkNode table) 32 10144 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10176 : span (bulkNode table) 32 10176 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10208 : span (bulkNode table) 32 10208 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10240 : span (bulkNode table) 32 10240 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10272 : span (bulkNode table) 32 10272 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10304 : span (bulkNode table) 32 10304 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10336 : span (bulkNode table) 32 10336 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10368 : span (bulkNode table) 32 10368 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10400 : span (bulkNode table) 32 10400 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10432 : span (bulkNode table) 32 10432 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10464 : span (bulkNode table) 32 10464 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10496 : span (bulkNode table) 32 10496 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10528 : span (bulkNode table) 32 10528 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10560 : span (bulkNode table) 32 10560 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10592 : span (bulkNode table) 32 10592 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10624 : span (bulkNode table) 32 10624 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10656 : span (bulkNode table) 32 10656 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10688 : span (bulkNode table) 32 10688 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10720 : span (bulkNode table) 32 10720 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10752 : span (bulkNode table) 32 10752 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10784 : span (bulkNode table) 32 10784 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10816 : span (bulkNode table) 32 10816 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10848 : span (bulkNode table) 32 10848 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10880 : span (bulkNode table) 32 10880 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10912 : span (bulkNode table) 32 10912 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10944 : span (bulkNode table) 32 10944 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10976 : span (bulkNode table) 32 10976 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11008 : span (bulkNode table) 32 11008 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11040 : span (bulkNode table) 32 11040 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11072 : span (bulkNode table) 32 11072 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11104 : span (bulkNode table) 32 11104 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11136 : span (bulkNode table) 32 11136 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11168 : span (bulkNode table) 32 11168 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11200 : span (bulkNode table) 32 11200 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11232 : span (bulkNode table) 32 11232 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11264 : span (bulkNode table) 32 11264 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11296 : span (bulkNode table) 32 11296 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11328 : span (bulkNode table) 32 11328 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11360 : span (bulkNode table) 32 11360 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11392 : span (bulkNode table) 32 11392 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11424 : span (bulkNode table) 32 11424 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11456 : span (bulkNode table) 32 11456 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11488 : span (bulkNode table) 32 11488 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11520 : span (bulkNode table) 32 11520 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11552 : span (bulkNode table) 32 11552 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11584 : span (bulkNode table) 32 11584 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11616 : span (bulkNode table) 32 11616 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11648 : span (bulkNode table) 32 11648 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11680 : span (bulkNode table) 32 11680 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11712 : span (bulkNode table) 32 11712 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11744 : span (bulkNode table) 32 11744 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11776 : span (bulkNode table) 32 11776 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11808 : span (bulkNode table) 32 11808 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11840 : span (bulkNode table) 32 11840 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11872 : span (bulkNode table) 32 11872 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11904 : span (bulkNode table) 32 11904 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11936 : span (bulkNode table) 32 11936 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11968 : span (bulkNode table) 32 11968 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12000 : span (bulkNode table) 32 12000 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12032 : span (bulkNode table) 32 12032 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12064 : span (bulkNode table) 32 12064 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12096 : span (bulkNode table) 32 12096 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12128 : span (bulkNode table) 32 12128 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12160 : span (bulkNode table) 32 12160 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12192 : span (bulkNode table) 32 12192 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12224 : span (bulkNode table) 32 12224 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12256 : span (bulkNode table) 32 12256 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12288 : span (bulkNode table) 32 12288 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12320 : span (bulkNode table) 32 12320 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12352 : span (bulkNode table) 32 12352 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12384 : span (bulkNode table) 32 12384 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12416 : span (bulkNode table) 32 12416 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12448 : span (bulkNode table) 32 12448 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12480 : span (bulkNode table) 32 12480 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12512 : span (bulkNode table) 32 12512 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12544 : span (bulkNode table) 32 12544 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12576 : span (bulkNode table) 32 12576 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12608 : span (bulkNode table) 32 12608 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12640 : span (bulkNode table) 32 12640 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12672 : span (bulkNode table) 32 12672 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12704 : span (bulkNode table) 32 12704 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12736 : span (bulkNode table) 32 12736 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12768 : span (bulkNode table) 32 12768 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12800 : span (bulkNode table) 32 12800 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12832 : span (bulkNode table) 32 12832 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12864 : span (bulkNode table) 32 12864 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12896 : span (bulkNode table) 32 12896 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12928 : span (bulkNode table) 32 12928 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12960 : span (bulkNode table) 32 12960 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12992 : span (bulkNode table) 32 12992 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13024 : span (bulkNode table) 32 13024 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13056 : span (bulkNode table) 32 13056 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13088 : span (bulkNode table) 32 13088 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13120 : span (bulkNode table) 32 13120 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13152 : span (bulkNode table) 32 13152 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13184 : span (bulkNode table) 32 13184 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13216 : span (bulkNode table) 32 13216 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13248 : span (bulkNode table) 32 13248 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13280 : span (bulkNode table) 32 13280 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13312 : span (bulkNode table) 32 13312 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13344 : span (bulkNode table) 32 13344 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13376 : span (bulkNode table) 32 13376 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13408 : span (bulkNode table) 32 13408 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13440 : span (bulkNode table) 32 13440 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13472 : span (bulkNode table) 32 13472 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13504 : span (bulkNode table) 32 13504 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13536 : span (bulkNode table) 32 13536 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13568 : span (bulkNode table) 32 13568 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13600 : span (bulkNode table) 32 13600 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13632 : span (bulkNode table) 32 13632 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13664 : span (bulkNode table) 32 13664 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13696 : span (bulkNode table) 32 13696 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13728 : span (bulkNode table) 32 13728 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13760 : span (bulkNode table) 32 13760 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13792 : span (bulkNode table) 32 13792 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13824 : span (bulkNode table) 32 13824 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13856 : span (bulkNode table) 32 13856 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13888 : span (bulkNode table) 32 13888 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13920 : span (bulkNode table) 32 13920 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13952 : span (bulkNode table) 16 13952 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem cover : span (bulkNode table) 13968 0 = true := (span_join (span_join (span_join (span_join (span_join (span_join (span_join (span_join (span_join c0 c32) (span_join c64 c96)) (span_join (span_join c128 c160) (span_join c192 c224))) (span_join (span_join (span_join c256 c288) (span_join c320 c352)) (span_join (span_join c384 c416) (span_join c448 c480)))) (span_join (span_join (span_join (span_join c512 c544) (span_join c576 c608)) (span_join (span_join c640 c672) (span_join c704 c736))) (span_join (span_join (span_join c768 c800) (span_join c832 c864)) (span_join (span_join c896 c928) (span_join c960 c992))))) (span_join (span_join (span_join (span_join (span_join c1024 c1056) (span_join c1088 c1120)) (span_join (span_join c1152 c1184) (span_join c1216 c1248))) (span_join (span_join (span_join c1280 c1312) (span_join c1344 c1376)) (span_join (span_join c1408 c1440) (span_join c1472 c1504)))) (span_join (span_join (span_join (span_join c1536 c1568) (span_join c1600 c1632)) (span_join (span_join c1664 c1696) (span_join c1728 c1760))) (span_join (span_join (span_join c1792 c1824) (span_join c1856 c1888)) (span_join (span_join c1920 c1952) (span_join c1984 c2016)))))) (span_join (span_join (span_join (span_join (span_join (span_join c2048 c2080) (span_join c2112 c2144)) (span_join (span_join c2176 c2208) (span_join c2240 c2272))) (span_join (span_join (span_join c2304 c2336) (span_join c2368 c2400)) (span_join (span_join c2432 c2464) (span_join c2496 c2528)))) (span_join (span_join (span_join (span_join c2560 c2592) (span_join c2624 c2656)) (span_join (span_join c2688 c2720) (span_join c2752 c2784))) (span_join (span_join (span_join c2816 c2848) (span_join c2880 c2912)) (span_join (span_join c2944 c2976) (span_join c3008 c3040))))) (span_join (span_join (span_join (span_join (span_join c3072 c3104) (span_join c3136 c3168)) (span_join (span_join c3200 c3232) (span_join c3264 c3296))) (span_join (span_join (span_join c3328 c3360) (span_join c3392 c3424)) (span_join (span_join c3456 c3488) (span_join c3520 c3552)))) (span_join (span_join (span_join (span_join c3584 c3616) (span_join c3648 c3680)) (span_join (span_join c3712 c3744) (span_join c3776 c3808))) (span_join (span_join (span_join c3840 c3872) (span_join c3904 c3936)) (span_join (span_join c3968 c4000) (span_join c4032 c4064))))))) (span_join (span_join (span_join (span_join (span_join (span_join (span_join c4096 c4128) (span_join c4160 c4192)) (span_join (span_join c4224 c4256) (span_join c4288 c4320))) (span_join (span_join (span_join c4352 c4384) (span_join c4416 c4448)) (span_join (span_join c4480 c4512) (span_join c4544 c4576)))) (span_join (span_join (span_join (span_join c4608 c4640) (span_join c4672 c4704)) (span_join (span_join c4736 c4768) (span_join c4800 c4832))) (span_join (span_join (span_join c4864 c4896) (span_join c4928 c4960)) (span_join (span_join c4992 c5024) (span_join c5056 c5088))))) (span_join (span_join (span_join (span_join (span_join c5120 c5152) (span_join c5184 c5216)) (span_join (span_join c5248 c5280) (span_join c5312 c5344))) (span_join (span_join (span_join c5376 c5408) (span_join c5440 c5472)) (span_join (span_join c5504 c5536) (span_join c5568 c5600)))) (span_join (span_join (span_join (span_join c5632 c5664) (span_join c5696 c5728)) (span_join (span_join c5760 c5792) (span_join c5824 c5856))) (span_join (span_join (span_join c5888 c5920) (span_join c5952 c5984)) (span_join (span_join c6016 c6048) (span_join c6080 c6112)))))) (span_join (span_join (span_join (span_join (span_join (span_join c6144 c6176) (span_join c6208 c6240)) (span_join (span_join c6272 c6304) (span_join c6336 c6368))) (span_join (span_join (span_join c6400 c6432) (span_join c6464 c6496)) (span_join (span_join c6528 c6560) (span_join c6592 c6624)))) (span_join (span_join (span_join (span_join c6656 c6688) (span_join c6720 c6752)) (span_join (span_join c6784 c6816) (span_join c6848 c6880))) (span_join (span_join (span_join c6912 c6944) (span_join c6976 c7008)) (span_join (span_join c7040 c7072) (span_join c7104 c7136))))) (span_join (span_join (span_join (span_join (span_join c7168 c7200) (span_join c7232 c7264)) (span_join (span_join c7296 c7328) (span_join c7360 c7392))) (span_join (span_join (span_join c7424 c7456) (span_join c7488 c7520)) (span_join (span_join c7552 c7584) (span_join c7616 c7648)))) (span_join (span_join (span_join (span_join c7680 c7712) (span_join c7744 c7776)) (span_join (span_join c7808 c7840) (span_join c7872 c7904))) (span_join (span_join (span_join c7936 c7968) (span_join c8000 c8032)) (span_join (span_join c8064 c8096) (span_join c8128 c8160)))))))) (span_join (span_join (span_join (span_join (span_join (span_join (span_join (span_join c8192 c8224) (span_join c8256 c8288)) (span_join (span_join c8320 c8352) (span_join c8384 c8416))) (span_join (span_join (span_join c8448 c8480) (span_join c8512 c8544)) (span_join (span_join c8576 c8608) (span_join c8640 c8672)))) (span_join (span_join (span_join (span_join c8704 c8736) (span_join c8768 c8800)) (span_join (span_join c8832 c8864) (span_join c8896 c8928))) (span_join (span_join (span_join c8960 c8992) (span_join c9024 c9056)) (span_join (span_join c9088 c9120) (span_join c9152 c9184))))) (span_join (span_join (span_join (span_join (span_join c9216 c9248) (span_join c9280 c9312)) (span_join (span_join c9344 c9376) (span_join c9408 c9440))) (span_join (span_join (span_join c9472 c9504) (span_join c9536 c9568)) (span_join (span_join c9600 c9632) (span_join c9664 c9696)))) (span_join (span_join (span_join (span_join c9728 c9760) (span_join c9792 c9824)) (span_join (span_join c9856 c9888) (span_join c9920 c9952))) (span_join (span_join (span_join c9984 c10016) (span_join c10048 c10080)) (span_join (span_join c10112 c10144) (span_join c10176 c10208)))))) (span_join (span_join (span_join (span_join (span_join (span_join c10240 c10272) (span_join c10304 c10336)) (span_join (span_join c10368 c10400) (span_join c10432 c10464))) (span_join (span_join (span_join c10496 c10528) (span_join c10560 c10592)) (span_join (span_join c10624 c10656) (span_join c10688 c10720)))) (span_join (span_join (span_join (span_join c10752 c10784) (span_join c10816 c10848)) (span_join (span_join c10880 c10912) (span_join c10944 c10976))) (span_join (span_join (span_join c11008 c11040) (span_join c11072 c11104)) (span_join (span_join c11136 c11168) (span_join c11200 c11232))))) (span_join (span_join (span_join (span_join (span_join c11264 c11296) (span_join c11328 c11360)) (span_join (span_join c11392 c11424) (span_join c11456 c11488))) (span_join (span_join (span_join c11520 c11552) (span_join c11584 c11616)) (span_join (span_join c11648 c11680) (span_join c11712 c11744)))) (span_join (span_join (span_join (span_join c11776 c11808) (span_join c11840 c11872)) (span_join (span_join c11904 c11936) (span_join c11968 c12000))) (span_join (span_join (span_join c12032 c12064) (span_join c12096 c12128)) (span_join (span_join c12160 c12192) (span_join c12224 c12256))))))) (span_join (span_join (span_join (span_join (span_join (span_join c12288 c12320) (span_join c12352 c12384)) (span_join (span_join c12416 c12448) (span_join c12480 c12512))) (span_join (span_join (span_join c12544 c12576) (span_join c12608 c12640)) (span_join (span_join c12672 c12704) (span_join c12736 c12768)))) (span_join (span_join (span_join (span_join c12800 c12832) (span_join c12864 c12896)) (span_join (span_join c12928 c12960) (span_join c12992 c13024))) (span_join (span_join (span_join c13056 c13088) (span_join c13120 c13152)) (span_join (span_join c13184 c13216) (span_join c13248 c13280))))) (span_join (span_join (span_join (span_join (span_join c13312 c13344) (span_join c13376 c13408)) (span_join (span_join c13440 c13472) (span_join c13504 c13536))) (span_join (span_join (span_join c13568 c13600) (span_join c13632 c13664)) (span_join (span_join c13696 c13728) (span_join c13760 c13792)))) (span_join (span_join (span_join c13824 c13856) (span_join c13888 c13920)) c13952)))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allOK (i : Nat) (hi : i < 13968) : bulkNode table i = true := span_ok cover i (Nat.zero_le _) hi
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem root0 : Impossible 13 0 wiresW := by
  have h := bulk_nodes table allOK 3 (by decide)
  have eq : permCheck wiresW (node 3).w = true := by decide +kernel
  exact perm_impossible (permCheck_perm eq) h
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem root1 : Impossible 13 1 wiresW := by
  have h := bulk_nodes table allOK 4 (by decide)
  have eq : permCheck wiresW (node 4).w = true := by decide +kernel
  exact perm_impossible (permCheck_perm eq) h
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem root2 : Impossible 13 2 wiresW := by
  have h := bulk_nodes table allOK 5 (by decide)
  have eq : permCheck wiresW (node 5).w = true := by decide +kernel
  exact perm_impossible (permCheck_perm eq) h
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem root3 : Impossible 13 3 wiresW := by
  have h := bulk_nodes table allOK 6 (by decide)
  have eq : permCheck wiresW (node 6).w = true := by decide +kernel
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
end PEqualNP.Outside.L_meta_3561.Normal

theorem PEqualNP.Outside.L_meta_3561 :
have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (13 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn (Function.update x5 (4 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (4 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ))]) = x1 x5) → False := by
  exact PEqualNP.Outside.L_meta_3561.conclude PEqualNP.Outside.L_meta_3561.Normal.allRoots
