import EncodedBank
namespace PEqualNP.Research3561.SingleShare

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

end PEqualNP.Research3561.SingleShare

namespace PEqualNP.Research3561.SingleShare
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
end PEqualNP.Research3561.SingleShare

namespace PEqualNP.Research3561.SingleShare
open OuterSmall

private theorem value_at (r : α → Sig) (side : Bool) (p : Fin 414) (e : Tree α) :
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
    (p n : Fin 414)
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

abbrev Respects (S : Finset Sig) (p n : Fin 414) := ∀ a∈S, bit true p a=true → bit false n a=true

/-- Rows forced by two independent outside comparisons must be separated by an
inside input. This is a necessary condition on any shared module. -/
theorem module_of_trees {S : Finset Sig} {i : Tree Sig} {o : Tree (Option Sig)}
    (ev : o.value (Tree.plug (i.value id))=target)
    (cnt : ∀ x, i.occurrences x + o.occurrences (some x) = if x∈S then 1 else 0) :
    ∀ (p n p' n' : Fin 414), Respects (S\group S i) p n' → Respects (S\group S i) p' n → ¬ Respects (group S i) p n := by
  intro p n p' n' hp hn inside
  have forced (r s : Fin 414) (out : Respects (S\group S i) r s) :=
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
    ∃ A ⊆ S, ∀ (p n p' n' : Fin 414), Respects (S\A) p n' → Respects (S\A) p' n → ¬ Respects A p n := by
  obtain ⟨i,o,ev,_,cnt⟩ := h
  exact ⟨group S i,Finset.filter_subset _ _,module_of_trees ev cnt⟩

end PEqualNP.Research3561.SingleShare

namespace PEqualNP.Research3561.SingleShare

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

abbrev Row := Fin 414

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

end PEqualNP.Research3561.SingleShare

namespace PEqualNP.Research3561.SingleShare
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

end PEqualNP.Research3561.SingleShare

namespace PEqualNP.Research3561.SingleShare

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

end PEqualNP.Research3561.SingleShare

namespace PEqualNP.Research3561.SingleShare.Cubes

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
def join (span lo hi : Nat) := 2^span * hi + lo%(2^span)

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

end PEqualNP.Research3561.SingleShare.Cubes

namespace PEqualNP.Research3561.SingleShare.Cubes

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

end PEqualNP.Research3561.SingleShare.Cubes

namespace PEqualNP.Research3561.SingleShare.PackedResidual
open Cubes
def s0 : Sig := raw1
def s1 : Sig := raw2
def s2 : Sig := raw3
def s3 : Sig := raw5
def s4 : Sig := raw7
def s5 : Sig := (bin true raw6 (bin false (bin true raw5 (bin true raw1 raw4)) (bin false (bin true raw0 raw4) (bin true raw0 raw3))))
def s6 : Sig := (bin true raw8 (bin false (bin true raw5 (bin true raw1 raw4)) (bin false (bin true raw0 raw4) (bin true raw0 raw3))))
def wires : List Sig := [s0,s1,s2,s3,s4,s5,s6]
abbrev bank := wires.toFinset
private abbrev Sole (p n : Row) (q : Sig) := ∀ x∈bank, bit true p x ≠ bit false n x → x=q
private theorem obstruction : ¬SignedTiling bank := by
  rintro ⟨f,legal,rect⟩
  have force {p n x} (owned : Sole p n x) : f p n=x := owned _ (legal p n).1 (legal p n).2
  have a₁ : Sole 404 21 s1 := by decide +kernel
  have a₂ : Sole 228 226 s1 := by decide +kernel
  have b₁ : Sole 404 36 s2 := by decide +kernel
  have b₂ : Sole 204 226 s2 := by decide +kernel
  have ra := (rect 404 21 228 226 ((force a₁).trans (force a₂).symm)).trans (force a₁)
  have rb := (rect 404 36 204 226 ((force b₁).trans (force b₂).symm)).trans (force b₁)
  exact (by decide : s1 ≠ s2) (ra.symm.trans rb)
def rules : List Rule := [
  .cross 4 119 5 227 7 253,
  .cross 1 55 5 253 39 188,
  .cross 38 212 39 253 8 130,
  .cross 7 237 8 183 16 227,
  .row 4 86 1 55,
  .row 1 119 7 212,
  .row 4 253 16 86,
  .row 0 253 4 86]
theorem certificate : covered wires rules=true := by decide +kernel
theorem impossible : ¬Live 7 0 bank := covered_sound (rules:=rules) (by decide +kernel) obstruction certificate
end PEqualNP.Research3561.SingleShare.PackedResidual
