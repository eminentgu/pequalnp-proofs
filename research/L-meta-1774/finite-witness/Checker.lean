import Live
import Mathlib.Data.BitVec
import Mathlib.Tactic.FinCases
import Mathlib.Data.Finset.Card

namespace Mono94

abbrev M := BitVec 63

def sigMask (w : Sig) : M :=
  let p : M := w.setWidth 63 &&& 511
  let block (j : Nat) : M := if w.getLsbD (9+j) then 0 else p
  block 0 ||| (block 1 <<< 9) ||| (block 2 <<< 18) ||| (block 3 <<< 27) |||
    (block 4 <<< 36) ||| (block 5 <<< 45) ||| (block 6 <<< 54)

def span (ws : List Sig) : M := ws.foldr (fun w m => sigMask w ||| m) 0

theorem sigMask_spec (w : Sig) (i : Fin 9) (j : Fin 7) :
    (sigMask w).getLsbD (j.val*9+i.val) = (w.getLsbD i.val && !w.getLsbD (9+j.val)) := by
  have readIf (b : Bool) (v : M) (t : Nat) :
      (if b then (0 : M) else v).getLsbD t = (!b && v.getLsbD t) := by
    cases b <;> simp
  fin_cases i <;> fin_cases j <;>
    simp only [sigMask,BitVec.getLsbD_or,BitVec.getLsbD_shiftLeft,readIf,
      BitVec.getLsbD_and,BitVec.getLsbD_setWidth] <;> simp [Bool.and_comm]


theorem live_size {T : Sig} {k : Nat} {S : Finset Sig} (h : Live T k S) : S.card ≤ k+1 := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := h
    simp
  | succ k ih =>
    obtain ⟨U,a,b,d,rfl,_,_,_,fresh,tail⟩ := h
    have hn : bin d a b ∉ U := fun h => fresh (by simp [h])
    have H := ih tail
    rw [Finset.card_insert_of_notMem hn] at H
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    omega

theorem live_proper {T : Sig} {k : Nat} {S : Finset Sig} (h : Live T k S) : ∀ w ∈ S, proper w := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    simpa using hp
  | succ k ih =>
    obtain ⟨U,a,b,d,rfl,pa,pb,_,_,tail⟩ := h
    simp only [Finset.forall_mem_insert]
    exact ⟨pa,pb,fun w hw => ih tail w (Finset.mem_insert_of_mem hw)⟩

theorem separates {T : Sig} {k : Nat} {S : Finset Sig} (h : Live T k S)
    (i j : Nat) (hi : T.getLsbD i = true) (hj : T.getLsbD j = false) :
    ∃ w ∈ S, w.getLsbD i = true ∧ w.getLsbD j = false := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := h
    exact ⟨_,by simp,hi,hj⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,rfl,_,_,_,_,tail⟩ := h
    obtain ⟨w,hw,wi,wj⟩ := ih tail
    rcases Finset.mem_insert.mp hw with rfl | hU
    · cases d <;> simp [bin] at wi wj
      · by_cases x : a.getLsbD j = true
        · exact ⟨b,by simp,wi.2,wj x⟩
        · exact ⟨a,by simp,wi.1,by simpa using x⟩
      · rcases wi with x | y
        · exact ⟨a,by simp,x,wj.1⟩
        · exact ⟨b,by simp,y,wj.2⟩
    · exact ⟨w,by simp [hU],wi,wj⟩

private theorem inSpan {w : Sig} {ws : List Sig} (hw : w ∈ ws) (j : Nat)
    (h : (sigMask w).getLsbD j = true) : (span ws).getLsbD j = true := by
  induction ws with
  | nil => cases hw
  | cons a l ih =>
    change ((sigMask a) ||| span l).getLsbD j = true
    simp only [BitVec.getLsbD_or,Bool.or_eq_true]
    rcases List.mem_cons.mp hw with rfl | rest
    · exact Or.inl h
    · exact Or.inr (ih rest)

theorem live_span {k : Nat} {ws : List Sig} (h : Live 511 k ws.toFinset) : span ws = BitVec.allOnes 63 := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  let i : Fin 9 := ⟨t%9,by omega⟩
  let j : Fin 7 := ⟨t/9,by omega⟩
  have idx : j.val * 9 + i.val = t := by dsimp [j,i]; omega
  have pos : ∀ u : Fin 9, (511 : Sig).getLsbD u.val = true := by decide
  have neg : ∀ v : Fin 7, (511 : Sig).getLsbD (9+v.val) = false := by decide
  obtain ⟨w,hw,wp,wn⟩ := separates h _ _ (pos i) (neg j)
  have on := sigMask_spec w i j
  rw [idx,wp,wn] at on
  rw [BitVec.getLsbD_allOnes]
  simpa [ht] using inSpan (List.mem_toFinset.mp hw) t on

def kept (v : Sig) (b : Bool) (xs : List Sig) := if b then v::xs else xs

instance (w : Sig) : Decidable (proper w) := by unfold proper; infer_instance

def children (covered : List Sig → Bool) (k : Nat) (ws rest : List Sig) (a b : Sig) : Bool :=
  let m := span rest
  [false,true].all fun d =>
    let c := bin d a b
    !decide (proper c) || ws.contains c ||
    let mc := sigMask c ||| m
    [false,true].all fun ka => [false,true].all fun kb =>
      let num := rest.length + 1 + ka.toNat + kb.toNat
      let mask := mc ||| (if ka then sigMask a else 0) ||| (if kb then sigMask b else 0)
      decide (k+1 < num) || mask != BitVec.allOnes 63 || covered (c :: kept a ka (kept b kb rest))

/-- The two list scans visit each unordered operand pair once. -/
def partners (p : Sig → List Sig → Bool) (before : List Sig) : List Sig → Bool
  | [] => true
  | b::bs => p b (before ++ bs) && partners p (b::before) bs

def pairs (p : Sig → Sig → List Sig → Bool) (before : List Sig) : List Sig → Bool
  | [] => true
  | a::as => partners (p a) before as && pairs p (a::before) as

def checkNode (bound : Nat) (ws : List Sig) (covered : List Sig → Bool) : Bool :=
  !(ws.contains 511) && match bound with
  | 0 => true
  | k+1 => pairs (fun a b rest => children covered k ws rest a b) [] ws

private theorem partners_find (p : Sig → List Sig → Bool) (before xs : List Sig)
    (pass : partners p before xs = true) {w : Sig} (mem : w ∈ xs) :
    ∃ rest, (w::rest).Perm (before ++ xs) ∧ p w rest = true := by
  induction xs generalizing before with
  | nil => cases mem
  | cons b bs ih =>
    obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp pass
    rcases List.mem_cons.mp mem with rfl | mem
    · exact ⟨_,List.perm_middle.symm,head⟩
    · obtain ⟨r,e,hr⟩ := ih (b::before) tail mem
      exact ⟨r,e.trans List.perm_middle.symm,hr⟩

private theorem pairs_find (p : Sig → Sig → List Sig → Bool) (before xs : List Sig)
    (pass : pairs p before xs = true) {v w : Sig} (vm : v ∈ xs) (wm : w ∈ xs) (ne : v ≠ w) :
    ∃ a b rest, ((a = v ∧ b = w) ∨ (a = w ∧ b = v)) ∧
      (a::b::rest).Perm (before ++ xs) ∧ p a b rest = true := by
  induction xs generalizing before with
  | nil => cases vm
  | cons q qs ih =>
    obtain ⟨sub,tail⟩ := Bool.and_eq_true_iff.mp pass
    rcases List.mem_cons.mp vm with rfl | vtail
    · have wh := (List.mem_cons.mp wm).resolve_left ne.symm
      obtain ⟨r,e,hr⟩ := partners_find (p v) before qs sub wh
      exact ⟨_,_,r,Or.inl ⟨rfl,rfl⟩,(e.cons v).trans List.perm_middle.symm,hr⟩
    rcases List.mem_cons.mp wm with rfl | wm
    · obtain ⟨r,e,hr⟩ := partners_find (p w) before qs sub vtail
      exact ⟨_,_,r,Or.inr ⟨rfl,rfl⟩,(e.cons w).trans List.perm_middle.symm,hr⟩
    · obtain ⟨a,b,r,eq,perm,ok⟩ := ih (q::before) tail vtail wm
      exact ⟨a,b,r,eq,perm.trans List.perm_middle.symm,ok⟩

private theorem children_sound (k l : ℕ) (le : l ≤ k) (ws rest : List Sig) (a b : Sig)
    (nd : ws.Nodup) (perm : (a::b::rest).Perm ws)
    (covered : List Sig → Bool) (good : children covered k ws rest a b = true)
    (U : Finset Sig) (d : Bool) (eq : ws.toFinset = insert a (insert b U))
    (fresh : bin d a b ∉ ws.toFinset) (tail : Live 511 l (insert (bin d a b) U)) :
    ∃ xs, xs.Nodup ∧ covered xs = true ∧ Live 511 l xs.toFinset := by
  let c := bin d a b
  let ka := decide (a ∈ U)
  let kb := decide (b ∈ U)
  let xs := c :: kept a ka (kept b kb rest)
  have ndrest := (perm.nodup_iff.mpr nd)
  simp only [List.nodup_cons,List.mem_cons,not_or] at ndrest
  have inrest (w : Sig) : w ∈ rest ↔ w ∈ U ∧ w ≠ a ∧ w ≠ b := by
    have all : w ∈ a::b::rest ↔ w ∈ insert a (insert b U) := by
      rw [perm.mem_iff,←eq,List.mem_toFinset]
    simp only [Finset.mem_insert,List.mem_cons] at all
    constructor
    · intro h
      have wa : w ≠ a := fun e => ndrest.1.2 (e ▸ h)
      have wb : w ≠ b := fun e => ndrest.2.1 (e ▸ h)
      exact ⟨((all.mp (Or.inr (Or.inr h))).resolve_left wa).resolve_left wb,wa,wb⟩
    · rintro ⟨h,wa,wb⟩
      exact ((all.mpr (Or.inr (Or.inr h))).resolve_left wa).resolve_left wb
  have bank : (kept a ka (kept b kb rest)).toFinset = U := by
    ext w
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;> simp [ka,kb,kept,ha,hb,inrest] <;> grind
  have nf : c ∉ U := fun h => fresh (eq ▸ (by simp [c,h] : bin d a b ∈ insert a (insert b U)))
  have xset : xs.toFinset = insert c U := by simp [xs,bank]
  have xnodup : xs.Nodup := by
    have missing : c ∉ kept a ka (kept b kb rest) := fun hm => nf (bank ▸ List.mem_toFinset.mpr hm)
    dsimp only [xs]
    rw [List.nodup_cons]
    refine ⟨missing,?_⟩
    cases ka <;> cases kb <;> simp [kept,ndrest.1.1,ndrest.1.2,ndrest.2.1,ndrest.2.2]
  have run : Live 511 l xs.toFinset := xset ▸ tail
  have sz := live_size run
  rw [List.toFinset_card_of_nodup xnodup] at sz
  have count : xs.length = rest.length + 1 + ka.toNat + kb.toNat := by
    dsimp only [xs]
    cases ka <;> cases kb <;> simp [kept]
  have maxlen : ¬ k+1 < rest.length + 1 + ka.toNat + kb.toNat := by omega
  have cc : proper c := live_proper tail c (Finset.mem_insert_self _ _)
  have nmem : c ∉ ws := fun h => fresh (List.mem_toFinset.mpr h)
  have mEq : (sigMask c ||| span rest ||| (if ka then sigMask a else 0) |||
      (if kb then sigMask b else 0)) = BitVec.allOnes 63 := by
    have z := live_span run
    dsimp only [xs] at z
    have rearrange (a b c : M) : a ||| (b ||| c) = b ||| (a ||| c) := by
      rw [←BitVec.or_assoc,BitVec.or_comm a b,BitVec.or_assoc]
    cases ha : ka <;> cases hb : kb <;>
      simpa [ha,hb,kept,span,BitVec.or_assoc,BitVec.or_comm,rearrange] using z
  have result := List.all_eq_true.mp good d (by cases d <;> simp)
  simp only [← show c = bin d a b from rfl] at result
  simp only [decide_eq_true cc,Bool.not_true,List.contains_eq_mem,decide_eq_false nmem,
    Bool.false_or] at result
  have first := List.all_eq_true.mp result ka (by cases ka <;> simp)
  have branch := List.all_eq_true.mp first kb (by cases kb <;> simp)
  refine ⟨xs,xnodup,?_,run⟩
  change (decide _ || (_ != BitVec.allOnes 63) || covered xs) = true at branch
  rw [decide_eq_false maxlen,mEq] at branch
  simpa using branch

theorem checkNode_sound (k : Nat) (ws : List Sig) (covered : List Sig → Bool)
    (nd : ws.Nodup) (pass : checkNode k ws covered = true)
    (closure : ∀ xs, xs.Nodup → covered xs = true → ∀ l, l < k → ¬Live 511 l xs.toFinset) :
    ∀ j, j ≤ k → ¬Live 511 j ws.toFinset := by
  intro j hj h
  have other := (Bool.and_eq_true_iff.mp pass).1
  have noT : (511:Sig) ∉ ws := by simpa using other
  cases j with
  | zero =>
    obtain ⟨eq,_⟩ := h
    exact noT (List.mem_toFinset.mp (eq ▸ Finset.mem_singleton_self _))
  | succ j =>
    cases k with
    | zero => omega
    | succ k =>
      obtain ⟨U,v,w,d,eq,_,_,ne,fresh,tail⟩ := h
      have vm : v ∈ ws := List.mem_toFinset.mp (eq ▸ (by simp))
      have wm : w ∈ ws := List.mem_toFinset.mp (eq ▸ (by simp))
      have ok := (Bool.and_eq_true_iff.mp pass).2
      obtain ⟨a,b,r,alt,pr,check⟩ := pairs_find
        (fun a b rest => children covered k ws rest a b) [] ws ok vm wm ne
      simp only [List.nil_append] at pr
      have ready : ws.toFinset = insert a (insert b U) ∧ bin d a b ∉ ws.toFinset ∧
          Live 511 j (insert (bin d a b) U) := by
        rcases alt with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact ⟨eq,fresh,tail⟩
        · have comm : bin d a b = bin d b a := by cases d <;> simp [bin,BitVec.or_comm,BitVec.and_comm]
          exact ⟨eq.trans (Finset.insert_comm ..),comm ▸ fresh,comm ▸ tail⟩
      obtain ⟨ys,yn,yc,yr⟩ := children_sound k j (by omega) ws r a b nd pr covered check
        U d ready.1 ready.2.1 ready.2.2
      exact closure ys yn yc j (by omega) yr

end Mono94
