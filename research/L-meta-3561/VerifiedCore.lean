import SearchCore
import SignedReadOnceKW

namespace PEqualNP.Research3561.KWCertificate
open SignedReadOnceKW
abbrev Row := Fin 414

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
def row (code offset : Nat) : Row := Fin.ofNat 414 ((code >>> (2+9*offset)) &&& 511)

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
end PEqualNP.Research3561.KWCertificate
namespace PEqualNP.Research3561.KWMemo
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
end PEqualNP.Research3561.KWMemo