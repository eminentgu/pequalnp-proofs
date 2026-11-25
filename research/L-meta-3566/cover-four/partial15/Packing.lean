import Live

namespace Mono94.Packing

def pack : List Sig → Nat
  | [] => 1
  | w :: ws => w.toNat + 65536 * pack ws

def unpack : Nat → Nat → List Sig
  | 0, _ => []
  | fuel+1, key =>
    if key < 65536 then [] else BitVec.ofNat 16 key :: unpack fuel (key / 65536)

theorem pack_pos (ws : List Sig) : 0 < pack ws := by
  induction ws with
  | nil => decide
  | cons w ws ih => simp only [pack]; omega

theorem unpack_pack (ws : List Sig) (fuel : Nat) (h : ws.length ≤ fuel) :
    unpack fuel (pack ws) = ws := by
  induction ws generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons w ws ih =>
    cases fuel with
    | zero => simp at h
    | succ fuel =>
      have small : w.toNat < 65536 := w.isLt
      have large : ¬ pack (w::ws) < 65536 := by
        change ¬w.toNat + 65536 * pack ws < 65536
        have := pack_pos ws
        omega
      have next : pack (w::ws) / 65536 = pack ws := by
        change (w.toNat + 65536 * pack ws) / 65536 = pack ws
        omega
      have hd : BitVec.ofNat 16 (pack (w::ws)) = w := by
        apply BitVec.eq_of_toNat_eq
        simp only [pack,BitVec.toNat_ofNat]
        change (w.toNat + 65536 * pack ws) % 65536 = w.toNat
        omega
      simp only [unpack,large,ite_false,next,hd]
      rw [ih fuel (by simpa using h)]

def insertWord (w : Sig) : List Sig → List Sig
  | [] => [w]
  | u::us => if w.toNat ≤ u.toNat then w::u::us else u::insertWord w us

theorem insertWord_perm (w : Sig) (ws : List Sig) : (insertWord w ws).Perm (w::ws) := by
  induction ws with
  | nil => exact List.Perm.refl _
  | cons u us ih =>
    simp only [insertWord]
    split
    · exact List.Perm.refl _
    · exact (ih.cons u).trans (List.Perm.swap _ _ _)

def canonical : List Sig → List Sig
  | [] => []
  | u::us => insertWord u (canonical us)

theorem canonical_perm (ws : List Sig) : (canonical ws).Perm ws := by
  induction ws with
  | nil => exact List.Perm.refl _
  | cons u us ih => exact (insertWord_perm u _).trans (ih.cons u)

def key (ws : List Sig) : Nat := pack (canonical ws)

theorem canonical_set (ws : List Sig) : (canonical ws).toFinset = ws.toFinset := by
  ext x
  simp only [List.mem_toFinset]
  exact (canonical_perm ws).mem_iff

def covered (fuel : Nat) (keyAt : Nat → Nat) (allowed : List Nat) (ws : List Sig) : Bool :=
  decide (ws.length ≤ fuel) && (let target := key ws; allowed.any (fun i => keyAt i == target))

theorem covered_sound {fuel : Nat} {keyAt : Nat → Nat} {allowed : List Nat} {ws : List Sig}
    (h : covered fuel keyAt allowed ws = true) :
    ∃ i ∈ allowed, (unpack fuel (keyAt i)).toFinset = ws.toFinset := by
  simp only [covered,Bool.and_eq_true,decide_eq_true_eq,List.any_eq_true,beq_iff_eq] at h
  obtain ⟨bl,i,mem,hk⟩ := h
  refine ⟨i,mem,?_⟩
  rw [hk,key,unpack_pack]
  · exact canonical_set ws
  · rw [(canonical_perm ws).length_eq]
    exact bl

end Mono94.Packing
