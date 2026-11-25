import Live
import PEqualNP.Defs.MetaComplexityLgpMono

-- The bit-parallel circuit semantics and backward extraction adapt upstream
-- PEqualNP.Outside.L_meta_3967 (leoli001031-blip, PR #8875). Only binary
-- AND/OR steps occur in this live plan. The selected sixteen rows are enough
-- to force all nine inputs in its initial set.

namespace VertexPeel.CoverFour.Case15Partial
open Mono94
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 8192

def zero : Sig := 0
def one : Sig := BitVec.allOnes 16
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self]; simp

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  cases l with
  | nil =>
    rcases ho with rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)


private theorem memberProper {T k S} (plan : Live T k S) : ∀ v ∈ S, proper v := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,h⟩ := plan
    simpa using h
  | succ k ih =>
    obtain ⟨U,a,b,d,rfl,pa,pb,_,_,tail⟩ := plan
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact pa
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact pb
    exact ih tail _ (Finset.mem_insert_of_mem hv)

private lemma pull_gate {w : List Sig} {z : Sig} {k S} (h : Live target k S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+1 ∧ Live target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := memberProper h z hm
      rcases hz with hr | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨k+1,_,le_rfl,⟨U,a,b,d,rfl,pa,pb,hab,hf,ht⟩,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k S, k ≤ gs.length ∧ Live target k S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,⟨rfl,hp⟩,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,T,by simp; omega,hu,hT⟩

def bit (i : Fin 16) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]





def roots : List Sig := [10755, 1036, 25136, 8128, 37905, 38948, 49218, 57480, 33024]
def goal : Sig := 511
def sample (r : Fin 16) (j : Fin 9) : Bool := bit r (roots.getD j.val zero)
private theorem sampled (r : Fin 16) : List.ofFn (sample r) = roots.map (bit r) := by
  have eq : List.ofFn (fun j : Fin 9 => roots.getD j.val zero) = roots := rfl
  rw [← eq,List.map_ofFn]
  rfl

private theorem table_eval (C : Circuit) (legal : Monotone2 C) (i : Nat) (r : Fin 16) :
    bit r ((execute C.gates roots).getD i zero) = (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1),sampled]
  rfl

private theorem liveDistinguishes {k : Nat} {S : Finset Sig} {r s : Fin 16}
    (plan : Live goal k S) (yes : bit r goal = true) (no : bit s goal = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := plan
    exact ⟨goal,by simp,yes,no⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,rfl,_,_,_,_,tail⟩ := plan
    obtain ⟨v,hv,hp,hn⟩ := ih tail
    rcases Finset.mem_insert.mp hv with rfl | hu
    · have separated : (bit r a = true ∧ bit s a = false) ∨
          (bit r b = true ∧ bit s b = false) := by
        rw [bit_bin] at hp hn
        exact (by decide : ∀ d u v w z : Bool,
          (if d then u || w else u && w) = true →
          (if d then v || z else v && z) = false →
          (u = true ∧ v = false) ∨ (w = true ∧ z = false)) d _ _ _ _ hp hn
      rcases separated with ha | hb
      · exact ⟨a,by simp,ha⟩
      · exact ⟨b,by simp,hb⟩
    · exact ⟨v,by simp [hu],hp,hn⟩

private def distinguishingRows (a : Sig) : Fin 16 × Fin 16 :=
  if a = 10755 then (0,10) else if a = 1036 then (2,11) else if a = 25136 then (4,10) else if a = 8128 then (6,14) else if a = 37905 then (0,9) else if a = 38948 then (2,10) else if a = 49218 then (1,9) else if a = 57480 then (3,10) else (8,9)

private theorem needEveryRoot : ∀ a ∈ roots, ∃ r s : Fin 16,
    bit r goal = true ∧ bit s goal = false ∧
      ∀ b ∈ roots, bit r b = true → bit s b = false → b = a := by
  intro a ha
  refine ⟨(distinguishingRows a).1,(distinguishingRows a).2,?_⟩
  have certificate : roots.all (fun v =>
      (bit (distinguishingRows v).1 goal && !(bit (distinguishingRows v).2 goal)) &&
      roots.all (fun b => decide
        (bit (distinguishingRows v).1 b = true → bit (distinguishingRows v).2 b = false → b = v))) =
      true := by decide +kernel
  have valid := List.all_eq_true.mp certificate a ha
  simpa only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, decide_eq_true_eq, and_assoc] using valid


theorem extractExact (C : Circuit) (legal : Monotone2 C)
    (correct : ∀ r : Fin 16, C.eval (List.ofFn (sample r)) = bit r goal) :
    ∃ k ≤ C.size, Live goal k roots.toFinset := by
  have hp : proper goal := by unfold proper; decide
  have out : (execute C.gates roots).getD C.output zero = goal := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    exact (table_eval C legal _ ⟨j,hj⟩).trans (correct ⟨j,hj⟩)
  have hits : goal ∈ execute C.gates roots := by
    have rep := get_rep (execute C.gates roots) C.output
    rw [out] at rep
    exact rep.resolve_right (fun h => h hp)
  obtain ⟨k,S,budget,plan,sub⟩ := extract C.gates roots legal hp hits
  have same : S = roots.toFinset := by
    ext a
    constructor
    · intro ha; exact List.mem_toFinset.mpr (sub _ ha)
    · intro ha
      obtain ⟨r,s,yes,no,only⟩ := needEveryRoot a (List.mem_toFinset.mp ha)
      obtain ⟨b,hb,hp,hn⟩ := liveDistinguishes plan yes no
      exact only b (sub _ hb) hp hn ▸ hb
  exact ⟨k,budget,same ▸ plan⟩

end VertexPeel.CoverFour.Case15Partial
