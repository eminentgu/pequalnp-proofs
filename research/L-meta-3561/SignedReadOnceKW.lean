import EncodedBank
namespace PEqualNP.Research3561
namespace SignedReadOnceKW
abbrev Row := Fin 414

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
end PEqualNP.Research3561
