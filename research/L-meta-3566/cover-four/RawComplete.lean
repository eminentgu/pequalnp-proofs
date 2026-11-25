import Raw8144

namespace VertexPeel.Mask4

private def WordSubset (a b : Code) := ∀ i, a.getLsbD i = true → b.getLsbD i = true

private theorem add_subset {z base : Code} (sub : WordSubset base z) (i : Nat) (hi : z.getLsbD i = true) :
    WordSubset (base ||| BitVec.twoPow 21 i) z := by
  intro j bit
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_twoPow, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at bit
  rcases bit with p|⟨_,rfl⟩
  · exact sub _ p
  · exact hi

private theorem mask_mono {a b m : Code} (sub : WordSubset a b) (h : (a &&& m) = m) :
    (b &&& m) = m := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have eq := congrArg (fun z : Code => z.getLsbD i) h
  simp only [BitVec.getLsbD_and] at eq ⊢
  cases bit : m.getLsbD i with
  | false => simp
  | true =>
    have aOn : a.getLsbD i = true := by simpa [bit] using eq
    simp [sub i aOn]

private theorem can_accept {z base : Code} (good : smallGirthB z = true) (sub : WordSubset base z)
    {t : Step} (known : ∀ m ∈ t.tests, m ∈ girthMasks) : accept t base = true := by
  apply List.all_eq_true.mpr
  intro m hm
  have h := List.all_eq_true.mp good m (known m hm)
  simp only [bne_iff_ne] at h ⊢
  exact fun e => h (mask_mono sub e)

private def follow (z : Code) : List Step → Code → Code
  | [], base => base
  | t::ts, base => follow z ts (if z.getLsbD t.index then base ||| BitVec.twoPow 21 t.index else base)

private theorem follow_mem (z : Code) (good : smallGirthB z = true) (ts : List Step) (base : Code)
    (sub : WordSubset base z) (tests : ∀ t ∈ ts, ∀ m ∈ t.tests, m ∈ girthMasks) :
    follow z ts base ∈ enumCodes ts base := by
  induction ts generalizing base with
  | nil => simp [follow,enumCodes]
  | cons t ts ih =>
    let new := base ||| BitVec.twoPow 21 t.index
    have tail := fun (q : Step) (qmem : q ∈ ts) => tests q (List.mem_cons_of_mem _ qmem)
    cases bit : z.getLsbD t.index with
    | false =>
      simp only [follow,bit,Bool.false_eq_true,ite_false,enumCodes,List.mem_append]
      exact Or.inl (ih base sub tail)
    | true =>
      have sm : WordSubset new z := add_subset sub t.index bit
      have acceptNew : accept t new = true := can_accept good sm (tests t List.mem_cons_self)
      rw [follow,enumCodes]
      simp only [bit,ite_true,List.mem_append]
      exact Or.inr (by simpa [new] using (show follow z ts new ∈
        (if accept t new then enumCodes ts new else []) from by simpa [acceptNew] using ih new sm tail))

private theorem follow_spec (z : Code) (ts : List Step) (base : Code) (i : Nat) (hi : i<21) :
    (follow z ts base).getLsbD i = true ↔ base.getLsbD i = true ∨
      ((∃ t ∈ ts, t.index=i) ∧ z.getLsbD i=true) := by
  induction ts generalizing base with
  | nil => simp [follow]
  | cons t ts ih =>
    rw [follow,ih]
    cases ht : z.getLsbD t.index <;>
      simp only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_or,
        BitVec.getLsbD_twoPow,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,
        List.mem_cons] <;> grind

theorem raw_complete (z : Code) (good : smallGirthB z = true) : z ∈ raw8144 := by
  have verifiedTests : steps.all (fun t => t.tests.all (fun m => girthMasks.contains m)) = true := by decide +kernel
  have known : ∀ t ∈ steps, ∀ m ∈ t.tests, m ∈ girthMasks := by
    intro t ht m hm
    have h := List.all_eq_true.mp (List.all_eq_true.mp verifiedTests t ht) m hm
    simpa using h
  have verifiedBits : (List.range 21).all (fun i => steps.any (fun t => t.index==i)) = true := by decide +kernel
  have allBits (i : Fin 21) : ∃ t ∈ steps, t.index=i.val := by
    have h := List.all_eq_true.mp verifiedBits i.val (List.mem_range.mpr i.isLt)
    simpa using List.any_eq_true.mp h
  have h := follow_mem z good steps 0 (by intro i h; simp at h) known
  have reconstruct : follow z steps 0 = z := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have eq := follow_spec z steps 0 j hj
    have chosen := allBits ⟨j,hj⟩
    simpa [chosen] using eq
  rw [reconstruct] at h
  exact h

end VertexPeel.Mask4
#print axioms VertexPeel.Mask4.raw_complete
