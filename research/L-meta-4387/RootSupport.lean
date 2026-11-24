import Mathlib

namespace PEqualNP.Research4387.RootSupport

/-- Terms over just the indicated roots. DAG sharing is allowed in the
original program. This predicate is used only for its semantic closure. -/
inductive From {n w : ℕ} (seed : Fin n → BitVec w) (S : Finset (Fin n)) : BitVec w → Prop where
  | root {i} : i ∈ S → From seed S (seed i)
  | conj {a b} : From seed S a → From seed S b → From seed S (a &&& b)
  | disj {a b} : From seed S a → From seed S b → From seed S (a ||| b)

abbrev Valid {n w : ℕ} (seed : Fin n → BitVec w) (xs : List (BitVec w)) :=
  ∀ i : Fin xs.length, ∃ a ∈ List.ofFn seed ++ xs.take i.val,
    ∃ b ∈ List.ofFn seed ++ xs.take i.val, xs.get i = a &&& b ∨ xs.get i = a ||| b

/-- A bank of k binary gates can supply all members of T from at most
k+|T| of the original roots, even when the outputs share predecessors. -/
theorem smallRoots {n w : ℕ} (seed : Fin n → BitVec w) (xs : List (BitVec w))
    (valid : Valid seed xs) (T : Finset (BitVec w))
    (present : ∀ z ∈ T, z ∈ List.ofFn seed ++ xs) :
    ∃ S : Finset (Fin n), S.card ≤ xs.length+T.card ∧ ∀ z ∈ T, From seed S z := by
  classical
  induction xs using List.reverseRecOn generalizing T with
  | nil =>
    have orig (x : {z // z ∈ T}) : ∃ i, seed i = x.val := by
      have haveRoot := present x.val x.property
      simpa only [List.append_nil,List.mem_ofFn] using haveRoot
    let S := T.attach.image (fun x => (orig x).choose)
    refine ⟨S,?_,?_⟩
    · simpa [S] using (Finset.card_image_le (s:=T.attach) (f:=fun x => (orig x).choose))
    · intro z hz
      let x : {z // z ∈ T} := ⟨z,hz⟩
      have hi : (orig x).choose ∈ S := Finset.mem_image.mpr ⟨x,Finset.mem_attach _ _,rfl⟩
      change From seed S x.val
      rw [← (orig x).choose_spec]
      exact From.root hi
  | append_singleton xs v ih =>
    have vp : Valid seed xs := by
      intro i
      simpa only [List.get_eq_getElem,List.getElem_append_left i.isLt,
        List.take_append_of_le_length i.isLt.le] using valid ⟨i.val,by simp⟩
    have old {z} (hz : z ∈ T) (ne : z ≠ v) : z ∈ List.ofFn seed ++ xs := by
      have hz' := present z hz
      simpa [← List.append_assoc,ne] using hz'
    by_cases used : v ∈ T
    · obtain ⟨a,ha,b,hb,op⟩ := valid ⟨xs.length,by simp⟩
      simp only [List.take_append_length,List.get_eq_getElem,List.getElem_append_right (Nat.le_refl _),
        Nat.sub_self,List.getElem_cons_zero] at ha hb op
      let Q := insert a (insert b (T.erase v))
      have before : ∀ z ∈ Q, z ∈ List.ofFn seed ++ xs := by
        intro z hz
        simp only [Q,Finset.mem_insert,Finset.mem_erase] at hz
        rcases hz with rfl | rfl | ⟨ne,hz⟩
        · exact ha
        · exact hb
        · exact old hz ne
      obtain ⟨S,count,closure⟩ := ih vp Q before
      have size := Finset.card_erase_of_mem used
      have ba := Finset.card_insert_le a (insert b (T.erase v))
      have bb := Finset.card_insert_le b (T.erase v)
      change S.card ≤ xs.length+(insert a (insert b (T.erase v))).card at count
      have tp := Finset.card_pos.mpr ⟨v,used⟩
      refine ⟨S,by simp only [List.length_append,List.length_singleton]; omega,?_⟩
      intro z hz
      by_cases eq : z = v
      · subst z
        have ca := closure a (by simp [Q])
        have cb := closure b (by simp [Q])
        rcases op with op | op
        · exact op ▸ From.conj ca cb
        · exact op ▸ From.disj ca cb
      · exact closure z (by simp [Q,eq,hz])
    · obtain ⟨S,count,closure⟩ := ih vp T (fun z hz => old hz (fun e => used (e ▸ hz)))
      exact ⟨S,by simp only [List.length_append,List.length_singleton]; omega,closure⟩

end PEqualNP.Research4387.RootSupport
