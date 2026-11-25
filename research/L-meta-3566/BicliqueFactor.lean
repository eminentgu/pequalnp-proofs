import FactorMatching

namespace VertexPeel.FactorMatching

variable {A B : Type*}

def flip (G : Relation A B) : Relation B A := fun c r => G r c

theorem transpose (G H K : Relation A B) (e : Exact G H K) : Exact (flip G) (flip H) (flip K) := by
  intro cols rows
  have swap (L : Relation A B) : Hits (flip L) cols rows ↔ Hits L rows cols := by
    constructor
    · rintro ⟨c,r,hc,hr,l⟩; exact ⟨r,c,hr,hc,l⟩
    · rintro ⟨r,c,hr,hc,l⟩; exact ⟨c,r,hc,hr,l⟩
  rw [swap,swap,swap,e]

theorem common (G H K : Relation A B) (e : Exact G H K) {a : A} {b : B}
    (hh : H a b) (kk : K a b) : G a b := by
  obtain ⟨r,c,ra,cb,w⟩ := (e (·=a) (·=b)).mpr ⟨⟨a,b,rfl,rfl,hh⟩,⟨a,b,rfl,rfl,kk⟩⟩
  exact ra ▸ cb ▸ w

/-- On a shared column, a row of the first rectangle or a row of the second
    must have an actual edge. -/
theorem common_col (G H K : Relation A B) (e : Exact G H K) {a z : A} {b : B}
    (hh : H a b) (kk : K z b) : G a b ∨ G z b := by
  by_contra! bad
  exact (cross G H K e hh bad.1 kk bad.2).elim bad.1 bad.2

section FiniteBlocks

variable [DecidableEq A] [DecidableEq B]
abbrev Block (H : Relation A B) (R : Finset A) (S : Finset B) : Prop :=
  ∀ r ∈ R, ∀ s ∈ S, H r s

omit [DecidableEq A] in
private theorem common_columns (G H K : Relation A B) (e : Exact G H K) (sq : SquareFree G)
    (R U : Finset A) (S V : Finset B) (hr : 1<R.card) (hu : 1<U.card)
    (bh : Block H R S) (bk : Block K U V) {a : A} (ar : a∈R) (au : a∈U) :
    (S∩V).card ≤ 2 := by
  classical
  obtain ⟨x,xr,xa⟩ := Finset.exists_mem_ne hr a
  obtain ⟨y,yu,ya⟩ := Finset.exists_mem_ne hu a
  let W := S∩V
  let green (t : A) := W.filter fun k => G t k
  have allG (k : B) (wk : k∈W) : G a k :=
    common G H K e (bh _ ar _ (Finset.mem_inter.mp wk).1) (bk _ au _ (Finset.mem_inter.mp wk).2)
  have one (t : A) (ta : t≠a) : (green t).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    have mp := Finset.mem_filter.mp hp
    have mq := Finset.mem_filter.mp hq
    by_contra ne
    exact sq ta ne mp.2 mq.2 (allG p mp.1) (allG q mq.1)
  have sub : W ⊆ green x ∪ green y := by
    intro k wk
    have sv := Finset.mem_inter.mp wk
    rcases common_col G H K e (bh _ xr _ sv.1) (bk _ yu _ sv.2) with xg | yg
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨wk,xg⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨wk,yg⟩)
  have bound := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  change W.card ≤ 2
  have := one x xa
  have := one y ya
  omega

/-- Any nonstar bicliques in opposite exact factors overlap in at most two
    original edges, regardless of gates shared between the branches. -/
theorem rectangle_overlap (G H K : Relation A B) (e : Exact G H K) (sq : SquareFree G)
    (R U : Finset A) (S V : Finset B) (hr : 1<R.card) (hu : 1<U.card)
    (hs : 1<S.card) (hv : 1<V.card) (bh : Block H R S) (bk : Block K U V) :
    (R∩U).card * (S∩V).card ≤ 2 := by
  classical
  by_cases er : (R∩U).Nonempty
  · obtain ⟨a,ar⟩ := er
    by_cases ec : (S∩V).Nonempty
    · obtain ⟨b,bs⟩ := ec
      have c2 := common_columns G H K e sq R U S V hr hu bh bk
        (Finset.mem_inter.mp ar).1 (Finset.mem_inter.mp ar).2
      have sq' : SquareFree (flip G) := by
        intro a b c d ab cd ac ad bc bd
        exact sq cd ab ac bc ad bd
      have r2 := common_columns (flip G) (flip H) (flip K) (transpose G H K e) sq' S V R U hs hv
        (fun _ s _ r => bh _ r _ s) (fun _ v _ u => bk _ u _ v)
        (Finset.mem_inter.mp bs).1 (Finset.mem_inter.mp bs).2
      by_cases single : (R∩U).card ≤ 1
      · exact (Nat.mul_le_mul single c2).trans (by decide)
      · have col : (S∩V).card ≤ 1 := by
          obtain ⟨x,hx,y,hy,xy⟩ := Finset.one_lt_card.mp (Nat.lt_of_not_ge single)
          apply Finset.card_le_one.mpr
          intro p hp q hq
          have hit (r : A) (hr : r∈R∩U) (t : B) (ht : t∈S∩V) : G r t :=
            common G H K e (bh _ (Finset.mem_inter.mp hr).1 _ (Finset.mem_inter.mp ht).1)
              (bk _ (Finset.mem_inter.mp hr).2 _ (Finset.mem_inter.mp ht).2)
          by_contra ne
          exact sq xy ne (hit x hx p hp) (hit x hx q hq) (hit y hy p hp) (hit y hy q hq)
        exact (Nat.mul_le_mul r2 col).trans (by decide)
    · simp [Finset.not_nonempty_iff_eq_empty.mp ec]
  · simp [Finset.not_nonempty_iff_eq_empty.mp er]

end FiniteBlocks
end VertexPeel.FactorMatching

#print axioms VertexPeel.FactorMatching.rectangle_overlap
