import PrivatePoints
import PEqualNP.Outside.L_meta_1955

namespace PEqualNP.Research2990
variable {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]

theorem lines_meet (q : ℕ) (hq : 2 ≤ q) (hN : N = q^2+q+1)
    (degree : ∀ l, (pointsOf I l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
    (a b : Fin N) : ∃ p, I p a ∧ I p b := by
  classical
  by_contra noMeet
  have through := PEqualNP.Outside.L_meta_1955.lines_through q N I hq hN degree unique
  obtain ⟨p,hpa'⟩ := Finset.card_pos.mp (show 0 < (pointsOf I a).card by rw [degree]; omega)
  have hpa := (Finset.mem_filter.mp hpa').2
  have npb : ¬ I p b := fun e => noMeet ⟨p,hpa,e⟩
  have ne (x : ↥(pointsOf I b)) : p ≠ x.val := by
    rintro rfl
    exact npb (Finset.mem_filter.mp x.property).2
  let F (x : ↥(pointsOf I b)) : Fin N := Classical.choose (unique p x.val (ne x))
  have inc (x : ↥(pointsOf I b)) : I p (F x) ∧ I x.val (F x) :=
    (Classical.choose_spec (unique p x.val (ne x))).1
  let T := Finset.univ.filter fun l : Fin N => I p l
  let G (x : ↥(pointsOf I b)) : ↥T := ⟨F x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(inc x).1⟩⟩
  have injective : Function.Injective G := by
    intro x y same
    by_contra diff
    have dxy : x.val ≠ y.val := fun h => diff (Subtype.ext h)
    have eq : F x = F y := congrArg Subtype.val same
    obtain ⟨_, _, sole⟩ := unique x.val y.val dxy
    have eb : F x = b := (sole (F x) ⟨(inc x).2,eq ▸ (inc y).2⟩).trans
      (sole b ⟨(Finset.mem_filter.mp x.property).2,(Finset.mem_filter.mp y.property).2⟩).symm
    exact npb (eb ▸ (inc x).1)
  have eqCard : Fintype.card ↥(pointsOf I b) = Fintype.card ↥T := by
    simpa only [Fintype.card_coe] using (degree b).trans (through p).symm
  have onto := ((Fintype.bijective_iff_injective_and_card G).mpr ⟨injective,eqCard⟩).2
  obtain ⟨x,eq⟩ := onto ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpa⟩⟩
  have xa : F x = a := congrArg Subtype.val eq
  exact noMeet ⟨x.val,xa ▸ (inc x).2,(Finset.mem_filter.mp x.property).2⟩

/-- A nonempty family of k lines can cover at most 1+kq points; a pencil attains it. -/
theorem covered_card (q : ℕ) (hq : 2 ≤ q) (hN : N = q^2+q+1)
    (degree : ∀ l, (pointsOf I l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
    (Y : Finset (Fin N)) : (Y.biUnion (pointsOf I)).card ≤ 1 + Y.card*q := by
  classical
  induction Y using Finset.induction_on with
  | empty => simp
  | @insert l Y hf ih =>
    by_cases hy : Y.Nonempty
    · obtain ⟨k,hk⟩ := hy
      obtain ⟨p,hlp,hkp⟩ := lines_meet I q hq hN degree unique l k
      have common : 0 < (pointsOf I l ∩ Y.biUnion (pointsOf I)).card := by
        apply Finset.card_pos.mpr
        exact ⟨p,Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlp⟩,
          Finset.mem_biUnion.mpr ⟨k,hk,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkp⟩⟩⟩⟩
      have card := Finset.card_union_add_card_inter (pointsOf I l) (Y.biUnion (pointsOf I))
      rw [degree] at card
      rw [Finset.biUnion_insert,Finset.card_insert_of_notMem hf,Nat.add_mul]
      omega
    · have empty := Finset.not_nonempty_iff_eq_empty.mp hy
      simp [empty,degree,Nat.add_comm]

/-- Even a boundary row testing q selected lines keeps at least q point inputs on. -/
theorem many_active_points (q : ℕ) (hq : 2 ≤ q) (hN : N = q^2+q+1)
    (degree : ∀ l, (pointsOf I l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
    (Y : Finset (Fin N)) (small : Y.card ≤ q) : q ≤ (outsidePoints I Y).card := by
  classical
  have upper := covered_card I q hq hN degree unique Y
  have split : (Finset.univ : Finset (Fin N)) ⊆ Y.biUnion (pointsOf I) ∪ outsidePoints I Y := by
    intro p _
    by_cases hp : ∀ k ∈ Y, ¬I p k
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩)
    · push Not at hp
      obtain ⟨k,hk,hi⟩ := hp
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨k,hk,Finset.mem_filter.mpr ⟨by simp,hi⟩⟩)
  have total := (Finset.card_le_card split).trans (Finset.card_union_le _ _)
  simp only [Finset.card_univ, Fintype.card_fin] at total
  have mul := Nat.mul_le_mul_right q small
  rw [pow_two] at hN
  omega

#print axioms many_active_points
end PEqualNP.Research2990
