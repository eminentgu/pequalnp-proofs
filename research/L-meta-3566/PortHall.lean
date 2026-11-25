import TwoPort
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.Hall.Finite

namespace VertexPeel.PortHall

open PEqualNP.TopForm

/-- An embedded six-cycle represented by its two triples; extra edges are allowed. -/
def SixCrown {n} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ X Y : Fin 3 → Fin n, Function.Injective X ∧ Function.Injective Y ∧
    (∀ i j, X i ≠ Y j) ∧ ∀ i j, i≠j → G.Adj (X i) (Y j)

variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {κ : Type*} [DecidableEq κ]

/-- Every choice of a different user of each label contains a graph edge. -/
def Blocked (U : Finset (Fin n)) (K : Fin n → Finset κ) : Prop :=
  ∀ x ∈ U, ∀ Y : κ → Fin n,
    (∀ p ∈ K x, Y p ∈ U ∧ Y p≠x ∧ p ∈ K (Y p)) →
    ∃ p ∈ K x, ∃ q ∈ K x, G.Adj (Y p) (Y q)

omit [DecidableRel G.Adj] [DecidableEq κ] in
private theorem nonnested {U : Finset (Fin n)} {K : Fin n → Finset κ} (blocked : Blocked G U K)
    {x y : Fin n} (hx : x ∈ U) (hy : y ∈ U) (ne : y≠x) : ¬ K x ⊆ K y := by
  intro incl
  obtain ⟨_,_,_,_,edge⟩ := blocked x hx (fun _ => y) (fun _ h => ⟨hy,ne,incl h⟩)
  exact edge.ne rfl

omit [DecidableRel G.Adj] in
private theorem cross {U : Finset (Fin n)} {K : Fin n → Finset κ} (blocked : Blocked G U K)
    {x a b : Fin n} (hx : x ∈ U) {p q : κ} (pq : p≠q) (ports : K x={p,q})
    (ha : a ∈ U) (ax : a≠x) (pa : p ∈ K a) (hb : b ∈ U) (bx : b≠x) (qb : q ∈ K b) : G.Adj a b := by
  let Y (k : κ) := if k=p then a else b
  obtain ⟨i,_,j,_,edge⟩ := blocked x hx Y (by
    intro k hk
    rcases (show k=p ∨ k=q by simpa [ports] using hk) with first|second
    · subst k
      simpa [Y] using (show a ∈ U ∧ a≠x ∧ p ∈ K a from ⟨ha,ax,pa⟩)
    · subst k
      simpa [Y,pq.symm] using (show b ∈ U ∧ b≠x ∧ q ∈ K b from ⟨hb,bx,qb⟩))
  by_cases hi : i=p <;> by_cases hj : j=p <;> simp [Y,hi,hj] at edge
  · exact edge
  · exact edge.symm

private theorem constant_or_injective (sq : NoFourCycle G) {X Y : Fin 3 → Fin n}
    (inj : Function.Injective X) (edges : ∀ i j, i≠j → G.Adj (X i) (Y j)) :
    (∃ y, ∀ i, Y i=y) ∨ Function.Injective Y := by
  classical
  by_cases separate : Function.Injective Y
  · exact Or.inr separate
  left
  unfold Function.Injective at separate
  push Not at separate
  obtain ⟨i,j,same,ij⟩ := separate
  refine ⟨Y i,?_⟩
  intro k
  by_cases ik : i=k
  · exact ik ▸ rfl
  by_cases jk : j=k
  · exact jk ▸ same.symm
  by_contra diff
  have small := Finset.card_le_one.mp (sq (Y k) (Y i) diff)
  apply ij
  apply inj
  apply small
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(edges i k ik).symm, same.symm ▸ (edges i j ij).symm⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(edges j k jk).symm,(edges j i ij.symm).symm⟩

/-- A failure of the finite Hall inequality forces an embedded six-cycle. -/
theorem crown_of_deficit (sq : NoFourCycle G) (U : Finset (Fin n)) (K : Fin n → Finset κ)
    (capacity : ∀ x ∈ U, (K x).card≤2) (blocked : Blocked G U K)
    (deficit : (U.biUnion K).card<U.card) : SixCrown G := by
  classical
  let F := U.powerset.filter fun W => (W.biUnion K).card<W.card
  obtain ⟨V,inF,minimal⟩ := F.exists_min_image Finset.card ⟨U,by simp [F,deficit]⟩
  obtain ⟨subset,short⟩ : V ⊆ U ∧ (V.biUnion K).card<V.card := by simpa [F] using inF
  have shared (x) (hx : x ∈ V) (p) (hp : p ∈ K x) : ∃ y ∈ V, y≠x ∧ p ∈ K y := by
    by_contra missing
    let W := V.erase x
    have trim : W.card+1 = V.card := Finset.card_erase_add_one hx
    have enough : W.card ≤ (W.biUnion K).card := by
      by_contra! bad
      have win : W ∈ F := by simp [F,W,((Finset.erase_subset x V).trans subset),bad]
      have := minimal W win
      omega
    have absent : p ∉ W.biUnion K := by
      intro found
      obtain ⟨y,hy,py⟩ := Finset.mem_biUnion.mp found
      exact missing ⟨y,(Finset.mem_erase.mp hy).2,(Finset.mem_erase.mp hy).1,py⟩
    have incl : insert p (W.biUnion K) ⊆ V.biUnion K := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl|ha
      · exact Finset.mem_biUnion.mpr ⟨x,hx,hp⟩
      · obtain ⟨y,hy,ay⟩ := Finset.mem_biUnion.mp ha
        exact Finset.mem_biUnion.mpr ⟨y,(Finset.mem_erase.mp hy).2,ay⟩
    have count := Finset.card_le_card incl
    rw [Finset.card_insert_of_notMem absent] at count
    omega
  have two (x) (hx : x ∈ V) : (K x).card=2 := by
    have cap := capacity x (subset hx)
    by_contra notTwo
    by_cases empty : K x=∅
    · obtain ⟨p,hp,_,_,_⟩ := blocked x (subset hx) (fun _ => x) (by simp [empty])
      simp [empty] at hp
    have positive := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty)
    obtain ⟨p,one⟩ := Finset.card_eq_one.mp (show (K x).card=1 by omega)
    obtain ⟨y,hy,ne,py⟩ := shared x hx p (by simp [one])
    apply nonnested G blocked (subset hx) (subset hy) ne
    simpa [one] using py
  let users (p : κ) := Finset.univ.filter fun x => x∈V ∧ p∈K x
  have crowded : ∃ p ∈ V.biUnion K, 3 ≤ (users p).card := by
    by_contra! no
    have count := Finset.sum_card_eq_sum_biUnion_card K V
    have left : (∑ x ∈ V, (K x).card) = V.card*2 := by
      rw [Finset.sum_congr rfl two]; simp
    have right : (∑ p ∈ V.biUnion K, (users p).card) ≤ (V.biUnion K).card*2 := by
      calc
        _ ≤ ∑ _p ∈ V.biUnion K, 2 := Finset.sum_le_sum (fun p hp => by have := no p hp; omega)
        _ = _ := by simp
    change (∑ x ∈ V, (K x).card) = ∑ p ∈ V.biUnion K, (users p).card at count
    omega
  obtain ⟨p,_,many⟩ := crowded
  obtain ⟨S,subS,three⟩ := Finset.exists_subset_card_eq many
  let f : Fin 3 ≃ S := (Fintype.equivFinOfCardEq (by simpa using three)).symm
  let X (i : Fin 3) := (f i).val
  have Xin : Function.Injective X := Subtype.val_injective.comp f.injective
  have use (i : Fin 3) : X i∈V ∧ p∈K (X i) := (Finset.mem_filter.mp (subS (f i).property)).2
  have other (i : Fin 3) : ∃ q, q≠p ∧ K (X i)={p,q} := by
    have cnt := Finset.card_erase_add_one (use i).2
    have sz := two (X i) (use i).1
    obtain ⟨q,eq⟩ := Finset.card_eq_one.mp (show ((K (X i)).erase p).card=1 by omega)
    have mem : q∈(K (X i)).erase p := by simp [eq]
    exact ⟨q,(Finset.mem_erase.mp mem).1,by rw [← Finset.insert_erase (use i).2,eq]⟩
  choose Q distinct ports using other
  have Qin : Function.Injective Q := by
    intro i j eq
    by_contra ij
    apply nonnested G blocked (subset (use i).1) (subset (use j).1) (Xin.ne (Ne.symm ij))
    rw [ports i,ports j,eq]
  have partners (i : Fin 3) : ∃ y ∈ V, y≠X i ∧ Q i∈K y :=
    shared (X i) (use i).1 (Q i) (by simp [ports i])
  choose Y ymem ydiff yport using partners
  have edges (i j : Fin 3) (ij : i≠j) : G.Adj (X i) (Y j) :=
    cross G blocked (subset (use j).1) (distinct j).symm (ports j) (subset (use i).1)
      (Xin.ne ij) (use i).2 (subset (ymem j)) (ydiff j) (yport j)
  have disjoint (i j : Fin 3) : X i ≠ Y j := by
    by_cases ij : i=j
    · subst j; exact (ydiff i).symm
    · exact (edges i j ij).ne
  rcases constant_or_injective G sq Xin edges with ⟨y,allY⟩|Yin
  · have allQ : Finset.univ.image Q ⊆ K y := by
      intro q hq
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
      exact allY i ▸ yport i
    have count := Finset.card_le_card allQ
    rw [Finset.card_image_of_injective _ Qin] at count
    have cap := capacity y (allY 0 ▸ subset (ymem 0))
    simp at count
    omega
  · exact ⟨X,Y,Xin,Yin,disjoint,edges⟩

theorem card_le (sq : NoFourCycle G) (noSix : ¬SixCrown G)
    (U : Finset (Fin n)) (K : Fin n → Finset κ) (capacity : ∀ x ∈ U, (K x).card≤2)
    (blocked : Blocked G U K) : U.card ≤ (U.biUnion K).card := by
  by_contra! deficit
  exact noSix (crown_of_deficit G sq U K capacity blocked deficit)

/-- Every selected vertex can simultaneously receive one of its own labels. -/
theorem assignment (sq : NoFourCycle G) (noSix : ¬SixCrown G)
    (U : Finset (Fin n)) (K : Fin n → Finset κ) (capacity : ∀ x ∈ U, (K x).card≤2)
    (blocked : Blocked G U K) :
    ∃ f : U → κ, Function.Injective f ∧ ∀ x, f x ∈ K x.val := by
  classical
  let options (x : U) := K x.val
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective' options).mp
  intro T
  let S := T.image Subtype.val
  have incl : S ⊆ U := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact i.property
  have bound := card_le G sq noSix S K (fun x hx => capacity x (incl hx)) (by
    intro x hx Y hy
    exact blocked x (incl hx) Y (fun p hp => ⟨incl (hy p hp).1,(hy p hp).2⟩))
  have count : S.card=T.card := Finset.card_image_of_injective _ Subtype.val_injective
  have same : S.biUnion K=T.biUnion options := by
    ext p
    simp [S,options]
  rwa [count,same] at bound

#print axioms assignment
#print axioms crown_of_deficit
#print axioms card_le
end VertexPeel.PortHall
