import PEqualNP.Outside.L_meta_615
import PEqualNP.Defs.TopForm

namespace VertexPeel.WrongSupports
open PEqualNP.TopForm
open scoped BigOperators

variable {n : ℕ}
abbrev Family (n : ℕ) := Finset (Finset (Fin n))
abbrev HasEdge (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) :=
  ∃ u ∈ X, ∃ v ∈ X, G.Adj u v

private def smallUnion (F : Family n) := F.biUnion id

private theorem union_size {F : Family n} {k : ℕ} (small : ∀ X ∈ F, X.card ≤ k) :
    (smallUnion F).card ≤ F.card * k := by
  calc
    (smallUnion F).card ≤ ∑ X ∈ F, X.card := Finset.card_biUnion_le
    _ ≤ ∑ _X ∈ F, k := Finset.sum_le_sum small
    _ = _ := by simp

private def commonSet (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (U : Finset (Fin n)) :=
  (U.powersetCard 2).biUnion fun p => Finset.univ.filter fun v => ∀ u ∈ p, G.Adj u v

private theorem common_size (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (sq : NoFourCycle G)
    (U : Finset (Fin n)) : (commonSet G U).card ≤ U.card.choose 2 := by
  unfold commonSet
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _p ∈ U.powersetCard 2, 1 := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨a,b,ne,eq⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hp).2
      apply le_trans _ (sq a b ne)
      apply Finset.card_le_card
      intro x hx
      obtain ⟨_,conn⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,conn _ (by simp [eq]),conn _ (by simp [eq])⟩
    _ = _ := by simp

/-- If each member of a disjoint family meets a neighbor of Y, a short Y must
contain a common neighbor of two distinct vertices from the family. -/
private theorem common_hits (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (F : Family n) (disj : (F : Set (Finset (Fin n))).Pairwise Disjoint) (Y : Finset (Fin n))
    (small : Y.card < F.card) (cross : ∀ X ∈ F, ∃ a ∈ X, ∃ b ∈ Y, G.Adj a b) :
    ∃ b ∈ Y, b ∈ commonSet G (smallUnion F) := by
  classical
  have pick (X : F) := cross X.val X.property
  let a (X : F) := (pick X).choose
  have ax (X : F) : a X ∈ X.val := (pick X).choose_spec.1
  have nb (X : F) := (pick X).choose_spec.2
  let b (X : F) : Y := ⟨(nb X).choose,(nb X).choose_spec.1⟩
  have ab (X : F) : G.Adj (a X) (b X) := (nb X).choose_spec.2
  obtain ⟨X,Z,ne,eq⟩ := Fintype.exists_ne_map_eq_of_card_lt b (by simpa using small)
  have az : a X ≠ a Z := by
    intro h
    exact (Finset.disjoint_left.mp (disj X.property Z.property (fun e => ne (Subtype.ext e))))
      (ax X) (h ▸ ax Z)
  have inU (V : F) : a V ∈ smallUnion F := Finset.mem_biUnion.mpr ⟨V.val,V.property,ax V⟩
  refine ⟨b X,(b X).property,Finset.mem_biUnion.mpr ⟨{a X,a Z},?_,?_⟩⟩
  · exact Finset.mem_powersetCard.mpr ⟨Finset.insert_subset (inU X) (Finset.singleton_subset_iff.mpr (inU Z)),
      by simp [az]⟩
  · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl|hz
    · exact ab X
    · have wZ := Finset.mem_singleton.mp hz
      rw [wZ,eq]
      exact ab Z

abbrev HitsAll (T : Finset (Fin n)) (F : Family n) := ∀ X ∈ F, ∃ v ∈ X, v ∈ T

/-- A dichotomy for cross-adjacent families of small independent supports.
The certificate is independent of the order, maximum degree and cover number of the graph. -/
theorem transversal (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (sq : NoFourCycle G)
    (F H : Family n) (p q : ℕ) (leftSize : ∀ X ∈ F, X.card ≤ p) (rightSize : ∀ Y ∈ H, Y.card ≤ q)
    (cross : ∀ X ∈ F, ∀ Y ∈ H, ∃ a ∈ X, ∃ b ∈ Y, G.Adj a b) :
    (∃ T, T.card ≤ q*p ∧ HitsAll T F) ∨
      (∃ T, T.card ≤ ((q+1)*p).choose 2 ∧ HitsAll T H) := by
  classical
  by_cases he : (∅ : Finset (Fin n)) ∈ F
  · right
    exact ⟨∅,by simp,fun Y hY => by obtain ⟨_,falseMem,_⟩ := cross _ he _ hY; simp at falseMem⟩
  let packs := F.powerset.filter (fun (A : Family n) => (A : Set (Finset (Fin n))).Pairwise Disjoint)
  obtain ⟨P,hP,maxP⟩ := Finset.exists_max_image packs Finset.card ⟨∅,by simp [packs]⟩
  obtain ⟨subP,pairP⟩ := Finset.mem_filter.mp hP
  have incl := Finset.mem_powerset.mp subP
  by_cases many : q+1 ≤ P.card
  · obtain ⟨A,subA,cardA⟩ := Finset.exists_subset_card_eq many
    have disj : (A : Set (Finset (Fin n))).Pairwise Disjoint := fun {_} hx {_} hy hn => pairP (subA hx) (subA hy) hn
    have bound := union_size (F:=A) (fun X hX => leftSize X (incl (subA hX)))
    right
    refine ⟨commonSet G (smallUnion A),(common_size G sq _).trans (Nat.choose_le_choose 2 (cardA ▸ bound)),?_⟩
    intro Y hY
    exact common_hits G A disj Y (by have := rightSize Y hY; omega)
      (fun X hX => cross X (incl (subA hX)) Y hY)
  · left
    refine ⟨smallUnion P,(union_size (F:=P) (fun X hX => leftSize X (incl hX))).trans
      (Nat.mul_le_mul_right _ (by omega)),?_⟩
    intro X hX
    by_contra! miss
    have nx : X ∉ P := by
      intro xp
      obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr (fun emp => he (emp ▸ hX))
      exact miss a ha (Finset.mem_biUnion.mpr ⟨X,xp,ha⟩)
    have pair' : ((insert X P : Family n) : Set (Finset (Fin n))).Pairwise Disjoint := by
      rw [Finset.coe_insert,Set.pairwise_insert]
      refine ⟨pairP,?_⟩
      intro Y yP _
      have ds : Disjoint X Y := Finset.disjoint_left.mpr (fun {v} hv hy =>
        miss v hv (Finset.mem_biUnion.mpr ⟨Y,yP,hy⟩))
      exact ⟨ds,ds.symm⟩
    have hp := maxP (insert X P) (Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.insert_subset hX incl),pair'⟩)
    rw [Finset.card_insert_of_notMem nx] at hp
    omega

private noncomputable def errors (G : SimpleGraph (Fin n)) (k : ℕ) (f : Finset (Fin n) → Prop) : Family n := by
  classical exact Finset.univ.filter (fun X => X.card ≤ k ∧ ¬ HasEdge G X ∧ f X)

theorem cross_of_sound_and (G : SimpleGraph (Fin n)) (f g : Finset (Fin n) → Prop)
    (mf : ∀ ⦃X Y⦄, X ⊆ Y → f X → f Y) (mg : ∀ ⦃X Y⦄, X ⊆ Y → g X → g Y)
    (sound : ∀ X, f X → g X → HasEdge G X)
    {X Y} (fx : f X) (gy : g Y) (ix : ¬HasEdge G X) (iy : ¬HasEdge G Y) :
    ∃ a ∈ X, ∃ b ∈ Y, G.Adj a b := by
  obtain ⟨a,ha,b,hb,ab⟩ := sound (X ∪ Y) (mf Finset.subset_union_left fx) (mg Finset.subset_union_right gy)
  rcases Finset.mem_union.mp ha with hax|hay <;> rcases Finset.mem_union.mp hb with hbx|hby
  · exact (ix ⟨a,hax,b,hbx,ab⟩).elim
  · exact ⟨a,hax,b,hby,ab⟩
  · exact ⟨b,hbx,a,hay,ab.symm⟩
  · exact (iy ⟨a,hay,b,hby,ab⟩).elim

/-- After setting a bounded set of coordinates to zero, one child of any sound AND
is sound on all supports up to its respective size threshold. No rank restriction
on the original child functions is assumed. -/
theorem sound_child (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (sq : NoFourCycle G)
    (f g : Finset (Fin n) → Prop)
    (mf : ∀ ⦃X Y⦄, X ⊆ Y → f X → f Y) (mg : ∀ ⦃X Y⦄, X ⊆ Y → g X → g Y)
    (sound : ∀ X, f X → g X → HasEdge G X) (p q : ℕ) :
    (∃ T : Finset (Fin n), T.card ≤ q*p ∧ ∀ X, Disjoint X T → X.card ≤ p → f X → HasEdge G X) ∨
    (∃ T : Finset (Fin n), T.card ≤ ((q+1)*p).choose 2 ∧ ∀ Y, Disjoint Y T → Y.card ≤ q → g Y → HasEdge G Y) := by
  classical
  have err (k) (h : Finset (Fin n) → Prop) (X : Finset (Fin n)) :
      X ∈ errors G k h ↔ X.card ≤ k ∧ ¬HasEdge G X ∧ h X := by simp [errors]
  have strip (k) (h : Finset (Fin n) → Prop) (T) (hit : HitsAll T (errors G k h)) :
      ∀ X, Disjoint X T → X.card ≤ k → h X → HasEdge G X := by
    intro X clear card on
    by_contra off
    obtain ⟨v,hv,ht⟩ := hit X ((err k h X).mpr ⟨card,off,on⟩)
    exact Finset.disjoint_left.mp clear hv ht
  have result := transversal G sq (errors G p f) (errors G q g) p q
    (fun X hx => ((err _ _ _).mp hx).1) (fun Y hy => ((err _ _ _).mp hy).1)
    (by
      intro X hx Y hy
      obtain ⟨_,ix,fx⟩ := (err _ _ _).mp hx
      obtain ⟨_,iy,gy⟩ := (err _ _ _).mp hy
      exact cross_of_sound_and G f g mf mg sound fx gy ix iy)
  exact result.imp (fun ⟨T,ht,hl⟩ => ⟨T,ht,strip _ _ _ hl⟩)
    (fun ⟨T,ht,hr⟩ => ⟨T,ht,strip _ _ _ hr⟩)

/-- Maximum size needed for a positive witness of a monotone predicate. -/
abbrev WitnessWidth (f : Finset (Fin n) → Prop) (k : ℕ) :=
  ∀ X, f X → ∃ W ⊆ X, W.card ≤ k ∧ f W

/-- The child agrees on every input with zeros in the coordinates in T. -/
abbrev ExactOff (G : SimpleGraph (Fin n)) (f : Finset (Fin n) → Prop) (T : Finset (Fin n)) :=
  ∀ X, Disjoint X T → (f X ↔ HasEdge G X)

/-- An AND computing G with bounded witness widths has a child already computing
the full restricted G after a bounded number of coordinates are set to zero. -/
theorem exact_child_after_deletion (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (sq : NoFourCycle G) (f g : Finset (Fin n) → Prop)
    (mf : ∀ ⦃X Y⦄, X ⊆ Y → f X → f Y) (mg : ∀ ⦃X Y⦄, X ⊆ Y → g X → g Y)
    (exactAnd : ∀ X, (f X ∧ g X) ↔ HasEdge G X) (p q : ℕ)
    (wf : WitnessWidth f p) (wg : WitnessWidth g q) :
    (∃ T : Finset (Fin n), T.card ≤ q*p ∧ ExactOff G f T) ∨
    (∃ T : Finset (Fin n), T.card ≤ ((q+1)*p).choose 2 ∧ ExactOff G g T) := by
  have upgrade (h : Finset (Fin n) → Prop) (k : ℕ) (w : WitnessWidth h k)
      (complete : ∀ X, HasEdge G X → h X) (T : Finset (Fin n))
      (limited : ∀ X, Disjoint X T → X.card ≤ k → h X → HasEdge G X) : ExactOff G h T := by
    intro X hx
    refine ⟨?_,complete X⟩
    intro on
    obtain ⟨W,sub,card,hw⟩ := w X on
    obtain ⟨a,ha,b,hb,adj⟩ := limited W (Finset.disjoint_left.mpr (fun {_} ha ht =>
      Finset.disjoint_left.mp hx (sub ha) ht)) card hw
    exact ⟨a,sub ha,b,sub hb,adj⟩
  have r := sound_child G sq f g mf mg (fun X a b => (exactAnd X).mp ⟨a,b⟩) p q
  exact r.imp
    (fun ⟨T,ht,hl⟩ => ⟨T,ht,upgrade f p wf (fun X e => ((exactAnd X).mpr e).1) T hl⟩)
    (fun ⟨T,ht,hr⟩ => ⟨T,ht,upgrade g q wg (fun X e => ((exactAnd X).mpr e).2) T hr⟩)

#print axioms exact_child_after_deletion
#print axioms transversal
#print axioms sound_child
end VertexPeel.WrongSupports
