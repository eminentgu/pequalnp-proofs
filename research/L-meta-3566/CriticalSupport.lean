import CoverKernel

namespace VertexPeel.CriticalSupport

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.CoverPromise PEqualNP.TopForm
open VertexPeel.CoverKernel

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- A leaf is critical if deleting its incident edge strictly decreases the minimum cover size. -/
def AllLeavesCritical : Prop := ∀ a, G.degree a = 1 → Loc.tau (G.deleteIncidenceSet a) < Loc.tau G

private theorem high_bound (square : NoFourCycle G) (X T : Finset (Fin n))
    (high : ∀ v ∈ X, 2 ≤ G.degree v) (toT : ∀ v ∈ X, G.neighborFinset v ⊆ T) :
    X.card ≤ T.card.choose 2 := by
  classical
  let pair (v : Fin n) : Finset (Fin n) :=
    if h : 2 ≤ (G.neighborFinset v).card then (Finset.exists_subset_card_eq h).choose else ∅
  have spec (v : Fin n) (hv : v ∈ X) : pair v ⊆ G.neighborFinset v ∧ (pair v).card = 2 := by
    have h : 2 ≤ (G.neighborFinset v).card := by simpa using high v hv
    simpa only [pair,dite_eq_left h] using (Finset.exists_subset_card_eq h).choose_spec
  rw [← Finset.card_powersetCard]
  apply Finset.card_le_card_of_injOn pair
  · intro v hv
    exact Finset.mem_powersetCard.mpr ⟨(spec v hv).1.trans (toT v hv),(spec v hv).2⟩
  · intro a ha b hb eq
    by_contra ne
    have incl : pair a ⊆ Finset.univ.filter (fun u => G.Adj a u ∧ G.Adj b u) := by
      intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(G.mem_neighborFinset a u).mp ((spec a ha).1 hu),
        (G.mem_neighborFinset b u).mp ((spec b hb).1 (eq ▸ hu))⟩
    have cap := (Finset.card_le_card incl).trans (square a b ne)
    rw [(spec a ha).2] at cap
    omega

private noncomputable def hub (v : Fin n) : Fin n :=
  if h : ∃ u, G.neighborFinset v = {u} then h.choose else v

private theorem hub_spec (v : Fin n) (h : G.degree v = 1) : G.neighborFinset v = {hub G v} := by
  classical
  have one : (G.neighborFinset v).card = 1 := by simpa using h
  have e := Finset.card_eq_one.mp one
  simpa [hub,e] using e.choose_spec

private theorem split_count (square : NoFourCycle G) (noTwins : ¬ TwinLeaves G) (X T : Finset (Fin n))
    (pos : ∀ v ∈ X, 0 < G.degree v) (all : ∀ v ∈ X, G.neighborFinset v ⊆ T) :
    X.card ≤ T.card + T.card.choose 2 := by
  classical
  let L := X.filter fun v => G.degree v = 1
  have low : L.card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (hub G)
    · intro v hv
      obtain ⟨hx,d⟩ := Finset.mem_filter.mp hv
      apply all v hx
      simp [hub_spec G v d]
    · intro a ha b hb eq
      by_contra ne
      exact noTwins ⟨a,b,hub G a,ne,hub_spec G a (Finset.mem_filter.mp ha).2,
        eq ▸ hub_spec G b (Finset.mem_filter.mp hb).2⟩
  have hi := high_bound G square (X \ L) T (by
    intro v hv
    obtain ⟨hx,notL⟩ := Finset.mem_sdiff.mp hv
    have n1 : G.degree v ≠ 1 := fun e => notL (Finset.mem_filter.mpr ⟨hx,e⟩)
    have := pos v hx
    omega) (fun v hv => all v (Finset.mem_sdiff.mp hv).1)
  have := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun v => G.degree v = 1) X)
  change (X \ L).card + L.card = X.card at this
  omega

/-- For two minimum covers, all vertices outside their union see only their intersection. -/
theorem two_covers (square : NoFourCycle G) (noTwins : ¬ TwinLeaves G) (T S : Finset (Fin n))
    (ct : IsVertexCover G T) (cs : IsVertexCover G S) :
    (active G).card ≤ T.card + S.card + (T ∩ S).card.choose 2 := by
  classical
  let X := active G \ (T ∪ S)
  have off (v : Fin n) (hv : v ∈ X) := Finset.mem_sdiff.mp hv
  have b := split_count G square noTwins X (T ∩ S) (fun v h => (Finset.mem_filter.mp (off v h).1).2) (by
    intro v hv u hu
    have e := (G.mem_neighborFinset v u).mp hu
    have hn := (off v hv).2
    exact Finset.mem_inter.mpr ⟨(ct v u e).resolve_left (fun h => hn (Finset.mem_union_left _ h)),
      (cs v u e).resolve_left (fun h => hn (Finset.mem_union_right _ h))⟩)
  have tot : (active G).card ≤ X.card + (T ∪ S).card := Finset.card_le_card_sdiff_add_card
  have sz := Finset.card_union_add_card_inter T S
  omega

private theorem choose_two_gap {a t : ℕ} (h : a + 2 ≤ t) (big : 3 ≤ t) :
    t + a.choose 2 ≤ t.choose 2 := by
  have le := Nat.choose_le_choose 2 (show a ≤ t-2 by omega)
  obtain ⟨b,hb⟩ : ∃ b, t=b+3 := ⟨t-3,by omega⟩
  subst t
  simp [Nat.choose_succ_succ'] at le ⊢
  omega

private theorem singles_and_pairs (b a : ℕ) (h : 3 ≤ b+a) : b + a.choose 2 ≤ (b+a).choose 2 := by
  rcases b with _|b
  · simp
  by_cases zero : b=0
  · subst b
    have h2 : 2 ≤ a := by omega
    have eq : (a + 1).choose 2 = a + a.choose 2 := by rw [Nat.choose_succ_succ' a 1, Nat.choose_one_right]
    simp only [Nat.zero_add] at *
    rw [Nat.add_comm 1 a,eq]
    omega
  · have gap := choose_two_gap (a := a) (t := (b+1)+a) (by omega) h
    omega

/-- If every leaf is critical, either two minimum covers differ in at least two positions,
or each exterior leaf monopolizes its hub: the hub has no other neighbor outside the cover. -/
private theorem unique_outside (critical : AllLeavesCritical G) (T : Finset (Fin n))
    (sz : T.card = Loc.tau G)
    (close : ∀ S, IsVertexCover G S → S.card = T.card → (S \ T).card ≤ 1)
    {a : Fin n} (out : a ∉ T) (one : G.degree a = 1) {v : Fin n}
    (off : v ∉ T) (edge : G.Adj (hub G a) v) : v = a := by
  classical
  let H := G.deleteIncidenceSet a
  obtain ⟨S,coverH,sizeH⟩ := Loc.tau_attained H
  let U := insert a S
  have cu : IsVertexCover G U := by
    intro i j adj
    by_cases ia : i=a
    · exact Or.inl (ia ▸ Finset.mem_insert_self _ _)
    by_cases ja : j=a
    · exact Or.inr (ja ▸ Finset.mem_insert_self _ _)
    exact (coverH i j (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨adj,ia,ja⟩)).imp
      (fun h => Finset.mem_insert_of_mem h) (fun h => Finset.mem_insert_of_mem h)
  have strict := critical a one
  change Loc.tau H < Loc.tau G at strict
  have low := Loc.tau_le G U cu
  have up : U.card ≤ S.card+1 := Finset.card_insert_le a S
  have same : U.card=T.card := by omega
  have hubout : hub G a ∉ S := by
    intro inside
    have coverG : IsVertexCover G S := by
      intro i j adj
      have fix (w : Fin n) (h : G.Adj a w) : w ∈ S := by
        have mem := (G.mem_neighborFinset a w).mpr h
        rw [hub_spec G a one,Finset.mem_singleton] at mem
        exact mem ▸ inside
      by_cases ia : i=a
      · exact Or.inr (fix j (ia ▸ adj))
      by_cases ja : j=a
      · exact Or.inl (fix i (ja ▸ adj.symm))
      exact coverH i j (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨adj,ia,ja⟩)
    have := Loc.tau_le G S coverG
    omega
  have edgeA : G.Adj a (hub G a) := (G.mem_neighborFinset a _).mp (by simp [hub_spec G a one])
  have hubNot : hub G a ∉ U := by simp [U,edgeA.ne.symm,hubout]
  have aU : a ∈ U \ T := Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self _ _,out⟩
  have vU : v ∈ U \ T := Finset.mem_sdiff.mpr ⟨(cu _ _ edge).resolve_left hubNot,off⟩
  exact Finset.card_le_one.mp (close U cu same) _ vU _ aU

/-- For cover number t≥3, a square-free graph with no twins or cover-stable leaf
has at most t + binom(t,2) non-isolated vertices. No condition on triangles is needed. -/
theorem active_bound (square : NoFourCycle G) (noTwins : ¬ TwinLeaves G) (critical : AllLeavesCritical G)
    (big : 3 ≤ Loc.tau G) : (active G).card ≤ Loc.tau G + (Loc.tau G).choose 2 := by
  classical
  obtain ⟨T,ct,sz⟩ := Loc.tau_attained G
  rw [← sz] at big ⊢
  by_cases far : ∃ S, IsVertexCover G S ∧ S.card = T.card ∧ 2 ≤ (S \ T).card
  · obtain ⟨S,cs,st,diff⟩ := far
    have tot := two_covers G square noTwins T S ct cs
    have counts := Finset.card_sdiff_add_card_inter S T
    rw [Finset.inter_comm S T,st] at counts
    have gap := choose_two_gap (a := (T ∩ S).card) (t := T.card) (by omega) big
    omega
  · have close (S : Finset (Fin n)) (cs : IsVertexCover G S) (st : S.card = T.card) : (S \ T).card ≤ 1 := by
      by_contra! h
      exact far ⟨S,cs,st,by omega⟩
    let E := active G \ T
    let L := E.filter fun v => G.degree v = 1
    let B := L.image (hub G)
    have ofL {v : Fin n} (hv : v ∈ L) := Finset.mem_filter.mp hv
    have ofE {v : Fin n} (hv : v ∈ E) := Finset.mem_sdiff.mp hv
    have bT : B ⊆ T := by
      intro u hu
      obtain ⟨v,hl,rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨he,deg⟩ := ofL hl
      have adj : G.Adj v (hub G v) := (G.mem_neighborFinset v _).mp (by simp [hub_spec G v deg])
      exact (ct _ _ adj).resolve_left (ofE he).2
    have bsz : B.card = L.card := Finset.card_image_of_injOn (by
      intro a ha b hb eq
      by_contra ne
      exact noTwins ⟨a,b,hub G a,ne,hub_spec G a (ofL ha).2,eq ▸ hub_spec G b (ofL hb).2⟩)
    have bound := high_bound G square (E \ L) (T \ B) (by
      intro v hv
      obtain ⟨he,notL⟩ := Finset.mem_sdiff.mp hv
      have pos := (Finset.mem_filter.mp (ofE he).1).2
      have n1 : G.degree v ≠ 1 := fun h => notL (Finset.mem_filter.mpr ⟨he,h⟩)
      omega) (by
      intro v hv u hu
      obtain ⟨he,notL⟩ := Finset.mem_sdiff.mp hv
      have adj := (G.mem_neighborFinset v u).mp hu
      refine Finset.mem_sdiff.mpr ⟨(ct _ _ adj).resolve_left (ofE he).2,?_⟩
      intro mem
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp mem
      have eq := unique_outside G critical T sz close (ofE (ofL ha).1).2 (ofL ha).2 (ofE he).2 adj.symm
      exact notL (eq ▸ ha))
    have sumB := Finset.card_sdiff_add_card_eq_card bT
    have sumL : (E \ L).card + L.card = E.card := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ E)
    have cost := singles_and_pairs B.card (T \ B).card (by omega)
    rw [show B.card + (T \ B).card = T.card by omega] at cost
    have tot : (active G).card ≤ E.card+T.card := Finset.card_le_card_sdiff_add_card
    omega

/-- Two leaves with a common hub always give a cover-stable deletion. -/
theorem no_twins (critical : AllLeavesCritical G) : ¬ TwinLeaves G := by
  intro twins
  obtain ⟨a,u,edge,only,same,_,_⟩ := reduce_twin G twins
  have one := (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mpr ⟨u,edge,only⟩
  have strict := critical a one
  omega

/-- Stable leaf removal reduces every leaf-hereditary class with cover number at least
three to critical graphs on at most t + choose(t,2) non-isolated vertices. -/
theorem of_critical (P : SimpleGraph (Fin n) → Prop)
    (inherit : ∀ (H : SimpleGraph (Fin n)) (a u : Fin n), P H → H.Adj a u →
      (∀ v, H.Adj a v → v = u) → Loc.tau (H.deleteIncidenceSet a) = Loc.tau H →
      P (H.deleteIncidenceSet a))
    (kernel : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj], P H → NoFourCycle H →
      AllLeavesCritical H → (active H).card ≤ Loc.tau H + (Loc.tau H).choose 2 →
      StableExtension.Numerical H (Loc.tau H))
    (member : P G) (square : NoFourCycle G) (big : 3 ≤ Loc.tau G) :
    StableExtension.Numerical G (Loc.tau G) := by
  suffices go : ∀ m (H : SimpleGraph (Fin n)) [DecidableRel H.Adj], H.edgeFinset.card = m →
      P H → NoFourCycle H → 3 ≤ Loc.tau H → StableExtension.Numerical H (Loc.tau H) by
    let base : DecidableRel G.Adj := inferInstance
    intro inst C mono correct
    have eq : inst = base := Subsingleton.elim _ _
    subst inst
    exact @go G.edgeFinset.card G base rfl member square big base C mono correct
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro H base size prop sq large inst C mono correct
    have eq : inst = base := Subsingleton.elim _ _
    subst inst
    by_cases hc : AllLeavesCritical H
    · exact kernel H prop sq hc (active_bound H sq (no_twins H hc) hc large) C mono correct
    · unfold AllLeavesCritical at hc
      push Not at hc
      obtain ⟨a,one,ge⟩ := hc
      obtain ⟨u,edge,only⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp one
      let J := H.deleteIncidenceSet a
      have same : Loc.tau J = Loc.tau H := by
        obtain ⟨S,c,s⟩ := Loc.tau_attained H
        exact Nat.le_antisymm ((Loc.tau_le J S (fun i j e => c i j (H.deleteIncidenceSet_le a e))).trans_eq s) ge
      have less : J.edgeFinset.card < m := by
        have pos := H.degree_le_card_edgeFinset a
        change (H.deleteIncidenceSet a).edgeFinset.card < m
        rw [H.card_edgeFinset_deleteIncidenceSet,one]
        omega
      have old : StableExtension.Numerical J (Loc.tau J) := by
        let decJ : DecidableRel J.Adj := inferInstance
        intro instJ D dm dc
        have eq : instJ = decJ := Subsingleton.elim _ _
        subst instJ
        exact @ih J.edgeFinset.card less J decJ rfl (inherit H a u prop edge only same)
          (square_cut H a sq) (same.symm ▸ large) decJ D dm dc
      rw [same] at old
      exact StableExtension.step_numerical edge only old C mono correct

#print axioms active_bound
#print axioms of_critical

end VertexPeel.CriticalSupport
