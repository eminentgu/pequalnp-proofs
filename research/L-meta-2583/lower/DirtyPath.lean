import FewUncovered

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open scoped Sym2

namespace PlaneReadOne

/-- Every OR path from a top side to a dirty AND either starts at that AND
or has a last OR whose empty child excludes it from lambda. The number of
dirty AND gates elsewhere is unrestricted. -/
theorem dirtyPathExit {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) {a g : ℕ} {b : Fin 2}
    (top : a ∈ tops G C) (dirty : g ∈ junk G C) (path : OrReaches n C (opnd C a b) g) :
    a ∈ centreless G C ∨ ∃ m ∈ orN G C \ lam G C, n+g ∈ (gateAt C m).inputs := by
  classical
  let w := opnd C a b
  let k := w-n
  have hA := PEqualNP.Outside.L_meta_1505.ao_of n C ao
  obtain ⟨hnw,hk,reach⟩ := PEqualNP.Outside.L_meta_1505.orReaches_reach n C w g path
  change k < C.gates.length at hk
  change PEqualNP.Outside.L_meta_1505.Reach n C k g at reach
  have hw : w = n+k := by dsimp [k]; omega
  simp only [junk,gatesWhere,Finset.mem_filter,Finset.mem_range] at dirty
  obtain ⟨_,hopg,_,x,hg,fx⟩ := dirty
  have emptyIn := PEqualNP.Outside.L_meta_1505.orIn_and n C g hopg
  by_cases direct : k = g
  · left
    have emptySide : side (n:=n) C a b = ∅ := by
      change orIn n C w = ∅
      rw [hw,direct,emptyIn]
    exact Finset.mem_filter.mpr ⟨top,by fin_cases b <;> first | exact Or.inl emptySide | exact Or.inr emptySide⟩
  · right
    obtain ⟨m,hm,mor,reads⟩ := PEqualNP.Outside.L_meta_1505.reach_last n C k g reach direct
    have hmk := PEqualNP.Outside.L_meta_1505.reach_lt n C hA k m hk hm
    have hml := hmk.trans_lt hk
    obtain ⟨_,p,q,hpq,hp,hq⟩ := hA m hml
    have one : n+g = p ∨ n+g = q := by simpa [hpq] using reads
    have notbelow : ¬ BelowF G C m := by
      intro below
      have val : gateVal n C m x = true := by
        show PEqualNP.Outside.L_meta_1505.W n C x (n+m) = true
        rw [PEqualNP.Outside.L_meta_1505.W_or n C x m hml mor p q hpq hp hq]
        change PEqualNP.Outside.L_meta_1505.W n C x (n+g) = true at hg
        rcases one with e | e <;> simp [← e,hg]
      have := below x val
      simp [fx] at this
    refine ⟨m,Finset.mem_sdiff.mpr ⟨?_,?_⟩,reads⟩
    · simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
      exact ⟨hml,mor,notbelow⟩
    · intro member
      obtain ⟨_,left,right,_⟩ := Finset.mem_filter.mp member
      rcases one with e | e
      · exact left.ne_empty (by simpa [opnd,hpq,← e] using emptyIn)
      · exact right.ne_empty (by simpa [opnd,hpq,← e] using emptyIn)

/-- A nonempty uncovered set always charges an extra unit beyond the count of
dirty AND gates, even when the same dirty gate serves multiple uncovered edges. -/
theorem nonemptyOverhead {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (squareFree : NoFourCycle G) (hasEdge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (normal : TopForm G C) (uncovered : (Ustar G C).Nonempty) :
    (centreless G C).Nonempty ∨ (orN G C \ lam G C).Nonempty := by
  classical
  obtain ⟨e,he⟩ := uncovered
  induction e using Sym2.inductionOn with
  | _ u v =>
    obtain ⟨a,ha,b,g,hg,_,path,_⟩ :=
      (PEqualNP.Outside.L_meta_1490 n G C squareFree hasEdge least normal).2 u v he
    rcases dirtyPathExit G C least.1 ha hg path with h | ⟨m,hm,_⟩
    · exact Or.inl ⟨a,h⟩
    · exact Or.inr ⟨m,hm⟩

variable {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (q : ℕ) (C : Circuit)
    (hq : 2 ≤ q) (order : N = q^2+q+1)
    (lines : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)

include hq order lines unique in
/-- If there are three uncovered incidences, a subthreshold circuit at order
at least three has precisely one dirty AND, zero centreless tops, and exactly
one OR outside lambda. -/
theorem threeEdgeException (big : 3 ≤ q) (least : IsLeastAO (graph I) C)
    (normal : TopForm (graph I) C) (three : (Ustar (graph I) C).card = 3)
    (small : C.size+1 < N*(q+2)) :
    (junk (graph I) C).card = 1 ∧ centreless (graph I) C = ∅ ∧
      (orN (graph I) C \ lam (graph I) C).card = 1 := by
  let G := graph I
  change (Ustar G C).card = 3 at three
  have nonempty : (Ustar G C).Nonempty := Finset.card_pos.mp (by omega)
  have hasEdge : G.edgeFinset.Nonempty :=
    nonempty.mono (by intro e he; exact (Finset.mem_sdiff.mp he).1)
  have overhead := nonemptyOverhead G C (noFour I unique) hasEdge least normal nonempty
  have dirty : 0 < (junk G C).card := by
    obtain ⟨e,he⟩ := nonempty
    induction e using Sym2.inductionOn with
    | _ u v =>
      obtain ⟨_,_,_,g,hg,_⟩ :=
        (PEqualNP.Outside.L_meta_1490 _ G C (noFour I unique) hasEdge least normal).2 u v he
      exact Finset.card_pos.mpr ⟨g,hg⟩
  have budget := uncoveredCharge I q C hq order lines unique least normal
  change N*(q+2)+2*(centreless G C).card+(junk G C).card+(orN G C \ lam G C).card ≤
      C.size+1+(Ustar G C).card+(Ustar G C).card/(q+1) at budget
  rw [three, Nat.div_eq_of_lt (show 3 < q+1 by omega)] at budget
  change (junk G C).card = 1 ∧ centreless G C = ∅ ∧ (orN G C \ lam G C).card = 1
  rw [← Finset.card_eq_zero]
  simp only [← Finset.card_pos] at overhead
  omega

include hq order lines unique in
/-- In the three-edge exceptional case, every missing incidence has a top
that receives the same mixing OR and the same dirty AND through the same side.
The fixed dirty AND is true on all three two-input assignments. -/
theorem threeEdgeCommonPath (big : 3 ≤ q) (least : IsLeastAO (graph I) C)
    (normal : TopForm (graph I) C) (three : (Ustar (graph I) C).card = 3)
    (small : C.size+1 < N*(q+2)) :
    let G := graph I
    ∃ g m : ℕ, junk G C = {g} ∧ (orN G C \ lam G C) = {m} ∧ m ∈ mixing G C ∧
      (N+N)+g ∈ (gateAt C m).inputs ∧
      ∀ u v : Fin (N+N), s(u,v) ∈ Ustar G C →
        ∃ a ∈ tops G C, ∃ b : Fin 2, gateVal (N+N) C a (pairInput u v) = true ∧
          OrReaches (N+N) C (opnd C a b) m ∧ OrReaches (N+N) C (opnd C a b) g ∧
          gateVal (N+N) C g (pairInput u v) = true := by
  classical
  let G := graph I
  obtain ⟨jc,empty,oc⟩ := threeEdgeException I q C hq order lines unique big least normal three small
  obtain ⟨g,sg⟩ := Finset.card_eq_one.mp jc
  obtain ⟨m,sm⟩ := Finset.card_eq_one.mp oc
  change (Ustar G C).card = 3 at three
  have existsEdge : (Ustar G C).Nonempty := Finset.card_pos.mp (by omega)
  have edge : G.edgeFinset.Nonempty := existsEdge.mono (by intro e he; exact (Finset.mem_sdiff.mp he).1)
  have allPaths (u v : Fin (N+N)) (he : s(u,v) ∈ Ustar G C) :
      m ∈ mixing G C ∧ (N+N)+g ∈ (gateAt C m).inputs ∧
      ∃ a ∈ tops G C, ∃ b : Fin 2, gateVal (N+N) C a (pairInput u v) = true ∧
        OrReaches (N+N) C (opnd C a b) m ∧ OrReaches (N+N) C (opnd C a b) g ∧
        gateVal (N+N) C g (pairInput u v) = true := by
    obtain ⟨a,ha,b,g',hg,ta,pg,tg⟩ :=
      (PEqualNP.Outside.L_meta_1490 _ G C (noFour I unique) edge least normal).2 u v he
    have hgg : g' = g := by simpa [G,sg] using hg
    subst g'
    have ne : (side (n:=N+N) C a b).Nonempty := by
      by_contra absent
      have blank := Finset.not_nonempty_iff_eq_empty.mp absent
      have bad : a ∈ centreless G C := Finset.mem_filter.mpr
        ⟨ha,by fin_cases b <;> first | exact Or.inl blank | exact Or.inr blank⟩
      simp [G,empty] at bad
    obtain ⟨m',hm,pm,reads⟩ :=
      PEqualNP.Outside.L_meta_1505 _ G C (noFour I unique) edge least normal g sg a ha b pg ne
    have outside : m' ∈ orN G C \ lam G C := by
      obtain ⟨out,unequal⟩ := Finset.mem_filter.mp hm
      refine Finset.mem_sdiff.mpr ⟨out,?_⟩
      intro lambda
      obtain ⟨_,left,right,_⟩ := Finset.mem_filter.mp lambda
      exact unequal (propext ⟨fun h => (left.ne_empty h).elim,fun h => (right.ne_empty h).elim⟩)
    have equal : m' = m := by simpa [G,sm] using outside
    subst m'
    exact ⟨hm,reads,a,ha,b,ta,pm,pg,tg⟩
  obtain ⟨e,he⟩ := existsEdge
  obtain ⟨⟨u,v⟩,rfl⟩ := Sym2.mk_surjective e
  obtain ⟨hm,reads,_⟩ := allPaths u v he
  exact ⟨g,m,sg,sm,hm,reads,fun u v he => (allPaths u v he).2.2⟩

end PlaneReadOne

#print axioms PlaneReadOne.dirtyPathExit
#print axioms PlaneReadOne.threeEdgeException

#print axioms PlaneReadOne.threeEdgeCommonPath
