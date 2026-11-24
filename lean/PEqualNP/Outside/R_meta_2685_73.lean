import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- Remove a single nonempty star and pay for its leaves and its join to the remainder.
-- The two construction hypotheses are the checked steps L-meta-3243 and L-meta-3245.
theorem PEqualNP.Outside.R_meta_2685_73
    (terminal : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit), E.Nonempty →
      ((∃ p : Fin n, ∀ e ∈ E, e.1 = p) ∨ (∃ l : Fin m, ∀ e ∈ E, e.2 = l)) →
      IsAO2 (n+m) C → circuitFun (n+m) C = PEqualNP.ReadTwo.fpl n (fun p l => (p,l) ∈ E) →
      E.card ≤ C.size)
    (peel : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit), E.Nonempty →
      ¬ ((∃ p : Fin n, ∀ e ∈ E, e.1 = p) ∨ (∃ l : Fin m, ∀ e ∈ E, e.2 = l)) →
      (∀ p q l s, p ≠ q → l ≠ s → ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)) →
      IsAO2 (n+m) C → circuitFun (n+m) C = PEqualNP.ReadTwo.fpl n (fun p l => (p,l) ∈ E) →
      ∃ F ⊂ E, ((∃ p : Fin n, ∀ e ∈ E \ F, e.1 = p) ∨ (∃ l : Fin m, ∀ e ∈ E \ F, e.2 = l)) ∧
        F.Nonempty ∧ ∃ D : Circuit, IsAO2 (n+m) D ∧
          circuitFun (n+m) D = PEqualNP.ReadTwo.fpl n (fun p l => (p,l) ∈ F) ∧
          D.size + (E \ F).card + 1 ≤ C.size)
    (realize : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (own : List (ℕ × List ℕ)),
  let n := Np + Nl
  (∀ tx ∈ own, tx.2 ≠ [] ∧
  ((tx.1 < Np ∧ ∀ u ∈ tx.2, Np ≤ u ∧ u < n) ∨
   (Np ≤ tx.1 ∧ tx.1 < n ∧ ∀ u ∈ tx.2, u < Np))) → (∀ (p : Fin Np) (l : Fin Nl), I p l ↔
  ∃ tx ∈ own, (tx.1 = p.val ∧ Np + l.val ∈ tx.2) ∨
    (tx.1 = Np + l.val ∧ p.val ∈ tx.2)) →
  let D := PEqualNP.MetaComplexity.coverCircuitB n own
  D.size = (own.map (fun tx => tx.2.length)).sum + own.length - 1 ∧ ∀ z : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n D z = decide (∃ (p : Fin Np) (l : Fin Nl), I p l ∧
  z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true))
    (shaped : ∀ (Np Nl : ℕ) (own : List (ℕ × List ℕ)),
  let n := Np + Nl
  (∀ tx ∈ own, tx.2 ≠ [] ∧
  ((tx.1 < Np ∧ ∀ u ∈ tx.2, Np ≤ u ∧ u < n) ∨
   (Np ≤ tx.1 ∧ tx.1 < n ∧ ∀ u ∈ tx.2, u < Np))) → let D := PEqualNP.MetaComplexity.coverCircuitB n own
  let g := PEqualNP.MetaComplexity.NestedCover.gateAt D
  ∃ P L : Finset ℕ, PEqualNP.TopForm.IsAO2 n D ∧
    (∀ w ∈ P, w < Np ∨ ∃ i < D.gates.length,
      w = n + i ∧ (g i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (g i).inputs, u ∈ P) ∧
    (∀ w ∈ L, (Np ≤ w ∧ w < n) ∨ ∃ i < D.gates.length,
      w = n + i ∧ (g i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (g i).inputs, u ∈ L) ∧
    ∀ i < D.gates.length, (g i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ∃ a b : ℕ, (g i).inputs = [a,b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (P L : Finset ℕ), PEqualNP.TopForm.IsAO2 (Np + Nl) D ∧ (∀ y : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D y = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ y (Fin.castAdd Nl p) = true ∧ y (Fin.natAdd Np l) = true)) ∧ D.size ≤ C.size ∧ (∀ w ∈ P, w < Np ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ P) ∧ (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ L) ∧ ∀ i < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)) := by
  classical
  intro n m I inst C hs hao hc
  let Tagged := fun (s : ℕ × List ℕ) => s.2 ≠ [] ∧
    ((s.1 < n ∧ ∀ u ∈ s.2, n ≤ u ∧ u < n+m) ∨
     (n ≤ s.1 ∧ s.1 < n+m ∧ ∀ u ∈ s.2, u < n))
  let Hits := fun (s : ℕ × List ℕ) (p : Fin n) (l : Fin m) =>
    (s.1 = p.val ∧ n+l.val ∈ s.2) ∨ (s.1 = n+l.val ∧ p.val ∈ s.2)
  have encode (T : Finset (Fin n × Fin m)) (hne : T.Nonempty)
      (star : (∃ p : Fin n, ∀ e ∈ T, e.1 = p) ∨ (∃ l : Fin m, ∀ e ∈ T, e.2 = l)) :
      ∃ s, Tagged s ∧ s.2.length = T.card ∧ ∀ p l, Hits s p l ↔ (p,l) ∈ T := by
    obtain ⟨e, he⟩ := hne
    rcases star with ⟨p,hp⟩ | ⟨l,hl⟩
    · let vals := T.toList.map (fun x => n+x.2.val)
      refine ⟨(p.val,vals),⟨?_,Or.inl ⟨p.isLt,?_⟩⟩,?_,?_⟩
      · have h : n+e.2.val ∈ vals := List.mem_map.mpr ⟨e,Finset.mem_toList.mpr he,rfl⟩
        exact List.ne_nil_of_mem h
      · intro u hu
        rcases List.mem_map.mp hu with ⟨v,_,rfl⟩
        have := v.2.isLt
        omega
      · simp [vals]
      · intro q l
        change (p.val = q.val ∧ n+l.val ∈ vals ∨ p.val = n+l.val ∧ q.val ∈ vals) ↔ _
        constructor
        · rintro (⟨eq,h⟩|⟨eq,_⟩)
          · obtain ⟨v,hv,ev⟩ := List.mem_map.mp h
            have mem := Finset.mem_toList.mp hv
            have left : v.1 = q := (hp v mem).trans (Fin.ext eq)
            have right : v.2 = l := Fin.ext (Nat.add_left_cancel ev)
            have pair : v = (q,l) := Prod.ext left right
            exact pair ▸ mem
          · have := p.isLt
            omega
        · intro h
          exact Or.inl ⟨congrArg Fin.val (hp _ h).symm,List.mem_map.mpr ⟨(q,l),Finset.mem_toList.mpr h,rfl⟩⟩
    · let vals := T.toList.map (fun x => x.1.val)
      refine ⟨(n+l.val,vals),⟨?_,Or.inr ⟨Nat.le_add_right _ _,by have := l.isLt; omega,?_⟩⟩,?_,?_⟩
      · have h : e.1.val ∈ vals := List.mem_map.mpr ⟨e,Finset.mem_toList.mpr he,rfl⟩
        exact List.ne_nil_of_mem h
      · intro u hu
        rcases List.mem_map.mp hu with ⟨v,_,rfl⟩
        exact v.1.isLt
      · simp [vals]
      · intro p r
        change (n+l.val = p.val ∧ n+r.val ∈ vals ∨ n+l.val = n+r.val ∧ p.val ∈ vals) ↔ _
        constructor
        · rintro (⟨eq,_⟩|⟨eq,h⟩)
          · have := p.isLt
            omega
          · obtain ⟨v,hv,ev⟩ := List.mem_map.mp h
            have mem := Finset.mem_toList.mp hv
            have left : v.1 = p := Fin.ext ev
            have right : v.2 = r := (hl v mem).trans (Fin.ext (Nat.add_left_cancel eq))
            have pair : v = (p,r) := Prod.ext left right
            exact pair ▸ mem
        · intro h
          exact Or.inr ⟨congrArg (fun j : Fin m => n+j.val) (hl _ h).symm,
            List.mem_map.mpr ⟨(p,r),Finset.mem_toList.mpr h,rfl⟩⟩
  have build (E : Finset (Fin n × Fin m)) : ∀ (A : Circuit),
      (∀ p q l s, p ≠ q → l ≠ s → ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)) →
      IsAO2 (n+m) A → circuitFun (n+m) A = PEqualNP.ReadTwo.fpl n (fun p l => (p,l) ∈ E) →
      ∃ own : List (ℕ × List ℕ), (∀ x ∈ own, Tagged x) ∧
        (∀ p l, (p,l) ∈ E ↔ ∃ x ∈ own, Hits x p l) ∧
        (own.map (fun s => s.2.length)).sum + own.length - 1 ≤ A.size := by
    induction E using Finset.strongInductionOn with
    | _ E ih =>
      intro A square model correct
      by_cases hE : E.Nonempty
      · by_cases whole : (∃ p : Fin n, ∀ e ∈ E, e.1 = p) ∨ (∃ l : Fin m, ∀ e ∈ E, e.2 = l)
        · obtain ⟨s,tag,len,inc⟩ := encode E hE whole
          have cost := terminal n m E A hE whole model correct
          exact ⟨[s],by simpa using tag,by simpa using fun p l => (inc p l).symm,
            by simpa [len] using cost⟩
        · obtain ⟨F,sub,star,live,D,dm,de,db⟩ := peel n m E A hE whole square model correct
          obtain ⟨s,tag,len,inc⟩ := encode (E \ F)
            (Finset.sdiff_nonempty_of_card_lt_card (Finset.card_lt_card sub)) star
          have subset : F ⊆ E := (Finset.ssubset_iff_subset_ne.mp sub).1
          have squareF : ∀ p q l t, p ≠ q → l ≠ t → ¬ ((p,l) ∈ F ∧ (p,t) ∈ F ∧ (q,l) ∈ F ∧ (q,t) ∈ F) := by
            intro p q l t pq lt h
            exact square p q l t pq lt ⟨subset h.1,subset h.2.1,subset h.2.2.1,subset h.2.2.2⟩
          obtain ⟨own,tags,edges,cost⟩ := ih F sub D squareF dm de
          refine ⟨s::own,?_,?_,?_⟩
          · intro x hx
            exact (List.mem_cons.mp hx).elim (fun h => h ▸ tag) (tags x)
          · intro p l
            rw [List.exists_mem_cons_iff,inc,← edges]
            simp only [Finset.mem_sdiff]
            exact ⟨fun h => by by_cases hf : (p,l) ∈ F; exact Or.inr hf; exact Or.inl ⟨h,hf⟩,
              fun h => h.elim And.left (fun hf => subset hf)⟩
          · obtain ⟨a,ha⟩ := live
            have used := (edges a.1 a.2).mp ha
            have pos : 0 < own.length := List.length_pos_iff.mpr (by rintro rfl; simp at used)
            simp only [List.map_cons,List.sum_cons,List.length_cons]
            rw [len]
            omega
      · have emp : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
        exact ⟨[],by simp,by simp [emp],by simp⟩
  let E := Finset.univ.filter (fun a : Fin n × Fin m => I a.1 a.2)
  have ep (p : Fin n) (l : Fin m) : (p,l) ∈ E ↔ I p l := by simp [E]
  have sq : ∀ p q l s, p ≠ q → l ≠ s → ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E) := by
    simpa only [ep] using hs
  have fn : circuitFun (n+m) C = PEqualNP.ReadTwo.fpl n (fun p l => (p,l) ∈ E) := by
    funext z
    change circuitFun (n+m) C z = decide (∃ (p : Fin n) (l : Fin m), (p,l) ∈ E ∧
      z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)
    simpa only [ep] using hc z
  obtain ⟨own,tags,covered,budget⟩ := build E C sq hao fn
  have allEdges : ∀ p l, I p l ↔ ∃ s ∈ own, Hits s p l := fun p l => (ep p l).symm.trans (covered p l)
  obtain ⟨size,computes⟩ := realize n m I own tags allEdges
  obtain ⟨P,L,ok,pts,lns,ands⟩ := shaped n m own tags
  exact ⟨_,P,L,ok,computes,by rw [size]; exact budget,pts,lns,ands⟩
