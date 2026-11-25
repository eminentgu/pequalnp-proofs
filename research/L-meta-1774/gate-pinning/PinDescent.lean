import StarPin

namespace PEqualNP.Research.GatePinning

open CircuitLowerBounds EdgeOwnership MetaComplexity MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_5465 (val)

def BadAt {n} (G : SimpleGraph (Fin n)) (D : Circuit) (j : Nat) :=
  ∃ a b c d : Fin n, G.Adj a b ∧ G.Adj c d ∧ Owns n D j a b ∧ Owns n D j c d ∧
    a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d

def Productive {n} (G : SimpleGraph (Fin n)) (D : Circuit) :=
  ∀ j < D.size, (gateAt D j).op = .and → ∃ a b : Fin n, G.Adj a b ∧ Owns n D j a b

def Eligible {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit) :=
  IsMinimalMonoCircuit n D ∧ circuitFun n D = graphFun G ∅ ∧ Productive G D

/-- Repairing the earliest defect suffices, even if a single repair introduces more
defects later. The finite prefix of defect-free gates grows by at least one each time. -/
theorem normal_of_first_repairs {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (repair : ∀ D : Circuit, Eligible G D → ∀ k < D.size, (∀ j < k, ¬BadAt G D j) → BadAt G D k →
      ∃ E : Circuit, Eligible G E ∧ E.size = D.size ∧ (∀ j < k, BadAt G E j → BadAt G D j) ∧ ¬BadAt G E k)
    (C : Circuit) (initial : Eligible G C) :
    ∃ D : Circuit, Eligible G D ∧ D.size = C.size ∧ ∀ j, ¬BadAt G D j := by
  classical
  have prefixGood (a : Nat) (bounded : a ≤ C.size) :
      ∃ D : Circuit, Eligible G D ∧ D.size=C.size ∧ ∀ j<a, ¬BadAt G D j := by
    induction a with
    | zero => exact ⟨C,initial,rfl,by simp⟩
    | succ k ih =>
      obtain ⟨D,hd,size,earlier⟩ := ih (by omega)
      by_cases bad : BadAt G D k
      · obtain ⟨E,he,esize,old,ok⟩ := repair D hd k (by omega) earlier bad
        refine ⟨E,he,esize.trans size,?_⟩
        intro j hj
        rcases Nat.lt_or_eq_of_le (by omega : j≤k) with less | rfl
        · exact fun new => earlier _ less (old _ less new)
        · exact ok
      · refine ⟨D,hd,size,?_⟩
        intro j hj
        rcases Nat.lt_or_eq_of_le (by omega : j≤k) with less | rfl
        · exact earlier _ less
        · exact bad
  obtain ⟨D,hd,sz,all⟩ := prefixGood C.size le_rfl
  refine ⟨D,hd,sz,?_⟩
  intro j bad
  obtain ⟨a,b,c,d,e,f,p,q,h⟩ := bad
  exact all j (sz ▸ p.1) ⟨a,b,c,d,e,f,p,q,h⟩

/-- Input data for the explicit gate exchange. At least one edge already owned by this
AND meets the proposed centre, so productivity survives this edit. -/
def AdmitsStarPin {n} (G : SimpleGraph (Fin n)) (C : Circuit) (k : Nat) :=
  ∃ (s t : Nat) (v : Fin n), (gateAt C k = ⟨.and,[s,t]⟩ ∨ gateAt C k = ⟨.and,[t,s]⟩) ∧ s<n+k ∧ t<n+k ∧
    (∀ x : Fin n → Bool, x v = true → val C (List.ofFn x) s = true) ∧
    (∀ a b, needed G C k a b → a=v ∨ b=v) ∧
    ∃ a b, G.Adj a b ∧ Owns n C k a b ∧ (a=v ∨ b=v)

theorem repair_of_star_pin {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (eligible : Eligible G C) {k : Nat} (inside : k < C.size) (admits : AdmitsStarPin G C k) :
    ∃ D : Circuit, Eligible G D ∧ D.size = C.size ∧ (∀ j < k, BadAt G D j → BadAt G C j) ∧ ¬ BadAt G D k := by
  obtain ⟨s,t,v,site,hs,ht,forces,star,a,b,edge,owned,hit⟩ := admits
  let D := pinSide C k v t
  obtain ⟨dm,df,size,others,center,atK⟩ := pin_critical_star G eligible.1.1 eligible.2.1 inside site hs ht v forces star
  have minimal : IsMinimalMonoCircuit n D := by
    refine ⟨dm,?_⟩
    intro E em ef
    exact size ▸ eligible.1.2 E em (ef.trans (df.trans eligible.2.1.symm))
  have useful : Productive G D := by
    intro j jbound hand
    by_cases eq : j=k
    · subst j
      exact ⟨a,b,edge,atK a b owned hit⟩
    · have op : (gateAt C j).op = .and := (congrArg Gate.op
          (show gateAt D j = gateAt C j from replace_elsewhere eq)).symm.trans hand
      obtain ⟨u,w,ed,own⟩ := eligible.2.2 j (size ▸ jbound) op
      exact ⟨u,w,ed,others j eq u w own⟩
  refine ⟨D,⟨minimal,df,useful⟩,size,?_,?_⟩
  · rintro j hj ⟨u,w,p,q,e,f,x,y,dis⟩
    exact ⟨u,w,p,q,e,f,before_new_to_old eligible.1.1 hj x,before_new_to_old eligible.1.1 hj y,dis⟩
  · rintro ⟨u,w,p,q,e,f,x,y,ne1,ne2,ne3,ne4⟩
    rcases center u w x with h | h <;> rcases center p q y with z | z <;> grind

/-- The remaining combinatorial premise is restricted to the earliest disjoint owner. -/
theorem normal_of_critical_stars {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (premise : ∀ C : Circuit, Eligible G C → ∀ k < C.size,
      (∀ j < k, ¬BadAt G C j) → BadAt G C k → AdmitsStarPin G C k) :
    ∀ C : Circuit, Eligible G C → ∃ D : Circuit, Eligible G D ∧ D.size = C.size ∧ ∀ j, ¬BadAt G D j :=
  normal_of_first_repairs G (fun C eligible k bound earlier bad =>
    repair_of_star_pin G eligible bound (premise C eligible k bound earlier bad))

end PEqualNP.Research.GatePinning
