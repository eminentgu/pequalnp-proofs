import PivotAND

namespace VertexPeel.PivotAND
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.Core PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_1774 PEqualNP.MetaComplexity.CoverPromise
open VertexPeel.AndSeparation VertexPeel.RowGraph VertexPeel.RowCharge VertexPeel.CoverCircuit
variable {n : ℕ}

private def pair (u v t : Fin n) : Bool := decide (t=u ∨ t=v)

/-- A private neighbor forces a gate port lit by the first singleton and
unlit by the second. The gate's other port is unlit by the first singleton. -/
theorem private_port (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (ao : IsAO2 n C)
    (correct : circuitFun n C = graphFun G ∅) {x y t : Fin n} (edge : G.Adj x t) (noEdge : ¬G.Adj y t) :
    ∃ j, lit C x j ∧ wval C (unit x) (in0 C j) ≠ wval C (unit x) (in1 C j) ∧
      (wval C (unit x) (in0 C j) = true → wval C (unit y) (in0 C j) = false) ∧
      (wval C (unit x) (in1 C j) = true → wval C (unit y) (in1 C j) = false) := by
  classical
  have ev (a : Fin n → Bool) : wval C a C.output = graphFun G ∅ a := congrFun correct a
  have off : ¬ ∃ a b, G.Adj a b ∧ pair y t a=true ∧ pair y t b=true := by
    rintro ⟨a,b,ab,ha,hb⟩
    rcases of_decide_eq_true ha with rfl|rfl <;> rcases of_decide_eq_true hb with rfl|rfl
    · exact ab.ne rfl
    · exact noEdge ab
    · exact noEdge ab.symm
    · exact ab.ne rfl
  have on : ∃ a b, G.Adj a b ∧ pair x t a=true ∧ pair x t b=true := ⟨x,t,edge,by simp [pair],by simp [pair]⟩
  obtain ⟨j,_,hand,hne,swap,other⟩ := opposing_ancestor C ao (unit x) (pair y t) (pair x t)
    (fun v hv => by rcases of_decide_eq_true hv with rfl|rfl; exact Or.inl (by simp [unit]); exact Or.inr (by simp [pair]))
    C.output (by rw [ev]; simp [graphFun,unit]) (by rw [ev]; simp [graphFun,off]) (by rw [ev]; simp [graphFun,on])
  have mono (u : ℕ) (h : wval C (unit y) u = true) : wval C (pair y t) u = true :=
    wire_mono C ao (fun v hv => decide_eq_true (Or.inl (of_decide_eq_true hv))) _ h
  have opp : wval C (unit x) (in0 C j) ≠ wval C (unit x) (in1 C j) := by rwa [other]
  have litAt : lit C x j := ⟨hand,by cases a : wval C (unit x) (in0 C j) <;> cases b : wval C (unit x) (in1 C j) <;> simp_all⟩
  refine ⟨j,litAt,opp,?_,?_⟩
  · intro h
    apply Bool.eq_false_iff.mpr
    intro hit
    exact hne (h.trans (mono _ hit).symm)
  · intro h
    apply Bool.eq_false_iff.mpr
    intro hit
    exact opp ((swap.trans (mono _ hit)).trans h.symm)

/-- If too few physical AND gates represent a graph, one vertex of every
sufficiently large set with pairwise distinct neighborhoods lights at least two gates. -/
theorem two_lit (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (ao : IsAO2 n C)
    (correct : circuitFun n C = graphFun G ∅) (A : Finset (Fin n))
    (active : ∀ x∈A, ∃ t, G.Adj x t)
    (privateN : ∀ x∈A, ∀ y∈A, x ≠ y → ∃ t, G.Adj x t ∧ ¬G.Adj y t)
    (few : 2*(physical C).card < A.card) : ∃ x∈A, ∃ i j, i ≠ j ∧ lit C x i ∧ lit C x j := by
  classical
  by_contra! unique
  have one (x : ↥A) : ∃ j, lit C x.val j ∧ wval C (unit x.val) (in0 C j) ≠ wval C (unit x.val) (in1 C j) := by
    obtain ⟨t,e⟩ := active x.val x.property
    obtain ⟨j,a,b,_⟩ := private_port G C ao correct e (G.loopless.irrefl t)
    exact ⟨j,a,b⟩
  choose J hj using one
  let tag (x : A) := wval C (unit x.val) (in0 C (J x))
  have incl (x : A) : J x ∈ physical C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hj x).1.1.1,(hj x).1.1⟩
  let addr (x : A) : ↥(physical C) × Bool := (⟨J x,incl x⟩,tag x)
  have inj : Function.Injective addr := by
    intro x y same
    by_contra ne
    have diff : x.val ≠ y.val := fun h => ne (Subtype.ext h)
    obtain ⟨t,xt,yt⟩ := privateN x.val x.property y.val y.property diff
    obtain ⟨j,jx,_,off0,off1⟩ := private_port G C ao correct xt yt
    have je : J x=j := by by_contra bad; exact unique x.val x.property (J x) j bad (hj x).1 jx
    have jj : J x=J y := congrArg (fun a : ↥(physical C) × Bool => a.1.val) same
    have eq0 : wval C (unit x.val) (in0 C (J x)) = wval C (unit y.val) (in0 C (J y)) := congrArg Prod.snd same
    have dy := (hj y).2
    have dx := (hj x).2
    rw [← jj] at eq0 dy
    rw [← je] at off0 off1
    cases a : wval C (unit x.val) (in0 C (J x)) <;> cases b : wval C (unit x.val) (in1 C (J x)) <;>
      cases c : wval C (unit y.val) (in0 C (J x)) <;> cases d : wval C (unit y.val) (in1 C (J x)) <;> simp_all
  have bound := Fintype.card_le_of_injective addr inj
  simp [Fintype.card_prod] at bound
  omega

#print axioms private_port
#print axioms two_lit
end VertexPeel.PivotAND
