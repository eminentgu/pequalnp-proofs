import AndSeparation

namespace VertexPeel.NeighborPorts
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.Core
open VertexPeel.ZeroFold VertexPeel.RowGraph VertexPeel.RowCharge VertexPeel.AndSeparation

variable {n : ℕ} (C : Circuit)
def single (x : Fin n) (i : Fin n) : Bool := decide (i=x)

/-- A canonical choice between the two ports, depending only on the gate and x. -/
def port (x : Fin n) (j : ℕ) : ℕ :=
  if wval C (single x) (in0 C j) = true then in0 C j else in1 C j

noncomputable def lit (x : Fin n) : Finset ℕ := by
  classical
  exact (Finset.range C.size).filter fun j =>
    isAnd C j ∧ wval C (single x) (port C x j)=true

def Private (color : Fin n → Bool) (x : Fin n) : Prop :=
  ∃ j ∈ lit C x, ∀ y, color y=color x → wval C (single y) (port C x j)=true → y=x

theorem orientation (x : Fin n) (y : Fin n → Bool) (j : ℕ)
    (opp : opposing C (single x) y j) :
    wval C (single x) (port C x j)=true ∧ wval C y (port C x j)=false := by
  obtain ⟨_,ne,sw,sw'⟩ := opp
  unfold port
  cases hx : wval C (single x) (in0 C j) <;> cases hy : wval C y (in0 C j) <;> simp_all

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (color : Fin n → Bool)
    (bip : ∀ u v, G.Adj u v → color u ≠ color v)

private def probe (x t i : Fin n) : Bool := decide (i=t ∨ (color i=color x ∧ ¬ G.Adj t i))

include bip in
/-- A real edge gets a port whose singleton activators on x's side all neighbor t. -/
theorem witness (ao : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅) {x t : Fin n}
    (edge : G.Adj x t) :
    ∃ j ∈ lit C x, ∀ y, color y=color x → wval C (single y) (port C x j)=true → G.Adj t y := by
  classical
  let I := probe G color x t
  have eval (z : Fin n → Bool) : wval C z C.output = graphFun G ∅ z := congrFun ok z
  have offX : wval C (single x) C.output=false := by
    rw [eval]
    simp [graphFun,single]
  have offI : wval C I C.output=false := by
    rw [eval]
    have no : ¬ ∃ a b, G.Adj a b ∧ I a=true ∧ I b=true := by
      rintro ⟨a,b,ab,va,vb⟩
      rcases (show a=t ∨ color a=color x ∧ ¬G.Adj t a by simpa [I,probe] using va) with rfl|ha
      · rcases (show b=a ∨ color b=color x ∧ ¬G.Adj a b by simpa [I,probe] using vb) with rfl|hb
        · exact ab.ne rfl
        · exact hb.2 ab
      · rcases (show b=t ∨ color b=color x ∧ ¬G.Adj t b by simpa [I,probe] using vb) with rfl|hb
        · exact ha.2 ab.symm
        · exact bip a b ab (ha.1.trans hb.1.symm)
    simp [graphFun,no]
  have on : wval C (pairInput x t) C.output=true := by
    rw [eval]
    simp [graphFun]
    exact ⟨x,t,edge,by simp [pairInput],by simp [pairInput]⟩
  obtain ⟨j,_,opp⟩ := opposing_ancestor C ao (single x) I (pairInput x t) (by
    intro i hi
    rcases (show i=x ∨ i=t by simpa [pairInput] using hi) with rfl|rfl
    · exact Or.inl (by simp [single])
    · exact Or.inr (by simp [I,probe])) _ offX offI on
  obtain ⟨yes,off⟩ := orientation C x I j opp
  refine ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr opp.1.1,opp.1,yes⟩,?_⟩
  intro y same hit
  by_contra missing
  have included : ∀ i, single y i=true → I i=true := by
    intro i hi
    have eq : i=y := by simpa [single] using hi
    simp [I,probe,eq,same,missing]
  exact Bool.noConfusion (off.symm.trans (wire_mono C ao included _ hit))

include bip in
/-- A vertex either has an AND port singling it out on its own side, or
its singleton input lights as many distinct physical AND gates as its degree. -/
theorem private_or_degree (ao : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅)
    (sq : NoFourCycle G) (x : Fin n) :
    Private C color x ∨ G.degree x ≤ (lit C x).card := by
  classical
  by_cases solo : Private C color x
  · exact Or.inl solo
  right
  have pick (t : Fin n) : ∃ j, G.Adj x t →
      j ∈ lit C x ∧ ∀ y, color y=color x → wval C (single y) (port C x j)=true → G.Adj t y := by
    by_cases e : G.Adj x t
    · obtain ⟨j,litJ,h⟩ := witness C G color bip ao ok e
      exact ⟨j,fun _ => ⟨litJ,h⟩⟩
    · exact ⟨0,fun h => (e h).elim⟩
  choose J good using pick
  have inject : Set.InjOn J (G.neighborFinset x : Set (Fin n)) := by
    intro t ht s hs eq
    have xt := (G.mem_neighborFinset x t).mp ht
    have xs := (G.mem_neighborFinset x s).mp hs
    obtain ⟨litJ,rightT⟩ := good t xt
    obtain ⟨_,rightS⟩ := good s xs
    have no : ¬ ∀ y, color y=color x → wval C (single y) (port C x (J t))=true → y=x :=
      fun h => solo ⟨_,litJ,h⟩
    push Not at no
    obtain ⟨y,same,hit,ne⟩ := no
    have ty := rightT y same hit
    have sy := rightS y same (eq ▸ hit)
    apply Finset.card_le_one.mp (sq x y ne.symm)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,xt,ty.symm⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,xs,sy.symm⟩
  have size := Finset.card_le_card_of_injOn (s:=G.neighborFinset x) J
    (fun t ht => (good t ((G.mem_neighborFinset x t).mp ht)).1) inject
  simpa using size
#print axioms witness
#print axioms private_or_degree
end VertexPeel.NeighborPorts
