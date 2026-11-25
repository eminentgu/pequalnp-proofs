import AndSeparation

namespace VertexPeel.CoverPatterns

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.Core
open VertexPeel.AndSeparation

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

/-- A support with no edge. -/
def independent (S : Finset (Fin n)) : Prop := ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b

def maximal (S : Finset (Fin n)) : Prop := independent G S ∧
  ∀ T, S ⊆ T → independent G T → T = S

noncomputable def maxSets : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter (maximal G)

private def characteristic (S : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ S)

private theorem off (S : Finset (Fin n)) (hs : independent G S) : graphFun G ∅ (characteristic S) = false := by
  have ha : ¬ ∃ a b, G.Adj a b ∧ characteristic S a = true ∧ characteristic S b = true := by
    rintro ⟨a,b,edge,h1,h2⟩
    exact hs a (by simpa [characteristic] using h1) b (by simpa [characteristic] using h2) edge
  simp [graphFun,ha]

private theorem pair_on {a b : Fin n} (edge : G.Adj a b) : graphFun G ∅ (pairInput a b) = true := by
  have : ∃ i j, G.Adj i j ∧ pairInput a b i = true ∧ pairInput a b j = true :=
    ⟨a,b,edge,by simp [pairInput],by simp [pairInput]⟩
  simp [graphFun,this]

/-- The characteristic patterns of maximal independent sets must be distinct already on
one input of each physical AND in the output cone. -/
theorem maximal_sets_bound (hc : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅) :
    (maxSets G).card ≤ 2 ^ (andCone (n := n) C C.output).card := by
  classical
  have ev (x : Fin n → Bool) : wval C x C.output = graphFun G ∅ x := congrFun ok x
  apply pattern_bound C hc C.output (maxSets G) characteristic
  · intro s hs
    exact (ev _).trans (off G s (Finset.mem_filter.mp hs).2.1)
  · intro s hs t ht ne
    have falseUnion : ¬ independent G (s ∪ t) := by
      intro ind
      have e1 := (Finset.mem_filter.mp hs).2.2 _ Finset.subset_union_left ind
      have e2 := (Finset.mem_filter.mp ht).2.2 _ Finset.subset_union_right ind
      exact ne (e1.symm.trans e2)
    unfold independent at falseUnion
    push Not at falseUnion
    obtain ⟨a,ha,b,hb,edge⟩ := falseUnion
    refine ⟨pairInput a b,(ev _).trans (pair_on G edge),?_⟩
    intro i hon
    have hin : i ∈ s ∪ t := (show i = a ∨ i = b by simpa [pairInput] using hon).elim
      (fun e => e ▸ ha) (fun e => e ▸ hb)
    simpa [characteristic] using (Finset.mem_union.mp hin)

/-- Each member of an induced matching costs one physical AND in the output cone,
regardless of other graph vertices and arbitrary reuse of existing gates. -/
theorem induced_matching_bound (hc : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅)
    {k : ℕ} (v : Fin k → Bool → Fin n) (edge : ∀ i, G.Adj (v i false) (v i true))
    (cross : ∀ i j, i ≠ j → ∀ a b, ¬ G.Adj (v i a) (v j b)) :
    k ≤ (andCone (n := n) C C.output).card := by
  classical
  let S (s : Fin k → Bool) := Finset.univ.image fun i => v i (s i)
  have ev (x : Fin n → Bool) : wval C x C.output = graphFun G ∅ x := congrFun ok x
  have neg (s : Fin k → Bool) : independent G (S s) := by
    intro a ha b hb
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
    by_cases h : i = j
    · subst j; exact fun e => e.ne rfl
    · exact cross i j h _ _
  have h := pattern_bound C hc C.output (Finset.univ : Finset (Fin k → Bool)) (fun s => characteristic (S s))
      (fun s _ => (ev _).trans (off G _ (neg s))) (by
        intro s _ t _ ne
        obtain ⟨i,hi⟩ : ∃ i, s i ≠ t i := Function.ne_iff.mp ne
        have hpair : G.Adj (v i (s i)) (v i (t i)) := by
          cases hs : s i <;> cases ht : t i <;> simp_all [SimpleGraph.adj_comm]
        refine ⟨pairInput (v i (s i)) (v i (t i)),(ev _).trans (pair_on G hpair),?_⟩
        intro a yes
        rcases (show a = v i (s i) ∨ a = v i (t i) by simpa [pairInput] using yes) with rfl|rfl
        · exact Or.inl (by simp [characteristic,S])
        · exact Or.inr (by simp [characteristic,S]))
  have pow : 2 ^ k ≤ 2 ^ (andCone (n := n) C C.output).card := by simpa [Fintype.card_fun] using h
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp pow

end VertexPeel.CoverPatterns
