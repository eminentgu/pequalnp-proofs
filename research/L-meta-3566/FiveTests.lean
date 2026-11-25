import CoverPatterns
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Hasse

namespace VertexPeel.FiveTests

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadTwo VertexPeel.AndSeparation

private def liftInput {m n : ℕ} (f : Fin m → Fin n) (x : Fin m → Bool) (i : Fin n) :=
  decide (∃ a, f a = i ∧ x a = true)

def NegativeFamily {n : ℕ} (F : (Fin n → Bool) → Bool) (k : ℕ) :=
  ∃ test : Fin k → Fin n → Bool, (∀ i, F (test i) = false) ∧
    ∀ i j, i ≠ j → ∃ z, F z = true ∧ ∀ t, z t = true → test i t = true ∨ test j t = true

/-- A family of independent supports in an induced subgraph can be tested in the whole
circuit. Each pair must contain the two endpoints of an edge in its union. -/
theorem induced_family {n m k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : SimpleGraph (Fin m)) (f : H ↪g G) (test : Fin k → Fin m → Bool)
    (off : ∀ i a b, H.Adj a b → test i a = true → test i b = true → False)
    (sep : ∀ i j, i ≠ j → ∃ a b, H.Adj a b ∧ (test i a = true ∨ test j a = true) ∧
      (test i b = true ∨ test j b = true))
    : NegativeFamily (graphFun G ∅) k := by
  classical
  refine ⟨fun i => liftInput f (test i),?_,?_⟩
  · intro i
    have none : ¬ ∃ a b, G.Adj a b ∧ liftInput f (test i) a = true ∧ liftInput f (test i) b = true := by
      rintro ⟨a,b,edge,ha,hb⟩
      obtain ⟨s,rfl,hs⟩ := of_decide_eq_true ha
      obtain ⟨t,rfl,ht⟩ := of_decide_eq_true hb
      exact off i s t (f.map_rel_iff.mp edge) hs ht
    simp [graphFun,none]
  · intro i j ne
    obtain ⟨a,b,edge,ha,hb⟩ := sep i j ne
    have pos : ∃ s t, G.Adj s t ∧ pairInput (f a) (f b) s = true ∧ pairInput (f a) (f b) t = true :=
      ⟨f a,f b,f.map_rel_iff.mpr edge,by simp [pairInput],by simp [pairInput]⟩
    refine ⟨pairInput (f a) (f b),by simp [graphFun,pos],?_⟩
    have yes (u : Fin m) (on : test i u = true ∨ test j u = true) :
        liftInput f (test i) (f u) = true ∨ liftInput f (test j) (f u) = true :=
      on.imp (fun h => decide_eq_true ⟨u,rfl,h⟩) (fun h => decide_eq_true ⟨u,rfl,h⟩)
    intro v hv
    rcases (show v = f a ∨ v = f b by simpa [pairInput] using hv) with rfl|rfl
    · exact yes a ha
    · exact yes b hb

private def tests (m : ℕ) (s : Fin 5 → ℕ) (i : Fin 5) (v : Fin m) := (s i).testBit v.val

private def cycleFive := tests 5 ![5,9,10,18,20]
private def cycleSix := tests 6 ![9,18,21,36,42]
private def pathSix := tests 6 ![18,21,37,41,42]

abbrev HasObstruction {n : ℕ} (G : SimpleGraph (Fin n)) :=
  Nonempty (SimpleGraph.cycleGraph 5 ↪g G) ∨ Nonempty (SimpleGraph.cycleGraph 6 ↪g G) ∨
    Nonempty (SimpleGraph.pathGraph 6 ↪g G)

theorem family_of_obstruction {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (obs : HasObstruction G) : NegativeFamily (graphFun G ∅) 5 := by
  rcases obs with h|h|h <;> obtain ⟨f⟩ := h
  · exact induced_family G _ f cycleFive (by decide +kernel) (by decide +kernel)
  · exact induced_family G _ f cycleSix (by decide +kernel) (by decide +kernel)
  · exact induced_family G _ f pathSix (by decide +kernel) (by decide +kernel)

theorem three_ands_of_obstruction {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (obs : HasObstruction G) (C : Circuit) (hc : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅) :
    3 ≤ (andCone (n := n) C C.output).card := by
  classical
  obtain ⟨test,off,sep⟩ := family_of_obstruction G obs
  have ev (x : Fin n → Bool) : wval C x C.output = graphFun G ∅ x := congrFun ok x
  have bound := pattern_bound C hc C.output Finset.univ test (fun i _ => (ev _).trans (off i)) (by
    intro i _ j _ ne
    obtain ⟨z,on,h⟩ := sep i j ne
    exact ⟨z,(ev _).trans on,h⟩)
  have lower : 5 ≤ 2 ^ (andCone (n := n) C C.output).card := by simpa using bound
  by_contra! small
  have h := Nat.pow_le_pow_right (by decide : 0 < 2) (show (andCone (n := n) C C.output).card ≤ 2 by omega)
  omega

end VertexPeel.FiveTests
