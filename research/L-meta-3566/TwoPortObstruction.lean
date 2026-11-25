import TwoPort

namespace VertexPeel.TwoPort.Obstruction

open PEqualNP.EdgeOwnership PEqualNP.TopForm

/-- Points and lines of the Fano plane, indexed by translates of {0,1,3} in Z/7. -/
abbrev G := edgeGraph 14 [(0,7),(1,7),(3,7),(1,8),(2,8),(4,8),(2,9),(3,9),(5,9),
  (3,10),(4,10),(6,10),(0,11),(4,11),(5,11),(1,12),(5,12),(6,12),(0,13),(2,13),(6,13)]

def color (v : Fin 14) := decide (v.val<7)
def vertex : Fin 6 → Fin 14 := ![0,1,2,8,13,7]
def supports : Fin 5 → Finset (Fin 14) := ![{0,1,2},{8,13,7},{0,8},{1,13},{2,7}]
def side : Fin 6 → Fin 5 := ![0,0,0,1,1,1]
def pair : Fin 6 → Fin 5 := ![2,3,4,2,3,4]

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem cubic : NoFourCycle G ∧ (∀ v, G.degree v=3) ∧ ∀ u v, G.Adj u v → color u ≠ color v := by
  decide +kernel

theorem hyp : (∀ s t, vertex s=vertex t → s=t) ∧
    (∀ s, side s≠pair s ∧ vertex s ∈ supports (side s) ∧ vertex s ∈ supports (pair s)) ∧
    (∀ s, ∀ u ∈ supports (side s), u ≠ vertex s →
      ∀ v ∈ supports (pair s), v ≠ vertex s → G.Adj u v) ∧
    (∀ s, ∀ v ∈ supports (pair s), color v = color (vertex s) → v=vertex s) ∧
    (∀ s, (supports (side s)).card = 3 ∧ (supports (pair s)).card=2) := by
  decide +kernel

/-- Within the six deficient vertices even the pairwise requirement of a common
physical gate with opposite ports is feasible: place labels 0 and 1 at one gate. -/
theorem opposite_labels : ∀ s t, G.Adj (vertex s) (vertex t) →
    (side s=0 ∧ side t=1) ∨ (side s=1 ∧ side t=0) := by decide +kernel

/-- There are fewer port labels than the six selected vertices, before imposing
any constraint on which label could be assigned to which vertex. -/
theorem no_assignment : ¬∃ f : Fin 6 → Fin 5, Function.Injective f := by
  rintro ⟨f,h⟩
  have := Fintype.card_le_of_injective f h
  simp at this

#print axioms cubic
#print axioms hyp
#print axioms no_assignment
end VertexPeel.TwoPort.Obstruction
