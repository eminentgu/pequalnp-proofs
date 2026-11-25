import PortHall
import TwoPortObstruction

namespace VertexPeel.TwoPort.Obstruction

open VertexPeel.PortHall

def selected : Finset (Fin 14) := Finset.univ.image vertex

def labels (x : Fin 14) : Finset (Fin 5) := Finset.univ.filter fun p => x ∈ supports p

/-- The Heawood example satisfies exactly the replacement premise of the Hall
theorem, with a deficit of one. The six-cycle hypothesis has combinatorial force. -/
theorem sharp : (∀ x ∈ selected, (labels x).card=2) ∧ Blocked G selected labels ∧
    (selected.biUnion labels).card+1=selected.card := by
  refine ⟨by decide +kernel,?_,by decide +kernel⟩
  intro x hx Y hy
  obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨_,a,b⟩ := hyp.2.1 s
  have sa : side s ∈ labels (vertex s) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,a⟩
  have sb : pair s ∈ labels (vertex s) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,b⟩
  obtain ⟨_,ya,pa⟩ := hy (side s) sa
  obtain ⟨_,yb,pb⟩ := hy (pair s) sb
  exact ⟨side s,sa,pair s,sb,hyp.2.2.1 s _ (Finset.mem_filter.mp pa).2 ya _ (Finset.mem_filter.mp pb).2 yb⟩

#print axioms sharp
end VertexPeel.TwoPort.Obstruction
