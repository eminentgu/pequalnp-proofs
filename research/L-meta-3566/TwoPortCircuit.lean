import PortTransversal
import TwoPort

namespace VertexPeel.NeighborPorts
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.Core
open VertexPeel.ZeroFold VertexPeel.RowGraph VertexPeel.RowCharge

variable {n : Nat} (C : Circuit)

def singletons (w : Nat) : Finset (Fin n) := Finset.univ.filter fun y => wval C (single y) w=true

/-- The two actual gates lit by x yield either a singleton port or a two-vertex
port whose other vertex is adjacent to every alternative of the other port. -/
theorem two_lit_ports (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ao : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅) (sq : NoFourCycle G)
    (x : Fin n) (p q : Nat) (different : p≠q) (only : lit C x={p,q}) (few : (lit C x).card<G.degree x) :
    let P := singletons (n:=n) C (port C x p)
    let Q := singletons (n:=n) C (port C x q)
    P={x} ∨ Q={x} ∨ (∃ y ≠ x, P={x,y} ∧ ∀ b ∈ Q.erase x, G.Adj y b) ∨
      ∃ y ≠ x, Q={x,y} ∧ ∀ a ∈ P.erase x, G.Adj y a := by
  classical
  let P := singletons (n:=n) C (port C x p)
  let Q := singletons (n:=n) C (port C x q)
  have inPort (j) (hj : j∈lit C x) : x ∈ singletons (n:=n) C (port C x j) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2.2⟩
  apply VertexPeel.TwoPort.two_ports G sq x P Q
    (inPort p (by simp [only])) (inPort q (by simp [only]))
  intro a ha b hb
  let Y (j : Nat) := if j=p then a else b
  have split (j) (hj : j ∈ lit C x) : j=p ∨ j=q := by simpa [only] using hj
  obtain ⟨i,hi,j,hj,edge⟩ := transversal_edge G C ao ok sq x few Y (by
    intro j hj
    rcases split j hj with rfl|rfl
    · simpa [Y] using (Finset.mem_erase.mp ha).1
    · simpa [Y,different.symm] using (Finset.mem_erase.mp hb).1) (by
    intro j hj
    rcases split j hj with rfl|rfl
    · simpa [Y] using (Finset.mem_filter.mp (Finset.mem_erase.mp ha).2).2
    · simpa [Y,different.symm] using (Finset.mem_filter.mp (Finset.mem_erase.mp hb).2).2)
  have alternatives (k) : Y k ∈ ({a,b} : Finset (Fin n)) := by by_cases e : k=p <;> simp [Y,e]
  exact ⟨Y i,alternatives i,Y j,alternatives j,edge⟩

/-- Every graph edge simultaneously lights one physical AND gate at both
endpoints, and the two canonical port wires at that gate are different. -/
theorem edge_opposite_ports (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ao : IsAO2 n C)
    (ok : circuitFun n C = graphFun G ∅) (x t : Fin n) (xt : G.Adj x t) :
    ∃ j ∈ lit C x, j ∈ lit C t ∧ port C x j≠port C t j := by
  classical
  have run (z : Fin n → Bool) : wval C z C.output=graphFun G ∅ z := congrFun ok z
  have off (v : Fin n) : wval C (single v) C.output=false := by rw [run]; simp [graphFun,single]
  have on : wval C (pairInput x t) C.output=true := by
    rw [run]
    simp [graphFun]
    exact ⟨x,t,xt,by simp [pairInput],by simp [pairInput]⟩
  obtain ⟨j,_,opp⟩ := VertexPeel.AndSeparation.opposing_ancestor C ao (single x) (single t)
    (pairInput x t) (by intro i hi; simpa [single,pairInput] using hi) _ (off x) (off t) on
  have rev : VertexPeel.AndSeparation.opposing C (single t) (single x) j :=
    ⟨opp.1,opp.2.1.symm,opp.2.2.2.symm,opp.2.2.1.symm⟩
  obtain ⟨xOn,tOff⟩ := orientation C x (single t) j opp
  obtain ⟨tOn,_⟩ := orientation C t (single x) j rev
  refine ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr opp.1.1,opp.1,xOn⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr opp.1.1,opp.1,tOn⟩,?_⟩
  intro eq
  rw [eq,tOn] at tOff
  contradiction

#print axioms edge_opposite_ports
#print axioms two_lit_ports
end VertexPeel.NeighborPorts
