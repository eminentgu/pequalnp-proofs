import OrderedMatching

namespace VertexPeel.PivotAND
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.Core PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_1774 PEqualNP.MetaComplexity.CoverPromise
open VertexPeel.AndSeparation VertexPeel.RowGraph VertexPeel.RowCharge VertexPeel.CoverCircuit

variable {n : ℕ}

/-- All physical AND indices, including gates outside the output cone. -/
noncomputable def physical (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.size).filter (isAnd C)

def unit (x u : Fin n) : Bool := decide (u=x)

def lit (C : Circuit) (x : Fin n) (j : ℕ) : Prop := isAnd C j ∧
  (wval C (unit x) (in0 C j)=true ∨ wval C (unit x) (in1 C j)=true)

end VertexPeel.PivotAND
