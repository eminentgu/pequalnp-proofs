import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import PEqualNP.Defs

namespace PEqualNP.Research.SharedMask

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

local instance : DecidableEq GateOp := gateOpDecEq

abbrev V := Fin 6

def G := edgeGraph 6 [(0,1),(0,3),(2,3),(0,4),(3,5)]

def C : Circuit :=
  ⟨[⟨.or,[0,2]⟩,⟨.or,[1,3]⟩,⟨.and,[6,7]⟩,⟨.or,[8,4]⟩,
    ⟨.and,[0,9]⟩,⟨.or,[8,5]⟩,⟨.and,[3,11]⟩,⟨.or,[10,12]⟩],13⟩

def smaller : Circuit :=
  ⟨[⟨.or,[1,4]⟩,⟨.and,[0,6]⟩,⟨.or,[0,2]⟩,⟨.or,[8,5]⟩,
    ⟨.and,[3,9]⟩,⟨.or,[7,10]⟩],11⟩

instance : DecidableRel G.Adj := inferInstanceAs (DecidableRel (edgeGraph _ _).Adj)

theorem triangleFree : ∀ (a b c : V), G.Adj a b → G.Adj b c → ¬G.Adj c a := by decide

theorem squareFree : PEqualNP.TopForm.NoFourCycle G := by decide

theorem exactGraph : G.edgeFinset.card = 5 := by decide +kernel

theorem isTree : G.IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  constructor
  · decide +kernel
  · rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
    decide +kernel

theorem ao2 : PEqualNP.TopForm.IsAO2 6 C ∧ PEqualNP.TopForm.IsAO2 6 smaller := by decide

theorem computes : circuitFun 6 C = graphFun G ∅ ∧ circuitFun 6 smaller = graphFun G ∅ := by
  constructor <;> funext x <;> revert x <;> decide +kernel

theorem sizeGap : smaller.size = 6 ∧ C.size = 8 := by decide

theorem notMinimum : ¬IsMinimalMonoCircuit 6 C := by
  intro h
  have mono : Monotone2 smaller := fun g hg =>
    ⟨ao2.2.1 g hg,(ao2.2.2.2 g hg).le⟩
  have bound := h.2 smaller mono (computes.2.trans computes.1.symm)
  change 8 ≤ 6 at bound
  omega

theorem ready : ∀ k < C.gates.length, (gateAt C k).op = .and →
    ∃ a b : V, G.Adj a b ∧ Owns 6 C k a b := by
  intro k hk
  have readyFin : ∀ j : Fin 8, (gateAt C j.val).op = .and →
      ∃ a b : V, G.Adj a b ∧ Owns 6 C j.val a b := by decide +kernel
  exact readyFin ⟨k,hk⟩

theorem bad : Owns 6 C 2 (0 : V) 1 ∧ Owns 6 C 2 (2 : V) 3 ∧
    G.Adj 0 1 ∧ G.Adj 2 3 ∧ s((0 : V),1) ≠ s(2,3) := by decide

theorem maskingAtNonedge : ¬G.Adj 1 2 ∧ gateVal 6 C 2 (pairInput 1 2) = true ∧
    InCone 6 C 2 4 ∧ InCone 6 C 2 6 ∧
    gateVal 6 C 4 (pairInput 1 2) = false ∧ gateVal 6 C 6 (pairInput 1 2) = false := by decide

theorem laterOwners (k : Fin 8) (a b : V) (afterBad : 2 < k.val) (edge : G.Adj a b) :
    Owns 6 C k.val a b ↔
      (k.val = 4 ∧ s(a,b) = s((0 : V),4)) ∨ (k.val = 6 ∧ s(a,b) = s((3 : V),5)) := by
  revert k a b
  decide +kernel

private def row (m : ℕ) : V → Bool := fun i => m.testBit i.val

private def replace (k : Fin 8) (g : Gate) : Circuit := ⟨C.gates.set k.val g,C.output⟩

private def wireRows : List (List ℕ) := [
  [12,9,3,3,3,3],
  [1,9,3,3,3,3,1],
  [1,9,3,3,3,3,1,8],
  [1,17,3,3,3,3,1,17,17],
  [1,2,3,3,3,3,1,2,6,6],
  [12,10,40,8,12,12,40,8,40,24,12],
  [1,2,4,8,12,12,1,2,6,6,12,6],
  [1,2,3,3,3,3,1,2,6,6,12,6,3]]

private def constRows : List (List ℕ) := [
  [3,8],
  [3,1],
  [3,1],
  [3,1],
  [3,0],
  [12,8],
  [12,0],
  [3,0]]

/-- No gate can be bypassed by any earlier wire while preserving the output function. -/
theorem noWireBypass (k : Fin 8) (r : Fin (6+k.val)) :
    ∃ x : V → Bool, circuitFun 6 (replace k ⟨.or,[r.val]⟩) x ≠ circuitFun 6 C x := by
  refine ⟨row ((wireRows.getD k.val []).getD r.val 0),?_⟩
  revert k r
  decide +kernel

/-- Every gate is essential even when either constant is available as a replacement. -/
theorem noConstantReplacement (k : Fin 8) (b : Bool) :
    ∃ x : V → Bool, circuitFun 6 (replace k ⟨if b then .and else .or,[]⟩) x ≠ circuitFun 6 C x := by
  refine ⟨row ((constRows.getD k.val []).getD b.toNat 0),?_⟩
  revert k b
  decide +kernel

/-- The first mask can change its OR input to b∨p while the second still covers ad. -/
def firstRewrite : Circuit := replace 3 ⟨.or,[1,4]⟩

/-- The second mask then changes its OR input to (a∨c)∨q. Neither mask needs the bad gate. -/
def bothRewrites : Circuit := ⟨firstRewrite.gates.set 5 ⟨.or,[6,5]⟩,firstRewrite.output⟩

theorem rewrites_preserve : circuitFun 6 firstRewrite = graphFun G ∅ ∧
    circuitFun 6 bothRewrites = graphFun G ∅ := by
  constructor <;> funext x <;> revert x <;> decide +kernel

theorem rewrittenUnused : ∀ k : Fin 8, 2 < k.val →
    8 ∉ (gateAt bothRewrites k.val).inputs := by decide

end PEqualNP.Research.SharedMask
