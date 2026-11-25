import Certificate
import PEqualNP.Outside.L_meta_214
import PEqualNP.Outside.L_meta_5355

namespace Research.CyclicBounds

open SimpleGraph Research.LeafCharge PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4837_aux GraphCircuit4837
open scoped Classical

theorem sparseOfParent {n} {G : SimpleGraph (Fin n)} (parent : Fin n → Fin n)
    (orient : ∀ u v, G.Adj u v → parent u = v ∨ parent v = u) :
    GraphInduction4837.sparse G := by
  intro S
  let pairs := S.image fun u => s(u,parent u)
  have sub : {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S} ⊆ (pairs : Set _) := by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
      rintro ⟨edge,inside⟩
      rcases orient u v edge with h|h
      · exact Finset.mem_image.mpr ⟨u,inside u (Sym2.mem_mk_left _ _),by rw [h]⟩
      · exact Finset.mem_image.mpr ⟨v,inside v (Sym2.mem_mk_right _ _),by rw [h,Sym2.eq_swap]⟩
  have cap := Set.ncard_le_ncard sub (Set.toFinite _)
  rw [Set.ncard_coe_finset] at cap
  exact cap.trans Finset.card_image_le

/-- An ordered matching meeting a cover of the same size determines the exact AND count,
including on graphs with arbitrarily many cycles. -/
theorem exactAndByMatching {n k} {G : SimpleGraph (Fin n)} (L R : Fin k → Fin n)
    (edge : ∀ j, G.Adj (L j) (R j)) (indep : ∀ i j, ¬G.Adj (L i) (L j))
    (order : ∀ i j, i<j → ¬G.Adj (L i) (R j))
    (T : Finset (Fin n)) (cov : CoverPromise.IsVertexCover G T) (card : T.card ≤ k) :
    IsLeast {a : ℕ | ∃ C : Circuit, Monotone2 C ∧ detects G C ∧ ands C.gates = a} k := by
  obtain ⟨C,hm,⟨A,cap,allAnd⟩,det⟩ := PEqualNP.Outside.L_meta_214 n G T cov
  obtain ⟨B,valid,count,mem⟩ := gateIndices C.gates
  have sub : B ⊆ A := by
    intro i hi
    have lt := Finset.mem_range.mp (valid hi)
    have atGate := List.getElem?_eq_getElem lt
    have op := (mem i _ atGate).mp hi
    have isGateAnd : C.gates[i].op = .and := by
      cases h : C.gates[i].op <;> simp_all [isAnd]
    exact allAnd i _ atGate isGateAnd
  have lb := orderedMatchingAnd G L R edge indep order C hm det
  constructor
  · refine ⟨C,hm,det,?_⟩
    have := Finset.card_le_card sub
    omega
  · rintro _ ⟨D,dm,dd,rfl⟩
    exact orderedMatchingAnd G L R edge indep order D dm dd

/-- A k-vertex cover matching the ordered lower bound supplies a circuit attaining it. -/
theorem exactByMatching {n k} {G : SimpleGraph (Fin n)} (hf : NoSquare G)
    (sparse : GraphInduction4837.sparse G) (L R : Fin k → Fin n)
    (edge : ∀ j, G.Adj (L j) (R j)) (indep : ∀ i j, ¬G.Adj (L i) (L j))
    (order : ∀ i j, i<j → ¬G.Adj (L i) (R j))
    (T : Finset (Fin n)) (cov : CoverPromise.IsVertexCover G T) (card : T.card ≤ k) :
    IsLeast {s : ℕ | ∃ C : Circuit, Monotone2 C ∧ detects G C ∧ C.size = s}
      (G.edgeSet.ncard + k - 1) := by
  classical
  have lb (D : Circuit) (hm : Monotone2 D) (hd : detects G D) :=
    orderedTotal hf (.base G sparse) L R edge indep order D hm hd
  obtain ⟨C,mono,funEq,small,_⟩ := PEqualNP.Outside.L_meta_5355 n G T cov
  have det : detects G C := by
    intro x
    have := congrFun funEq x
    change C.eval (List.ofFn x) = _ at this
    rw [this]
    simp [NestedCover.graphFun]
  constructor
  · exact ⟨C,mono,det,by have := lb C mono det; omega⟩
  · rintro s ⟨D,dm,dd,rfl⟩
    have := lb D dm dd
    omega

namespace SunletSix

def parent : Fin 12 → Fin 12 := ![6,7,8,9,10,11,7,8,9,10,11,6]
def graph : SimpleGraph (Fin 12) := SimpleGraph.fromRel (fun u v => parent u = v)
abbrev left (i : Fin 6) : Fin 12 := Fin.castAdd 6 i
abbrev right (i : Fin 6) : Fin 12 := Fin.natAdd 6 i

private theorem square : NoSquare graph := by unfold NoSquare graph; decide +kernel
private theorem oriented : ∀ u v, graph.Adj u v → parent u = v ∨ parent v = u := by
  intro u v h
  exact h.2

theorem exactSeventeen : IsLeast {s : ℕ | ∃ C : Circuit, Monotone2 C ∧ detects graph C ∧ C.size=s} 17 := by
  let T : Finset (Fin 12) := {6,7,8,9,10,11}
  have total := exactByMatching square (sparseOfParent parent oriented) left right
    (by unfold graph; decide +kernel) (by unfold graph; decide +kernel)
    (by unfold graph; decide +kernel) T (by unfold CoverPromise.IsVertexCover graph; decide +kernel)
    (by decide)
  have edges : graph.edgeSet.ncard = 12 := by
    letI : DecidableRel graph.Adj := fun a b => inferInstanceAs
      (Decidable ((SimpleGraph.fromRel (fun u v => parent u = v)).Adj a b))
    have hc : graph.edgeFinset.card = 12 := by decide +kernel
    exact (Set.ncard_eq_toFinset_card' graph.edgeSet).trans hc
  simpa [edges] using total

end SunletSix
end Research.CyclicBounds
