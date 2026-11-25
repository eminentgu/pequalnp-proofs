import LocalReaders
import SafeTail
import ComponentStability
import SubdivisionAssembly

namespace VertexPeel.LocalReaders
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.Core
  PEqualNP.Outside.L_meta_1774
open VertexPeel.ZeroFold VertexPeel.LocalizedPeel VertexPeel.CoverCircuit

variable {n : ℕ} (G : SimpleGraph (Fin n)) [base : DecidableRel G.Adj]

/-- A localized stable side suffices in an arbitrary square-free graph. -/
theorem uniform_of_local_side (sq : NoFourCycle G) (S : Finset (Fin n)) (nonempty : S.Nonempty)
    (good : ∀ z∈S, G.degree z=2 ∧ ¬SidePeel.Drops G z)
    (side : ∀ z∈S, ∃ t∉S, G.Adj t z ∧ ∀ y, G.Adj t y → y∈S) : Uniform G := by
  classical
  let B := S.image Fin.val
  have iffS (v : Fin n) : v.val∈B ↔ v∈S := by simp [B,Fin.val_inj]
  have bounded (v) (hv : v∈B) : v<n := by
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hv
    exact w.isLt
  have localB : LocalSide G B := by
    intro a ha
    obtain ⟨t,tS,ta,allN⟩ := side a ((iffS _).mp ha)
    exact ⟨t,fun h => tS ((iffS _).mp h),ta,fun y e => (iffS _).mpr (allN y e)⟩
  let P (k : ℕ) := ∃ C : Circuit, IsAO2 n C ∧ circuitFun n C=graphFun G ∅ ∧ C.size=k
  by_cases existsP : ∃ k,P k
  · obtain ⟨C,ao,ok,sz⟩ := Nat.find_spec existsP
    have least : IsLeastAO G C := ⟨ao,ok,fun E eao ec => sz ▸ Nat.find_min' existsP ⟨E,eao,ec,rfl⟩⟩
    obtain ⟨D,dleast,clean,_⟩ := SafeTail.exists_clean_readers G C least
    have closed : OrClosed G D := by
      intro j hj _ d hd sound
      exact (clean j hj d (by simpa only [gateAt_eq D j hj] using hd) sound).2
    have degree (v : Fin n) (hv : v.val∈B) := (good v ((iffS v).mp hv)).1
    have stable (v : Fin n) (hv : v.val∈B) := (good v ((iffS v).mp hv)).2
    apply of_localized_two G D dleast.1 dleast.2.1 dleast.2.2 B degree stable
    exact localized_two G D B bounded (nonempty.image _) localB sq
      (fun v hv => (degree v hv).ge) stable dleast.1 dleast.2.1 closed
  · obtain ⟨z,hz⟩ := nonempty
    exact ⟨z,by rw [(good z hz).1]; decide,fun C ao ok => (existsP ⟨C.size,C,ao,ok,rfl⟩).elim⟩

/-- Check one vertex in any component. All of its neighbors survive in cover
number after deletion and have degree two. The conclusion is uniform in the circuit. -/
theorem stable_neighborhood (sq : NoFourCycle G) (t : Fin n) (active : 0<G.degree t)
    (neighbors : ∀ a, G.Adj t a → G.degree a=2 ∧ ¬SidePeel.Drops G a) : Uniform G := by
  apply uniform_of_local_side G sq (G.neighborFinset t) (Finset.card_pos.mp active)
  · intro z hz
    exact neighbors z ((G.mem_neighborFinset _ _).mp hz)
  · intro z hz
    exact ⟨t,by simp,(G.mem_neighborFinset _ _).mp hz,fun y e => (G.mem_neighborFinset _ _).mpr e⟩

private theorem branch (c : Fin n → Bool) (proper : ∀ u v, G.Adj u v → c u≠c v)
    (low : ∀ v, c v=false → G.degree v≤2) (sq : NoFourCycle G)
    (leafless : ∀ v,G.degree v≠1) (high : ∃ u,2<G.degree u) : Uniform G := by
  obtain ⟨S,nonempty,good,side⟩ := ComponentStability.branch_candidates G c proper low
    (fun ⟨v,hv⟩ => leafless v hv) high
  exact uniform_of_local_side G sq S nonempty good side

/-- No connectivity, minimum degree, component bound, cover bound, or degree bound
on the opposite color class is assumed. Both posted conclusions hold on this graph. -/
theorem side_degree_two_sharp (c : Fin n → Bool) (proper : ∀ u v, G.Adj u v → c u≠c v)
    (low : ∀ v,c v=false → G.degree v≤2) (sq : NoFourCycle G) (many : 2≤G.edgeFinset.card) :
    (Uniform G ∧ StepAt G) ∧ (∀ [_d : DecidableRel G.Adj] (C : Circuit), Monotone2 C →
      circuitFun n C = graphFun G ∅ → G.edgeFinset.card + Loc.tau G ≤ C.size+1) := by
  apply subdivision_from_branch G c proper low sq many
  intro H _ sub _ leafless high
  exact branch H c (fun u v e => proper u v (sub e))
    (fun v hv => (H.degree_le_of_le sub).trans (low v hv)) (PivotAND.square_mono sub sq) leafless high

#print axioms stable_neighborhood
#print axioms side_degree_two_sharp
end VertexPeel.LocalReaders
