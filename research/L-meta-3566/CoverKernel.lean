import StableExtension
import CycleCover
import Mathlib.Data.Finset.Powerset

namespace VertexPeel.CoverKernel
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.CoverPromise PEqualNP.TopForm

/-- Count only vertices on at least one edge. -/
def active {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Finset (Fin n) :=
  Finset.univ.filter (fun v => 0 < G.degree v)

/-- Two distinct leaves have precisely the same single neighbor. -/
def TwinLeaves {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  ∃ a b u, a ≠ b ∧ G.neighborFinset a = {u} ∧ G.neighborFinset b = {u}

/-- A minimum cover is not required. Distinct non-leaves outside the cover have
different pairs of neighbors, while distinct leaves have different sole neighbors. -/
theorem active_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (square : NoFourCycle G) (reduced : ¬TwinLeaves G) (T : Finset (Fin n))
    (cover : IsVertexCover G T) :
    (active G).card ≤ 2 * T.card + T.card.choose 2 := by
  classical
  let N (v : Fin n) := G.neighborFinset v
  let sig (v : Fin n) : Finset (Fin n) :=
    if h : 2 ≤ (N v).card then (Finset.exists_subset_card_eq h).choose else N v
  have desc (v : Fin n) : sig v ⊆ N v ∧ (2 ≤ (N v).card → (sig v).card = 2) ∧
      ((N v).card < 2 → sig v = N v) := by
    by_cases h : 2 ≤ (N v).card
    · have witnesses := (Finset.exists_subset_card_eq h).choose_spec
      exact ⟨by simpa [sig,h] using witnesses.1, fun _ => by simpa [sig,h] using witnesses.2,
        fun small => False.elim (by omega)⟩
    · simp [sig,h]
  let exterior := active G \ T
  have outside {v : Fin n} (hv : v ∈ exterior) : 0 < (N v).card ∧ v ∉ T := by
    obtain ⟨valid,out⟩ := Finset.mem_sdiff.mp hv
    exact ⟨(Finset.mem_filter.mp valid).2,out⟩
  let codomain := T.powersetCard 1 ∪ T.powersetCard 2
  have maps : Set.MapsTo sig exterior codomain := by
    intro v hv
    obtain ⟨pos,out⟩ := outside hv
    obtain ⟨sub,two,one⟩ := desc v
    have subT : sig v ⊆ T := by
      intro u hu
      exact (cover v u ((G.mem_neighborFinset v u).mp (sub hu))).resolve_left out
    by_cases large : 2 ≤ (N v).card
    · exact Finset.mem_union_right _ (Finset.mem_powersetCard.mpr ⟨subT,two large⟩)
    · exact Finset.mem_union_left _ (Finset.mem_powersetCard.mpr ⟨subT,by
        rw [one (by omega)]; omega⟩)
  have injective : (↑exterior : Set (Fin n)).InjOn sig := by
    intro v hv w hw eq
    by_contra ne
    have common : sig v ⊆ Finset.univ.filter (fun u => G.Adj v u ∧ G.Adj w u) := by
      intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (G.mem_neighborFinset v u).mp ((desc v).1 hu),
        (G.mem_neighborFinset w u).mp ((desc w).1 (eq ▸ hu))⟩
    have small := (Finset.card_le_card common).trans (square v w ne)
    have small' : (sig w).card ≤ 1 := eq ▸ small
    have nv : (N v).card < 2 := by
      by_contra! h
      have := (desc v).2.1 h
      omega
    have nw : (N w).card < 2 := by
      by_contra! h
      have := (desc w).2.1 h
      omega
    have pos := (outside hv).1
    obtain ⟨u,un⟩ := Finset.card_eq_one.mp (show (N v).card = 1 by omega)
    rw [(desc v).2.2 nv,(desc w).2.2 nw] at eq
    exact reduced ⟨v,w,u,ne,un,eq.symm.trans un⟩
  have count := Finset.card_le_card_of_injOn sig maps injective
  have second : codomain.card ≤ T.card + T.card.choose 2 := by
    simpa only [codomain,Finset.card_powersetCard,Nat.choose_one_right] using
      (Finset.card_union_le (T.powersetCard 1) (T.powersetCard 2))
  have within : active G ⊆ exterior ∪ T := by
    intro v hv
    by_cases h : v ∈ T
    · exact Finset.mem_union_right _ h
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hv,h⟩)
  have first := (Finset.card_le_card within).trans (Finset.card_union_le exterior T)
  omega

/-- A genuine one-edge reduction. The cover number is preserved even when the input cover
has no prescription at the two leaves. -/
theorem reduce_twin {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (twins : TwinLeaves G) :
    ∃ a u, G.Adj a u ∧ (∀ v, G.Adj a v → v = u) ∧
      Loc.tau (G.deleteIncidenceSet a) = Loc.tau G ∧
      (G.deleteIncidenceSet a).edgeFinset.card + 1 = G.edgeFinset.card ∧
      (StableExtension.Numerical (G.deleteIncidenceSet a) (Loc.tau (G.deleteIncidenceSet a)) →
       StableExtension.Numerical G (Loc.tau G)) := by
  obtain ⟨a,b,u,ne,na,nb⟩ := twins
  have eqs (v : Fin n) : G.Adj a v ↔ v = u := by
    rw [← G.mem_neighborFinset,na,Finset.mem_singleton]
  have eqt (v : Fin n) : G.Adj b v ↔ v = u := by
    rw [← G.mem_neighborFinset,nb,Finset.mem_singleton]
  have au := (eqs u).mpr rfl
  have only := fun v => (eqs v).mp
  have stable := Leaves.sharedNeighborStable G a b u ne au ((eqt u).mpr rfl) only
    (fun v => (eqt v).mp)
  have same : Loc.tau (G.deleteIncidenceSet a) = Loc.tau G := by
    apply Nat.le_antisymm
    · obtain ⟨S,c,size⟩ := Loc.tau_attained G
      rw [← size]
      exact Loc.tau_le _ _ (fun i j e => c i j (G.deleteIncidenceSet_le a e))
    · obtain ⟨S,c,size⟩ := Loc.tau_attained (G.deleteIncidenceSet a)
      obtain ⟨T,d,k⟩ := stable S c
      rw [← size]
      exact (Loc.tau_le _ T d).trans k
  have deg : G.degree a = 1 := by rw [← G.card_neighborFinset_eq_degree,na]; simp
  have pos : 0 < G.edgeFinset.card := Finset.card_pos.mpr ⟨s(a,u),by simpa using au⟩
  refine ⟨a,u,au,only,same,?_,?_⟩
  · rw [G.card_edgeFinset_deleteIncidenceSet,deg]; omega
  · intro old
    rw [same] at old
    exact StableExtension.step_numerical au only old

/-- Sufficient to check the reduced, bounded-support graphs in any leaf-hereditary class. -/
theorem of_reduced {n : ℕ} (P : SimpleGraph (Fin n) → Prop)
    (inherit : ∀ (G : SimpleGraph (Fin n)) (a u : Fin n), P G → G.Adj a u →
      (∀ v, G.Adj a v → v = u) → Loc.tau (G.deleteIncidenceSet a) = Loc.tau G →
      P (G.deleteIncidenceSet a))
    (kernel : ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], P G → NoFourCycle G →
      ¬TwinLeaves G → (active G).card ≤ 2 * (Loc.tau G) + (Loc.tau G).choose 2 →
      StableExtension.Numerical G (Loc.tau G))
    (G : SimpleGraph (Fin n)) [instG : DecidableRel G.Adj] (member : P G) (square : NoFourCycle G) :
    StableExtension.Numerical G (Loc.tau G) := by
  suffices go : ∀ m (H : SimpleGraph (Fin n)) [DecidableRel H.Adj], H.edgeFinset.card = m →
      P H → NoFourCycle H → StableExtension.Numerical H (Loc.tau H) by
    intro inst' C mono correct
    have sameInst : inst' = instG := Subsingleton.elim _ _
    subst inst'
    exact @go G.edgeFinset.card G instG rfl member square instG C mono correct
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro H inst size prop sq inst' C mono correct
    have sameInst : inst' = inst := Subsingleton.elim _ _
    subst inst'
    by_cases twins : TwinLeaves H
    · obtain ⟨a,u,edge,only,same,drop,upgrade⟩ := reduce_twin H twins
      have recur : StableExtension.Numerical (H.deleteIncidenceSet a) (Loc.tau (H.deleteIncidenceSet a)) := by
        let J := H.deleteIncidenceSet a
        let decJ : DecidableRel J.Adj := inferInstance
        have less : J.edgeFinset.card < m := by dsimp [J]; omega
        have ok := inherit H a u prop edge only same
        have sq' := square_cut H a sq
        intro instJ D mon cor
        have sameDec : instJ = decJ := Subsingleton.elim _ _
        subst instJ
        exact @ih J.edgeFinset.card less J decJ rfl ok sq' decJ D mon cor
      exact upgrade recur C mono correct
    · obtain ⟨T,c,t⟩ := Loc.tau_attained H
      have count := active_bound H sq twins T c
      rw [t] at count
      exact kernel H prop sq twins count C mono correct

#print axioms active_bound
#print axioms reduce_twin
#print axioms of_reduced
end VertexPeel.CoverKernel
