import NoNestedGraph
import CleanAnd
import LineStarUpper

namespace PEqualNP.Research2583.NoNested
open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover EdgeOwnership TopForm ReadK

/-- Every plane order, including all labelings, for the class with no AND in another AND's cone. -/
theorem plane_bound_on_output {N : Nat} (q : Nat) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hq : 2 ≤ q) (order : N = q^2+q+1)
    (lines : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
    (ao : IsAO2 (N+N) C) (correct : PlaneReadOne.Computes I C)
    (layer : OnOutput (N+N) C) : N*(q+2) ≤ C.size+1 := by
  have hn : 0 < N := by omega
  let l : Fin N := ⟨0,hn⟩
  have hp : (Finset.univ.filter fun p => I p l).Nonempty :=
    Finset.card_pos.mp (by rw [lines]; omega)
  obtain ⟨p,hp⟩ := hp
  have edge : (PlaneReadOne.graph I).Adj (Fin.castAdd N p) (Fin.natAdd N l) := by
    simpa only [PlaneReadOne.graph,PlaneReadOne.adjacent,Fin.addCases_left,Fin.addCases_right]
      using (Finset.mem_filter.mp hp).2
  apply PlaneReadOne.ofCoverBound I q C hq order lines unique
  have hm : Monotone2 C := fun g hg => ⟨ao.1 g hg,Nat.le_of_eq (ao.2.2 g hg)⟩
  apply cover_bound_on_output (PlaneReadOne.graph I) ⟨_,_,edge⟩ (PlaneReadOne.cycleFree I unique) C hm ao.2.1 layer
  intro x
  change circuitFun (N+N) C x = true ↔ _
  rw [correct x,decide_eq_true_eq,PlaneReadOne.graph_eval I x]

theorem plane_normalization_on_output {N : Nat} (q : Nat) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hq : 2 ≤ q) (order : N = q^2+q+1)
    (lines : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
    (ao : IsAO2 (N+N) C) (correct : PlaneReadOne.Computes I C)
    (layer : OnOutput (N+N) C) :
    ∃ D : Circuit, IsAO2 (N+N) D ∧ PlaneReadOne.Computes I D ∧ D.size ≤ C.size ∧
      IsReadK (N+N) D 1 := by
  have budget := plane_bound_on_output q I C hq order lines unique ao correct layer
  obtain ⟨D,hD,fD,sD,read⟩ := LineStars.regular_read_upper N q I (by omega) lines
  exact ⟨D,hD,fD,by omega,read⟩

theorem plane_bound {N : Nat} (q : Nat) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hq : 2 ≤ q) (order : N = q^2+q+1)
    (lines : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
    (ao : IsAO2 (N+N) C) (correct : PlaneReadOne.Computes I C)
    (layer : ¬∃ i j, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧
      InCone (N+N) C i j) : N*(q+2) ≤ C.size+1 := by
  apply plane_bound_on_output q I C hq order lines unique ao correct
  rintro o hout ⟨i,j,hi,hj,hij,_⟩
  exact layer ⟨i,j,hi,hj,hij⟩

theorem plane_normalization {N : Nat} (q : Nat) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hq : 2 ≤ q) (order : N = q^2+q+1)
    (lines : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
    (ao : IsAO2 (N+N) C) (correct : PlaneReadOne.Computes I C)
    (layer : ¬∃ i j, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧
      InCone (N+N) C i j) :
    ∃ D : Circuit, IsAO2 (N+N) D ∧ PlaneReadOne.Computes I D ∧ D.size ≤ C.size ∧
      IsReadK (N+N) D 1 := by
  have budget := plane_bound q I C hq order lines unique ao correct layer
  obtain ⟨D,hD,fD,sD,read⟩ := LineStars.regular_read_upper N q I (by omega) lines
  exact ⟨D,hD,fD,by omega,read⟩

#print axioms plane_normalization_on_output
#print axioms plane_normalization
end PEqualNP.Research2583.NoNested
