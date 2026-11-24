import PhysicalHeawood

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.Research2583

namespace Packed4387

theorem checkedPhysical :
  let base := List.map (BitVec.ofNat 58) ([95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752, 95274182876594239] : List Nat)
  ∀ xs : List (BitVec 58), xs.length ≤ 25 →
    (∀ j : Fin xs.length, let w := base ++ xs.take j.val
      ∃ a ∈ w, ∃ b ∈ w, xs.get j = a &&& b ∨ xs.get j = a ||| b) →
    (2097151 : BitVec 58) ∈ xs →
    ∃ C : Circuit, IsAO2 14 C ∧ C.gates.head? = some (⟨.or,[0,1]⟩ : Gate) ∧ C.size ≤ 26 ∧
    (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) =
      decide (∃ p l : Fin 7, (p.val+l.val)%7 ∈ ([0,1,3] : List Nat) ∧
        x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) ∧
    (∃ i j, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 14 C i j) ∧
    (∃ k, k < C.size ∧ (gateAt C k).op = .and ∧ ∃ u v : Fin 14,
      gateVal 14 C k (pairInput u v) = true ∧ C.eval (List.ofFn (pairInput u v)) = false) := by
  intro start xs budget chain hit
  have start_eq : start = base := rfl
  rw [start_eq] at chain
  have old : Chain seeds xs := by
    intro j
    obtain ⟨a,ha,b,hb,h⟩ := chain j
    exact ⟨a,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha),
      b,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hb),h⟩
  obtain ⟨C,ao,first,size,func,nested,dirty⟩ := physicalCounterexample xs budget old (List.mem_append_right _ hit)
  refine ⟨C,ao,first,size,?_,nested,dirty⟩
  have table : ∀ p l : Fin 7, Fano.I p l ↔ (p.val+l.val)%7 ∈ ([0,1,3] : List Nat) := by
    decide +kernel
  intro x
  change circuitFun 14 C x = _
  rw [func]
  apply decide_eq_decide.mpr
  simp only [table]

theorem checkedPhysicalShort :
  let base := List.map (BitVec.ofNat 58) ([95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752, 95274182876594239] : List Nat)
  ∀ xs : List (BitVec 58), xs.length ≤ 25 →
    (∀ j : Fin xs.length, let w := base ++ xs.take j.val
      ∃ a ∈ w, ∃ b ∈ w, xs.get j = a &&& b ∨ xs.get j = a ||| b) →
    (2097151 : BitVec 58) ∈ xs →
    ∃ C : Circuit, IsAO2 14 C ∧ C.gates.head? = some (⟨.or,[0,1]⟩ : Gate) ∧ C.size ≤ 26 ∧
    (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) =
      decide (∃ p l : Fin 7, (p.val+l.val)%7 ∈ ([0,1,3] : List Nat) ∧
        x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) := by
  intro start xs budget chain hit
  obtain ⟨C,ao,head,size,correct,_⟩ := checkedPhysical xs budget chain hit
  exact ⟨C,ao,head,size,correct⟩

theorem checkedGateFacts :
  ∀ C : Circuit, (IsAO2 14 C ∧ C.gates.head? = some (⟨.or,[0,1]⟩ : Gate) ∧ C.size ≤ 26 ∧
    (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) =
      decide (∃ p l : Fin 7, (p.val+l.val)%7 ∈ ([0,1,3] : List Nat) ∧
        x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true))) →
    (∃ i j, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 14 C i j) ∧
    (∃ k, k < C.size ∧ (gateAt C k).op = .and ∧ ∃ u v : Fin 14,
      gateVal 14 C k (pairInput u v) = true ∧ C.eval (List.ofFn (pairInput u v)) = false) := by
  rintro C ⟨ao,_,size,correct⟩
  have table : ∀ p l : Fin 7, Fano.I p l ↔ (p.val+l.val)%7 ∈ ([0,1,3] : List Nat) := by
    decide +kernel
  have computes : Fano.Computes C := by
    intro x
    change C.eval (List.ofFn x) = _
    rw [correct]
    apply decide_eq_decide.mpr
    simp only [table]
  have nested : Fano.Nested C := by
    by_contra h
    have := Fano.single_and_layer ao computes h
    omega
  have dirty := PlaneReadOne.dirtyWitness Fano.I 2 C (by decide) (by decide)
    Fano.plane_axioms.1 Fano.plane_axioms.2 ao computes (by omega)
  obtain ⟨k,hk,op,u,v,_,gate,output⟩ := dirty
  exact ⟨nested,k,hk,op,u,v,gate,output⟩

def physicalResidual : Prop :=
  ¬ (∃ C : Circuit, IsAO2 14 C ∧ C.gates.head? = some (⟨.or,[0,1]⟩ : Gate) ∧ C.size ≤ 26 ∧
    (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) =
      decide (∃ p l : Fin 7, (p.val+l.val)%7 ∈ ([0,1,3] : List Nat) ∧
        x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) ∧
    (∃ i j, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 14 C i j) ∧
    (∃ k, k < C.size ∧ (gateAt C k).op = .and ∧ ∃ u v : Fin 14,
      gateVal 14 C k (pairInput u v) = true ∧ C.eval (List.ofFn (pairInput u v)) = false))

end Packed4387

#print axioms Packed4387.checkedPhysical
#print axioms Packed4387.checkedPhysicalShort
#print axioms Packed4387.checkedGateFacts
