import PhysicalChain
import Normalize
import FanoBounds
import CleanAnd
import PEqualNP.Outside.L_meta_3008

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.Research2583

namespace Packed4387

def raw : List Col := [95229015649943559,63038587666488,256462815680,4292497062759936,
  8521481482240,14003410187812864,55389823207997440,189297016294081033,
  155696362464477250,218994303132270608,183565875465490436,229736628138025984,
  270286071508633728,288160007407550752]

def base : List Col := raw ++ [95274182876594239]
def seeds : List Col := 0 :: BitVec.allOnes 58 :: base
def target : Col := 2097151

private theorem initial : Real raw base [firstGate] := by
  refine ⟨rfl,rfl,by decide,?_⟩
  intro k
  have key : (95274182876594239 : Col) = (95229015649943559 : Col) ||| 63038587666488 := by decide
  change row k raw ++ [(95229015649943559 : Col).getLsbD k ||
      ((63038587666488 : Col).getLsbD k || false)] = row k raw ++ [(95274182876594239 : Col).getLsbD k]
  rw [key,BitVec.getLsbD_or,Bool.or_false]

private theorem isPhysical {xs : List Col} (length : xs.length ≤ 25)
    (chain : Chain seeds xs) (hit : target ∈ seeds++xs) :
    ∃ C : Circuit, IsAO2 14 C ∧ C.gates.head? = some firstGate ∧ C.size ≤ 26 ∧
      ∀ k : ℕ, C.eval (row k raw) = target.getLsbD k := by
  obtain ⟨ys,budget,last,normal⟩ := PEqualNP.Research4387.normalizeChain base xs target
    chain hit (by decide) (by decide) (by decide)
  obtain ⟨gs,built⟩ := compile initial ys (fun j => (normal j).2.2.2)
  obtain ⟨before,eq⟩ := List.getLast?_eq_some_iff.mp last
  have hmem : target ∈ base++ys := by simp [eq]
  obtain ⟨idx,points⟩ := List.mem_iff_get.mp hmem
  refine ⟨⟨gs,idx.val⟩,built.ao,built.first,?_,?_⟩
  · have h := built.count
    have hr : raw.length = 14 := rfl
    have hb : base.length = 15 := rfl
    rw [hr,List.length_append,hb] at h
    change gs.length ≤ 26
    omega
  · intro k
    change ((Circuit.mk gs 0).wires (row k raw)).getD idx.val false = _
    rw [built.wires k]
    rw [List.getD_eq_getElem _ _ (by simpa [row] using idx.isLt)]
    simp only [row,List.getElem_map]
    exact congrArg (fun c : Col => c.getLsbD k) points

private theorem isComputing {C : Circuit} (ao : IsAO2 14 C)
    (table : ∀ k : ℕ, C.eval (row k raw) = target.getLsbD k) : Fano.Computes C := by
  have mono : Monotone2 C := fun g hg => ⟨ao.1 g hg,(ao.2.2 g hg).le⟩
  have exactC := PEqualNP.Outside.L_meta_3008 C mono table
  have link : ∀ a b : Fin 14, (a.val,b.val) ∈ PEqualNP.Outside.L_meta_3008_aux.edges ↔
      ∃ p l : Fin 7, Fano.I p l ∧ a = Fin.castAdd 7 p ∧ b = Fin.natAdd 7 l := by
    decide +kernel
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  change C.eval (List.ofFn x) = true ↔ _
  rw [exactC x]
  change (∃ a b : Fin 14, (a.val,b.val) ∈ PEqualNP.Outside.L_meta_3008_aux.edges ∧ x a = true ∧ x b = true) ↔ _
  constructor
  · rintro ⟨a,b,edge,xa,xb⟩
    obtain ⟨p,l,inc,rfl,rfl⟩ := (link a b).mp edge
    exact ⟨p,l,inc,xa,xb⟩
  · rintro ⟨p,l,inc,xp,xl⟩
    exact ⟨_,_,(link _ _).mpr ⟨p,l,inc,rfl,rfl⟩,xp,xl⟩

/-- A hypothetical 25-step chain gives a physical toposorted AO2 circuit with
    a prescribed first gate. Two ANDs are nested, and some AND accepts a
    rejected input supported on at most two raw vertices. -/
theorem physicalCounterexample (xs : List Col) (length : xs.length ≤ 25)
    (chain : Chain seeds xs) (hit : target ∈ seeds++xs) :
    ∃ C : Circuit, IsAO2 14 C ∧ C.gates.head? = some firstGate ∧ C.size ≤ 26 ∧
      Fano.Computes C ∧ Fano.Nested C ∧
      ∃ k, k < C.size ∧ (gateAt C k).op = .and ∧
        ∃ u v : Fin 14, gateVal 14 C k (pairInput u v) = true ∧
          C.eval (List.ofFn (pairInput u v)) = false := by
  obtain ⟨C,ao,first,size,table⟩ := isPhysical length chain hit
  have computes := isComputing ao table
  have nested : Fano.Nested C := by
    by_contra h
    have := Fano.single_and_layer ao computes h
    omega
  have dirty := PlaneReadOne.dirtyWitness Fano.I 2 C (by decide) (by decide)
    Fano.plane_axioms.1 Fano.plane_axioms.2 ao computes (by omega)
  obtain ⟨k,hk,op,u,v,_,gate,output⟩ := dirty
  exact ⟨C,ao,first,size,computes,nested,k,hk,op,u,v,gate,output⟩

end Packed4387

#print axioms Packed4387.physicalCounterexample
