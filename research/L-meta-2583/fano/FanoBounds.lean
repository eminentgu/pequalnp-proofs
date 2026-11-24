import Fano27
import PEqualNP.Outside.L_meta_1983
import PEqualNP.Outside.L_meta_1483

namespace PEqualNP.Research2583.Fano
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

def Computes (C : Circuit) : Prop := ∀ x : Fin (7+7) → Bool, circuitFun 14 C x =
  decide (∃ p l : Fin 7, I p l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)

def Nested (C : Circuit) : Prop := ∃ i j, (gateAt C i).op = .and ∧
  (gateAt C j).op = .and ∧ EdgeOwnership.InCone 14 C i j

private theorem mono {C : Circuit} (h : TopForm.IsAO2 14 C) : Monotone2 C := by
  intro g hg
  exact ⟨h.1 g hg, Nat.le_of_eq (h.2.2 g hg)⟩

private def FlagWires (a b : Fin 14) : Prop := ∃ p l : Fin 7, I p l ∧
  a = Fin.castAdd 7 p ∧ b = Fin.natAdd 7 l

instance {a b : Fin 14} : Decidable (FlagWires a b) := by unfold FlagWires; infer_instance

private theorem wire_numbers : ∀ a b : Fin 14,
    (a.val,b.val) ∈ PEqualNP.Outside.L_meta_1983.hL ↔ FlagWires a b := by decide +kernel

private theorem flags_eval {C : Circuit} (hC : Computes C) (x : Fin 14 → Bool) :
    C.eval (List.ofFn x) = true ↔ ∃ a b : Fin 14, FlagWires a b ∧ x a = true ∧ x b = true := by
  change circuitFun 14 C x = true ↔ _
  rw [hC,decide_eq_true_eq]
  constructor
  · rintro ⟨p,l,h,ha,hb⟩
    exact ⟨_,_,⟨p,l,h,rfl,rfl⟩,ha,hb⟩
  · rintro ⟨a,b,⟨p,l,h,rfl,rfl⟩,ha,hb⟩
    exact ⟨p,l,h,ha,hb⟩

theorem single_and_layer {C : Circuit} (ao : TopForm.IsAO2 14 C) (hC : Computes C)
    (h : ¬ Nested C) : 27 ≤ C.size := by
  apply PEqualNP.Outside.L_meta_1983 C (mono ao) ao.2.1 h
  intro x
  rw [flags_eval hC]
  change _ ↔ ∃ a b : Fin 14, (a.val,b.val) ∈ PEqualNP.Outside.L_meta_1983.hL ∧ x a = true ∧ x b = true
  simp only [wire_numbers]

private def Rel (a b : Fin 14) : Prop := a.val < 7 ∧ 7 ≤ b.val ∧
  (a.val + (b.val - 7)) % 7 ∈ ({0,1,3} : Finset Nat)
instance {a b : Fin 14} : Decidable (Rel a b) := by unfold Rel; infer_instance

private theorem from_pairs : ∀ a b : Fin 14,
    (SimpleGraph.fromRel Rel).Adj a b ↔ FlagWires a b ∨ FlagWires b a := by
  intro a b
  rw [SimpleGraph.fromRel_adj]
  revert a b
  decide +kernel

theorem twenty {C : Circuit} (ao : TopForm.IsAO2 14 C) (hC : Computes C) : 20 ≤ C.size := by
  apply PEqualNP.Outside.L_meta_1483 C (mono ao)
  intro x
  rw [flags_eval hC]
  change _ ↔ ∃ a b, (SimpleGraph.fromRel Rel).Adj a b ∧ x a = true ∧ x b = true
  simp only [from_pairs]
  constructor
  · rintro ⟨a,b,h,ha,hb⟩; exact ⟨a,b,Or.inl h,ha,hb⟩
  · rintro ⟨a,b,h,ha,hb⟩
    rcases h with h | h
    · exact ⟨a,b,h,ha,hb⟩
    · exact ⟨b,a,h,hb,ha⟩

end PEqualNP.Research2583.Fano
