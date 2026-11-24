import PEqualNP.Outside.R_meta_2685_73
import PEqualNP.Outside.L_meta_3243
import PEqualNP.Outside.L_meta_3245
import StarForestCharge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

namespace IncidencePeeling

/-- The remaining star must leave a nonempty residual circuit and pay for its connecting OR. -/
def PeelingStep : Prop :=
  ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit), E.Nonempty →
      ¬ ((∃ p : Fin n, ∀ e ∈ E, e.1 = p) ∨ (∃ l : Fin m, ∀ e ∈ E, e.2 = l)) →
      (∀ p q l s, p ≠ q → l ≠ s → ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)) →
      IsAO2 (n+m) C → circuitFun (n+m) C = PEqualNP.ReadTwo.fpl n (fun p l => (p,l) ∈ E) →
      ∃ F ⊂ E, ((∃ p : Fin n, ∀ e ∈ E \ F, e.1 = p) ∨ (∃ l : Fin m, ∀ e ∈ E \ F, e.2 = l)) ∧
        F.Nonempty ∧ ∃ D : Circuit, IsAO2 (n+m) D ∧
          circuitFun (n+m) D = PEqualNP.ReadTwo.fpl n (fun p l => (p,l) ∈ F) ∧
          D.size + (E \ F).card + 1 ≤ C.size

/-- The terminal star bound and both compiler properties discharge three of the four premises. -/
theorem normal_form (h : PeelingStep) :
    ∀ (n m : ℕ) (I : Fin n → Fin m → Prop) [DecidableRel I] (C : Circuit),
      (∀ p q l s, p ≠ q → l ≠ s → ¬ (I p l ∧ I p s ∧ I q l ∧ I q s)) →
      IsAO2 (n+m) C → (∀ x, circuitFun (n+m) C x = PEqualNP.ReadTwo.fpl n I x) →
      ∃ (D : Circuit) (P L : Finset ℕ), IsAO2 (n+m) D ∧
        (∀ x, circuitFun (n+m) D x = PEqualNP.ReadTwo.fpl n I x) ∧ D.size ≤ C.size ∧
        (∀ w ∈ P, w < n ∨ ∃ i < D.gates.length, w = n+m+i ∧
          (NestedCover.gateAt D i).op = GateOp.or ∧ ∀ u ∈ (NestedCover.gateAt D i).inputs, u ∈ P) ∧
        (∀ w ∈ L, (n ≤ w ∧ w < n+m) ∨ ∃ i < D.gates.length, w = n+m+i ∧
          (NestedCover.gateAt D i).op = GateOp.or ∧ ∀ u ∈ (NestedCover.gateAt D i).inputs, u ∈ L) ∧
        ∀ i < D.gates.length, (NestedCover.gateAt D i).op = GateOp.and →
          ∃ a b, (NestedCover.gateAt D i).inputs = [a,b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)) :=
  PEqualNP.Outside.R_meta_2685_73 (fun _ _ => StarForestCharge.last_star) h
    PEqualNP.Outside.L_meta_3243 PEqualNP.Outside.L_meta_3245

end IncidencePeeling
