import FinalAccounting

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadK

namespace Incidence2990

/-- The output-bound premise of L-meta-2990 is unnecessary for this implication. -/
private theorem canonicalAO {N : ℕ} {C : Circuit} (mono : Monotone2 C)
    (ordered : ∀ j g, C.gates[j]? = some g →
      ∃ a b, g.inputs=[a,b] ∧ a<b ∧ b<N+N+j) : IsAO2 (N+N) C := by
  have row (j : ℕ) (hj : j < C.gates.length) :
      ∃ a b, (gateAt C j).inputs=[a,b] ∧ a<b ∧ b<N+N+j := by
    apply ordered j _
    simp [gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
  refine ⟨fun g hg => (mono g hg).1,?_,?_⟩
  · intro j hj k hk
    obtain ⟨a,b,e,ab,lim⟩ := row j hj
    rw [e] at hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl <;> omega
  · intro g hg
    obtain ⟨j,eq⟩ := List.mem_iff_get.mp hg
    obtain ⟨a,b,e,_,_⟩ := row j j.isLt
    have here : gateAt C j = g := by simpa [gateAt,List.getD_eq_getElem _ _ j.isLt] using eq
    rw [← here,e]
    rfl

/-- Under the desk's sparse soundness and ordered fan-in hypotheses, measure
    how many incident point/line pairs admit no proof with two reads per input. -/
theorem lossBound (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 2 ≤ q)
    (lines : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1)
    (unique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (mono : Monotone2 C)
    (ordered : ∀ j g, C.gates[j]? = some g →
      ∃ a b, g.inputs=[a,b] ∧ a<b ∧ b<N+N+j)
    (sound : ∀ z : Fin (N+N) → Bool,
      Fintype.card {l : Fin N // z (Fin.natAdd N l)=true} ≤ q →
      (¬∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p)=true ∧ z (Fin.natAdd N l)=true) →
      circuitFun (N+N) C z=false) :
    N*(q+1) ≤ 50*C.size + 2*N + (heavy I C).card := by
  apply accounting q N I C (fun l => by simpa only [Fintype.card_subtype] using lines l)
    unique (canonicalAO mono ordered)
  intro z _ atMostTwo noEdge
  apply sound z _ noEdge
  simpa only [Fintype.card_subtype] using atMostTwo.trans hq

/-- A violation of the claimed gate bound forces strictly more than 99/200
    of all N(q+1) incident flags to fail the local read-2 test. -/
theorem hardDensity {q N size hard : ℕ} (large : 300 ≤ q)
    (count : N*(q+1) ≤ 50*size + 2*N + hard) (small : 100*size < N*q) :
    N*q < 2*hard + 2*N ∧ 99*(N*(q+1)) < 200*hard := by
  have mul : N*300 ≤ N*q := Nat.mul_le_mul_left N large
  rw [Nat.mul_add,Nat.mul_one] at count ⊢
  omega

end Incidence2990

#print axioms Incidence2990.lossBound
#print axioms Incidence2990.hardDensity
