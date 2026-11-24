import PEqualNP.Defs.MetaComplexityLgpMono
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sum
import Mathlib.Logic.Equiv.Fin.Basic

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Local3456.Forest

variable {n m : ℕ}

/-- Point vertices occupy the first input block and line vertices the second. -/
def incidenceGraph (I : Fin n → Fin m → Prop) : SimpleGraph (Fin (n+m)) :=
  SimpleGraph.fromRel (fun a b => ∃ p l, I p l ∧ a = Fin.castAdd m p ∧ b = Fin.natAdd n l)

private theorem apart (p : Fin n) (l : Fin m) : Fin.castAdd m p ≠ Fin.natAdd n l := by
  intro h
  have e := congrArg Fin.val h
  change p.val = n + l.val at e
  omega

private theorem adjacent {I : Fin n → Fin m → Prop} {p l} (h : I p l) :
    (incidenceGraph I).Adj (Fin.castAdd m p) (Fin.natAdd n l) :=
  ⟨apart p l,Or.inl ⟨p,l,h,rfl,rfl⟩⟩

private theorem incidence_iff (I : Fin n → Fin m → Prop) (x : Fin (n+m) → Bool) :
    (∃ a b, (incidenceGraph I).Adj a b ∧ x a = true ∧ x b = true) ↔
    ∃ p l, I p l ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true := by
  constructor
  · rintro ⟨a,b,h,ha,hb⟩
    rcases h.2 with ⟨p,l,hp,rfl,rfl⟩ | ⟨p,l,hp,rfl,rfl⟩
    · exact ⟨p,l,hp,ha,hb⟩
    · exact ⟨p,l,hp,hb,ha⟩
  · rintro ⟨p,l,h,hp,hl⟩
    exact ⟨_,_,adjacent h,hp,hl⟩

private def taggedEdge (e : Fin n × Fin m) : Sym2 (Fin (n+m)) :=
  s(Fin.castAdd m e.1,Fin.natAdd n e.2)

private theorem tagged_injective : Function.Injective (@taggedEdge n m) := by
  intro e f h
  rcases Sym2.eq_iff.mp h with ⟨hp,hl⟩ | ⟨h,_⟩
  · apply Prod.ext
    · exact Fin.ext (congrArg (fun i : Fin (n+m) => i.val) hp)
    · apply Fin.ext
      have v := congrArg Fin.val hl
      change n+e.2.val = n+f.2.val at v
      omega
  · exact (apart e.1 f.2 h).elim

/-- The only circuit lower bound used below; this is the statement of L-meta-104. -/
abbrev ForestLower := ∀ (r k s : ℕ) (G : SimpleGraph (Fin r)) [DecidableRel G.Adj],
  G.IsAcyclic → (∃ i j, G.Adj i j) →
  (∀ T : Finset (Fin r), (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) →
  HasCircuitSize r (fun x => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) s →
  G.edgeFinset.card + k ≤ s + 1

/-- On every bipartite forest, the original circuit pays for a minimum vertex cover
    and all edges, allowing the one saved OR gate on the first nonempty star. -/
theorem cover_budget (lower : ForestLower) (I : Fin n → Fin m → Prop) [DecidableRel I]
    (C : Circuit) (forest : (incidenceGraph I).IsAcyclic) (legal : FanInTwo C)
    (correct : ∀ z, circuitFun (n+m) C z = true ↔
      ∃ p l, I p l ∧ z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true) :
    let E := Finset.univ.filter (fun e : Fin n × Fin m => I e.1 e.2)
    ∃ (A : Finset (Fin n)) (B : Finset (Fin m)),
      (∀ e∈E, e.1 ∈ A ∨ e.2 ∈ B) ∧ E.card + A.card + B.card - 1 ≤ C.size := by
  classical
  let E := Finset.univ.filter (fun e : Fin n × Fin m => I e.1 e.2)
  change ∃ (A : Finset (Fin n)) (B : Finset (Fin m)), (∀ e∈E, e.1 ∈ A ∨ e.2 ∈ B) ∧ E.card + A.card + B.card - 1 ≤ C.size
  by_cases nonempty : E.Nonempty
  · let G := incidenceGraph I
    let cover (T : Finset (Fin (n+m))) := ∀ a b, G.Adj a b → a∈T ∨ b∈T
    have anyCover : ∃ k, ∃ T, cover T ∧ T.card = k :=
      ⟨_,Finset.univ,fun a _ _ => Or.inl (Finset.mem_univ a),rfl⟩
    obtain ⟨T,ht,cardT⟩ := Nat.find_spec anyCover
    have least (U) (hu : cover U) : T.card ≤ U.card := by
      rw [cardT]
      exact Nat.find_min' anyCover ⟨U,hu,rfl⟩
    obtain ⟨e,he⟩ := nonempty
    have edge : ∃ i j, G.Adj i j := ⟨_,_,adjacent (Finset.mem_filter.mp he).2⟩
    have computes : HasCircuitSize (n+m) (fun x => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) C.size := by
      refine ⟨C,legal,le_rfl,?_⟩
      intro x
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq]
      exact (correct x).trans (incidence_iff I x).symm
    have cost := lower (n+m) T.card C.size G forest edge least computes
    have included : E.image taggedEdge ⊆ G.edgeFinset := by
      intro e he
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
      exact SimpleGraph.mem_edgeFinset.mpr (G.mem_edgeSet.mpr (adjacent (Finset.mem_filter.mp hi).2))
    have edges := Finset.card_le_card included
    rw [Finset.card_image_of_injective _ tagged_injective] at edges
    let equiv : Fin n ⊕ Fin m ≃ Fin (n+m) := finSumFinEquiv
    let split := T.map equiv.symm.toEmbedding
    refine ⟨split.toLeft, split.toRight,?_,?_⟩
    · intro i hi
      have ends := ht _ _ (adjacent (Finset.mem_filter.mp hi).2)
      rcases ends with h | h
      · exact Or.inl (Finset.mem_toLeft.mpr (Finset.mem_map_equiv.mpr h))
      · exact Or.inr (Finset.mem_toRight.mpr (Finset.mem_map_equiv.mpr h))
    · have parts : split.toLeft.card + split.toRight.card = T.card := by
        rw [Finset.card_toLeft_add_card_toRight,Finset.card_map]
      omega
  · have empty : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp nonempty
    exact ⟨∅,∅,by simp [empty],by simp [empty]⟩

end PEqualNP.Local3456.Forest
