import PEqualNP.Outside.L_meta_1660

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace StarForestCharge

variable {n m : ℕ}

abbrev Edge (n m : ℕ) := Fin n × Fin m
abbrev Vertex (n m : ℕ) := Fin n ⊕ Fin m

def Touches (e : Edge n m) (v : Vertex n m) : Prop :=
  v = Sum.inl e.1 ∨ v = Sum.inr e.2

noncomputable def active (E : Finset (Edge n m)) : Finset (Vertex n m) := by
  classical exact Finset.univ.filter fun v => ∃ e ∈ E, Touches e v

lemma mem_active {E : Finset (Edge n m)} {v : Vertex n m} :
    v ∈ active E ↔ ∃ e ∈ E, Touches e v := by classical simp [active]

/-- Each nonisolated endpoint is essential. Binary circuits have at most one more
    essential input than gates, even when unused wires and unrestricted fanout occur. -/
theorem active_budget (E : Finset (Edge n m)) (C : Circuit)
    (fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (correct : ∀ z, circuitFun (n+m) C z = decide (∃ p l, (p,l) ∈ E ∧
      z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) :
    (active E).card ≤ C.size + 1 := by
  classical
  obtain ⟨Sup, dep, bound⟩ := PEqualNP.Outside.L_meta_1660.fold_sup (n+m) C.gates fan
    _ (n+m) _ 0 (PEqualNP.Outside.L_meta_1660.st_init _) (fun Q => by
      have h := Finset.card_biUnion_le_card_mul Q _ 1
        (fun a _ => PEqualNP.Outside.L_meta_1660.sup0_card (n+m) a)
      omega)
  have outBound := bound {C.output}
  rw [Finset.singleton_biUnion, Finset.card_singleton] at outBound
  have apart (p : Fin n) (l : Fin m) : Fin.castAdd m p ≠ Fin.natAdd n l := by
    intro h
    have hv := congrArg Fin.val h
    change p.val = n + l.val at hv
    omega
  have touchSup (e : Edge n m) (he : e ∈ E) :
      Fin.castAdd m e.1 ∈ Sup C.output ∧ Fin.natAdd n e.2 ∈ Sup C.output := by
    let x (i : Fin (n+m)) := decide (i = Fin.castAdd m e.1 ∨ i = Fin.natAdd n e.2)
    have yes : circuitFun (n+m) C x = true := by
      rw [correct, decide_eq_true_eq]
      exact ⟨e.1,e.2,he,by simp [x],by simp [x]⟩
    constructor
    · by_contra hn
      let y (i : Fin (n+m)) := decide (i = Fin.natAdd n e.2)
      have no : circuitFun (n+m) C y = false := by simp [correct, y, apart]
      have eq : circuitFun (n+m) C x = circuitFun (n+m) C y := dep C.output x y (by
        intro j hj
        have hja : j ≠ Fin.castAdd m e.1 := fun h => hn (h ▸ hj)
        simp [x, y, hja])
      simp [yes, no] at eq
    · by_contra hn
      let y (i : Fin (n+m)) := decide (i = Fin.castAdd m e.1)
      have no : circuitFun (n+m) C y = false := by simp [correct, y, Ne.symm (apart _ _)]
      have eq : circuitFun (n+m) C x = circuitFun (n+m) C y := dep C.output x y (by
        intro j hj
        have hjb : j ≠ Fin.natAdd n e.2 := fun h => hn (h ▸ hj)
        simp [x, y, hjb])
      simp [yes, no] at eq
  have inc : (active E).map finSumFinEquiv.toEmbedding ⊆ Sup C.output := by
    intro i hi
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨e, he, hl | hr⟩ := mem_active.mp hv
    · subst v
      exact (touchSup e he).1
    · subst v
      exact (touchSup e he).2
  have card := Finset.card_le_card inc
  rw [Finset.card_map] at card
  change (active E).card ≤ C.gates.length + 1
  omega

/-- Each edge has an endpoint incident to no other edge. This is the intrinsic
    star-forest condition, with either choice of center on isolated edges. -/
def StarForest (E : Finset (Edge n m)) : Prop :=
  ∀ e ∈ E, (∀ f ∈ E, f.1 = e.1 → f = e) ∨ (∀ f ∈ E, f.2 = e.2 → f = e)

/-- Charge all edges to distinct leaves, then charge each matching edge to its center. -/
theorem edge_matching_le_active (E M : Finset (Edge n m)) (stars : StarForest E)
    (sub : M ⊆ E)
    (first : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (second : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) :
    E.card + M.card ≤ (active E).card := by
  classical
  let privateLeft (e : Edge n m) := ∀ f ∈ E, f.1 = e.1 → f = e
  let leaf (e : Edge n m) : Vertex n m := if privateLeft e then .inl e.1 else .inr e.2
  let center (e : Edge n m) : Vertex n m := if privateLeft e then .inr e.2 else .inl e.1
  have leafEnd (e) : Touches e (leaf e) := by by_cases h : privateLeft e <;> simp [Touches, leaf, h]
  have centerEnd (e) : Touches e (center e) := by by_cases h : privateLeft e <;> simp [Touches, center, h]
  have apart (e) : leaf e ≠ center e := by by_cases h : privateLeft e <;> simp [leaf, center, h]
  have uniqueLeaf (e) (he : e ∈ E) (f) (hf : f ∈ E) (hit : Touches f (leaf e)) : f = e := by
    by_cases h : privateLeft e
    · apply h f hf
      simpa [Touches,leaf,h,eq_comm] using hit
    · apply ((stars e he).resolve_left h) f hf
      simpa [Touches,leaf,h,eq_comm] using hit
  let code : E ⊕ M → active E := Sum.elim
    (fun e => ⟨leaf e.val, mem_active.mpr ⟨e.val,e.property,leafEnd e.val⟩⟩)
    (fun e => ⟨center e.val, mem_active.mpr ⟨e.val,sub e.property,centerEnd e.val⟩⟩)
  have separated (e : E) (f : M) : leaf e.val ≠ center f.val := by
    intro h
    have eq := uniqueLeaf e.val e.property f.val (sub f.property) (h.symm ▸ centerEnd f.val)
    exact apart e.val (eq ▸ h)
  have inj : Function.Injective code := by
    intro i j h
    have eq := congrArg Subtype.val h
    cases i with
    | inl e =>
      cases j with
      | inl f =>
        change leaf e.val = leaf f.val at eq
        exact congrArg Sum.inl (Subtype.ext (uniqueLeaf e.val e.property f.val f.property
          (eq.symm ▸ leafEnd f.val)).symm)
      | inr f => exact False.elim (separated e f eq)
    | inr e =>
      cases j with
      | inl f => exact False.elim (separated f e eq.symm)
      | inr f =>
        change center e.val = center f.val at eq
        apply congrArg Sum.inr
        apply Subtype.ext
        by_cases h₁ : privateLeft e.val <;> by_cases h₂ : privateLeft f.val <;>
          simp [center,h₁,h₂] at eq
        · exact second _ e.property _ f.property eq
        · exact first _ e.property _ f.property eq
  simpa using Fintype.card_le_of_injective code inj

/-- The complete matching charge required by R-meta-2685-41 for all star forests. -/
theorem star_forest_charge (E M : Finset (Edge n m)) (C : Circuit)
    (stars : StarForest E) (ao : PEqualNP.TopForm.IsAO2 (n+m) C)
    (correct : ∀ z, circuitFun (n+m) C z = decide (∃ p l, (p,l) ∈ E ∧
      z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true))
    (sub : M ⊆ E) (first : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (second : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) :
    E.card + M.card ≤ C.size + 1 :=
  (edge_matching_le_active E M stars sub first second).trans
    (active_budget E C (fun g hg => le_of_eq (ao.2.2 g hg)) correct)

/-- A final nonempty point-star or line-star pays its entire edge count. -/
theorem last_star (E : Finset (Edge n m)) (C : Circuit) (hn : E.Nonempty)
    (star : (∃ p, ∀ e ∈ E, e.1 = p) ∨ (∃ l, ∀ e ∈ E, e.2 = l))
    (ao : PEqualNP.TopForm.IsAO2 (n+m) C)
    (correct : circuitFun (n+m) C = PEqualNP.ReadTwo.fpl n (fun p l => (p,l) ∈ E)) :
    E.card ≤ C.size := by
  obtain ⟨e, he⟩ := hn
  have forest : StarForest E := by
    intro f hf
    rcases star with ⟨p,h⟩ | ⟨l,h⟩
    · exact Or.inr (fun g hg right => Prod.ext ((h g hg).trans (h f hf).symm) right)
    · exact Or.inl (fun g hg left => Prod.ext left ((h g hg).trans (h f hf).symm))
  have h := star_forest_charge E {e} C forest ao (fun z => congrFun correct z)
    (by simpa) (by simp) (by simp)
  simpa using h

end StarForestCharge
