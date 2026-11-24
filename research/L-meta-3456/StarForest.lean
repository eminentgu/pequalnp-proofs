import ReadOnce

namespace SingletonFiniteFormula.Formula

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

variable {α β : Type}

def joinMany (f : β → Formula α) : β → List β → Formula α
  | a, [] => f a
  | a, b :: bs => .node .join (f a) (joinMany f b bs)

theorem vars_joinMany (f : β → Formula α) (a : β) (bs : List β) :
    (joinMany f a bs).varList = (a :: bs).flatMap (fun b => (f b).varList) := by
  induction bs generalizing a with
  | nil => simp [joinMany]
  | cons b bs ih => simp [joinMany, varList, ih]

theorem eval_joinMany (f : β → Formula α) (z : α → Bool) (a : β) (bs : List β) :
    (joinMany f a bs).eval z = true ↔ ∃ b ∈ a :: bs, (f b).eval z = true := by
  induction bs generalizing a with
  | nil => simp [joinMany]
  | cons b bs ih =>
    simp only [joinMany, eval, Op.apply, Bool.or_eq_true, ih]
    simp

structure Star (α : Type) where
  center : α
  first : α
  more : List α

def Star.neighbors (s : Star α) := s.first :: s.more

def Star.formula (s : Star α) : Formula α :=
  .node .meet (.atom s.center) (joinMany Formula.atom s.first s.more)

def Star.variables (s : Star α) := s.center :: s.neighbors

theorem Star.vars_formula (s : Star α) : s.formula.varList = s.variables := by
  simp [Star.formula, Star.variables, Star.neighbors, varList, vars_joinMany]

theorem Star.eval_formula (s : Star α) (z : α → Bool) :
    s.formula.eval z = true ↔ z s.center = true ∧ ∃ k ∈ s.neighbors, z k = true := by
  simp [Star.formula, Star.neighbors, eval, Op.apply, eval_joinMany]

def forest (s : Star α) (ss : List (Star α)) := joinMany Star.formula s ss

theorem forest_vars (s : Star α) (ss : List (Star α)) :
    (forest s ss).varList = (s :: ss).flatMap Star.variables := by
  simp [forest, vars_joinMany, Star.vars_formula]

theorem forest_eval (s : Star α) (ss : List (Star α)) (z : α → Bool) :
    (forest s ss).eval z = true ↔
      ∃ t ∈ s :: ss, z t.center = true ∧ ∃ k ∈ t.neighbors, z k = true := by
  simp only [forest, eval_joinMany, Star.eval_formula]

def Endpoints {N : Nat} (u v : Fin (N+N)) (p l : Fin N) : Prop :=
  (u = Fin.castAdd N p ∧ v = Fin.natAdd N l) ∨ (v = Fin.castAdd N p ∧ u = Fin.natAdd N l)

/-- Each listed spoke is a graph edge and each edge is one of the listed spokes.
    A center may be on either side of the bipartition. -/
structure Presents {N : Nat} (ss : List (Star (Fin (N+N)))) (I : Fin N → Fin N → Prop) : Prop where
  sound : ∀ t ∈ ss, ∀ k ∈ t.neighbors, ∃ p l, I p l ∧ Endpoints t.center k p l
  complete : ∀ p l, I p l → ∃ t ∈ ss, ∃ k ∈ t.neighbors, Endpoints t.center k p l

theorem forest_incidence {N : Nat} {s : Star (Fin (N+N))} {ss : List (Star (Fin (N+N)))}
    {I : Fin N → Fin N → Prop} (pres : Presents (s::ss) I) (z : Fin (N+N) → Bool) :
    (forest s ss).eval z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
  rw [forest_eval]
  constructor
  · rintro ⟨t, ht, hu, k, hk, hv⟩
    obtain ⟨p,l,hi,pair⟩ := pres.sound t ht k hk
    refine ⟨p,l,hi,?_⟩
    rcases pair with ⟨hp,hl⟩ | ⟨hp,hl⟩
    · exact ⟨hp ▸ hu,hl ▸ hv⟩
    · exact ⟨hp ▸ hv,hl ▸ hu⟩
  · rintro ⟨p,l,hi,hp,hl⟩
    obtain ⟨t,ht,k,hk,pair⟩ := pres.complete p l hi
    rcases pair with ⟨ep,el⟩ | ⟨ep,el⟩
    · exact ⟨t,ht,ep.symm ▸ hp,k,hk,el.symm ▸ hl⟩
    · exact ⟨t,ht,el.symm ▸ hl,k,hk,ep.symm ▸ hp⟩

/-- The circuit promised by L-meta-3456, with its original size and singleton conditions. -/
def IncidenceNormalizes {N : Nat} (I : Fin N → Fin N → Prop) (C : Circuit) : Prop :=
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size ≤ C.size ∧
      (∀ z : Fin (N+N) → Bool, circuitFun (N+N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      ∀ j < D.gates.length, (gateAt D j).op = .and →
        (∀ p : Fin N, (D.wires (List.ofFn (fun i : Fin (N+N) =>
          decide (i = Fin.castAdd N p)))).getD (N+N+j) false = false) ∧
        ∀ l : Fin N, (D.wires (List.ofFn (fun i : Fin (N+N) =>
          decide (i = Fin.natAdd N l)))).getD (N+N+j) false = false

/-- Exact L-meta-3456 conclusion for a disjoint nonempty family of nonempty stars. -/
theorem normalize_star_forest {N : Nat} (I : Fin N → Fin N → Prop) (C : Circuit)
    (s : Star (Fin (N+N))) (ss : List (Star (Fin (N+N))))
    (disjoint : ((s::ss).flatMap Star.variables).Nodup)
    (pres : Presents (s::ss) I) (mono : Monotone2 C)
    (he : ∀ z : Fin (N+N) → Bool, circuitFun (N+N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    IncidenceNormalizes I C := by
  have eq (z : Fin (N+N) → Bool) : (forest s ss).eval z = circuitFun (N+N) C z := by
    have h := (forest_incidence pres z).trans (he z).symm
    cases a : (forest s ss).eval z <;> cases b : circuitFun (N+N) C z <;> simp_all
  apply incidence_of_formula N I C _ he
  exact ⟨forest s ss, readOnce_optimal C _ mono ((forest_vars s ss).symm ▸ disjoint) eq, eq⟩

/-- A star forest is given by its disjoint stars. Vertices missing from the presentation
    are isolated. The empty list presents precisely the edgeless graph. -/
def IsStarForest {N : Nat} (I : Fin N → Fin N → Prop) : Prop :=
  ∃ stars : List (Star (Fin (N+N))),
    (stars.flatMap Star.variables).Nodup ∧ Presents stars I

theorem normalize_edgeless {N : Nat} (I : Fin N → Fin N → Prop) (C : Circuit)
    (hempty : ∀ p l, ¬ I p l) : IncidenceNormalizes I C := by
  let D : Circuit := ⟨[], N+N⟩
  refine ⟨D, ?_, ?_, ?_, ?_, ?_⟩
  · simp [D, Monotone2]
  · simp [D, ReadsBack]
  · simp [D, Circuit.size]
  · intro z
    simp [D, circuitFun, Circuit.eval, Circuit.wires, hempty]
  · simp [D]

/-- Covers every finite disjoint union of bipartite stars, including zero stars. -/
theorem normalize_of_star_forest {N : Nat} (I : Fin N → Fin N → Prop) (C : Circuit)
    (hs : IsStarForest I) (mono : Monotone2 C)
    (he : ∀ z : Fin (N+N) → Bool, circuitFun (N+N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    IncidenceNormalizes I C := by
  obtain ⟨stars,nd,pres⟩ := hs
  cases stars with
  | nil =>
    apply normalize_edgeless
    intro p l h
    obtain ⟨t,ht,_⟩ := pres.complete p l h
    simp at ht
  | cons s ss => exact normalize_star_forest I C s ss nd pres mono he

end SingletonFiniteFormula.Formula
