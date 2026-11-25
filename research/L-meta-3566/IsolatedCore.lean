import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.PermInputs

namespace VertexPeel.IsolatedCore

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.MetaComplexity.Helpers.PermInputs

/-- A graph retraction transports every Monotone2 circuit to the retract at the same size. -/
theorem retract_circuit {m n : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj]
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (f : H ↪g G) (r : Fin n → Fin m)
    (fixes : ∀ i, r (f i) = i) (hom : ∀ a b, G.Adj a b → H.Adj (r a) (r b))
    (C : Circuit) (mono : Monotone2 C) (ok : circuitFun n C = graphFun G ∅) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun m D = graphFun H ∅ ∧ D.size = C.size := by
  refine ⟨relabel n m r C,?_,?_,by simp [relabel,Circuit.size]⟩
  · intro g hg
    obtain ⟨g0,mem,rfl⟩ := List.mem_map.mp hg
    obtain ⟨op,arity⟩ := mono g0 mem
    exact ⟨op,by simpa [relGate] using arity⟩
  · funext x
    have sim : circuitFun m (relabel n m r C) x = circuitFun n C (x ∘ r) :=
      (rel_fold n m r C.gates _ _ (rel_init n m r x)).2.2 C.output
    rw [sim,ok]
    have iffEdge : (∃ a b, G.Adj a b ∧ x (r a) = true ∧ x (r b) = true) ↔
        ∃ a b, H.Adj a b ∧ x a = true ∧ x b = true := by
      constructor
      · rintro ⟨a,b,ab,ha,hb⟩
        exact ⟨r a,r b,hom a b ab,ha,hb⟩
      · rintro ⟨a,b,ab,ha,hb⟩
        exact ⟨f a,f b,f.map_rel_iff.mpr ab,by simpa [fixes] using ha,by simpa [fixes] using hb⟩
    simp [graphFun,iffEdge]

/-- An induced core containing every non-isolated vertex inherits the whole graph's circuit budget. -/
theorem core_lower {m n : ℕ} [Nonempty (Fin m)] (H : SimpleGraph (Fin m)) [DecidableRel H.Adj]
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (f : H ↪g G)
    (active : ∀ a b, G.Adj a b → a ∈ Set.range f ∧ b ∈ Set.range f)
    {s : ℕ} (lower : ∀ D : Circuit, Monotone2 D → circuitFun m D = graphFun H ∅ → s ≤ D.size)
    (C : Circuit) (mono : Monotone2 C) (ok : circuitFun n C = graphFun G ∅) : s ≤ C.size := by
  classical
  let r := Function.invFun f
  have left : Function.LeftInverse r f := Function.leftInverse_invFun f.injective
  have hom : ∀ a b, G.Adj a b → H.Adj (r a) (r b) := by
    intro a b ab
    obtain ⟨⟨i,rfl⟩,⟨j,rfl⟩⟩ := active a b ab
    rw [left,left]
    exact f.map_rel_iff.mp ab
  obtain ⟨D,dm,dc,size⟩ := retract_circuit H G f r left hom C mono ok
  exact size ▸ lower D dm dc

end VertexPeel.IsolatedCore
