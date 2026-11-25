import SidePeel

namespace VertexPeel.PendantCross
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
    PEqualNP.TopForm PEqualNP.ReadTwo
open ZeroFold SideReaders SidePeel

/-- A differing output outside a cut has a differing gate outside the cut
    with a raw or computed operand inside it. -/
theorem crosses_diff (C : Circuit) (ao : IsAO2 n C) (X : Finset ℕ) (x y : Fin n → Bool)
    (agree : ∀ a : Fin n, a.val ∉ X → x a = y a)
    (diff : wval C x C.output ≠ wval C y C.output) (outside : C.output ∉ X) :
    ∃ j, ∃ hj : j < C.gates.length, n+j ∉ X ∧ wval C x (n+j) ≠ wval C y (n+j) ∧
      ∃ t ∈ X, t ∈ C.gates[j].inputs := by
  classical
  by_contra! never
  have ok : ∀ w : ℕ, w ∉ X → wval C x w = wval C y w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hx
      by_cases raw : w < n
      · exact (wval_in C x ⟨w,raw⟩).trans ((agree ⟨w,raw⟩ hx).trans (wval_in C y ⟨w,raw⟩).symm)
      by_cases past : n + C.gates.length ≤ w
      · rw [wval_past C x w past,wval_past C y w past]
      obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
      have hj : j < C.gates.length := by omega
      by_contra differ
      obtain ⟨a,b,hab,ha,hb,_⟩ := two n C ao j hj
      have ex (t : ℕ) (ht : t ∈ C.gates[j].inputs) : t ∉ X := fun e => never j hj hx differ t e ht
      apply differ
      rw [wval_gate C x j a b hj hab ha hb,wval_gate C y j a b hj hab ha hb,
        ih a ha (ex a (by simp [hab])),ih b hb (ex b (by simp [hab]))]
  exact diff (ok _ outside)

def Reads (C : Circuit) (j w : ℕ) : Prop := ∃ hj : j < C.gates.length, w ∈ C.gates[j].inputs

theorem raw_reader (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (ao : IsAO2 n C)
    (cor : circuitFun n C = graphFun G ∅) (a b : Fin n) (ab : G.Adj a b) : ∃ j, Reads C j a.val := by
  obtain ⟨x,y,eq,diff⟩ := sensitive G C cor ab.symm
  obtain ⟨j,hj,_,t,ht,read⟩ := crosses C ao {a.val} x y
    (fun u hu => eq u (by rintro rfl; simp at hu)) diff (by simpa using no_raw_output G cor a)
  exact ⟨j,hj,Finset.mem_singleton.mp ht ▸ read⟩

/-- If a gate reads both coordinates of a pendant edge, another gate also
    reads at least one of them. The pair {b,c} is an edge and {a,c} is not,
    whereas either binary operation at the shared gate is symmetric. -/
theorem other_reader (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (ao : IsAO2 n C)
    (cor : circuitFun n C = graphFun G ∅) {a b c : Fin n} (ab : G.Adj a b)
    (ac : ¬G.Adj a c) (bc : G.Adj b c) (ca : c ≠ a)
    {j : ℕ} (ja : Reads C j a.val) (jb : Reads C j b.val) :
    ∃ l, l ≠ j ∧ (Reads C l a.val ∨ Reads C l b.val) := by
  classical
  let x := bits {a,c}
  let y := bits {b,c}
  have diff : wval C x C.output ≠ wval C y C.output := by
    change circuitFun n C _ ≠ circuitFun n C _
    rw [cor]
    intro eq
    exact ac ((pair_iff G a c).mp (eq.trans ((pair_iff G b c).mpr bc)))
  obtain ⟨l,hl,_,different,t,ht,read⟩ := crosses_diff C ao {a.val,b.val} x y (by
    intro u hu
    have hu' : u.val ≠ a.val ∧ u.val ≠ b.val := by simpa [not_or] using hu
    have ua : u ≠ a := fun e => hu'.1 (congrArg Fin.val e)
    have ub : u ≠ b := fun e => hu'.2 (congrArg Fin.val e)
    simp [x,y,bits,ua,ub]) diff (by simp [no_raw_output G cor a,no_raw_output G cor b])
  refine ⟨l,?_,?_⟩
  · rintro rfl
    obtain ⟨u,v,ports,hu,hv,op⟩ := two n C ao l hl
    have aa : a.val = u ∨ a.val = v := by simpa [ports] using ja.choose_spec
    have bb : b.val = u ∨ b.val = v := by simpa [ports] using jb.choose_spec
    have ne : a.val ≠ b.val := fun e => ab.ne (Fin.ext e)
    apply different
    rw [wval_gate C x l u v hl ports hu hv,wval_gate C y l u v hl ports hu hv]
    rcases aa with e | e <;> rcases bb with d | d
    · exact (ne (e.trans d.symm)).elim
    · rw [← e,← d,wval_in,wval_in,wval_in,wval_in]
      rcases op with o | o <;> simp [o,GateOp.eval,x,y,bits,ab.ne,ab.ne.symm,bc.ne,ca.symm]
    · rw [← d,← e,wval_in,wval_in,wval_in,wval_in]
      rcases op with o | o <;> simp [o,GateOp.eval,x,y,bits,ab.ne,ab.ne.symm,bc.ne,ca.symm]
    · exact (ne (e.trans d.symm)).elim
  · rcases Finset.mem_insert.mp ht with e | e
    · exact Or.inl ⟨hl,e ▸ read⟩
    · exact Or.inr ⟨hl,Finset.mem_singleton.mp e ▸ read⟩

end VertexPeel.PendantCross
