import CountReaders
import PendantPathPeel

namespace VertexPeel.PendantObstruction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadTwo
open SideReaders SidePeel PendantCross ThreeGatePeel CountReaders CoverCircuit

/-- The globally quantified conclusion at the specified vertex. -/
abbrev PeelsAt (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (z : Fin n) : Prop :=
  ∀ E : Circuit, IsAO2 n E → circuitFun n E = graphFun G ∅ → SavesAt G z E

private theorem from_two (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : Fin n)
    (leaf : G.degree a=1) (C : Circuit) (least : IsLeastAO G C) {j k : ℕ}
    (hj : j < C.size) (hk : k < C.size) (kj : k ≠ j)
    (nj : ¬ZeroFold.Mg C {a} j) (nk : ¬ZeroFold.Mg C {a} k) : PeelsAt G a := by
  classical
  let S := (Finset.range C.size).filter (ZeroFold.Mg C {a})
  have sub : insert k (insert j S) ⊆ Finset.range C.size := by
    intro i hi
    rcases Finset.mem_insert.mp hi with e | h
    · exact e ▸ Finset.mem_range.mpr hk
    rcases Finset.mem_insert.mp h with e | h
    · exact e ▸ Finset.mem_range.mpr hj
    exact (Finset.mem_filter.mp h).1
  have bound := Finset.card_le_card sub
  simp [S,kj,nk,nj] at bound
  obtain ⟨D,dao,dc,ds⟩ := ZeroFold.compile C least.1 {a}
  intro E eao ec
  have le := least.2.2 E eao ec
  exact ⟨D,dao,dc.trans (restrict_correct G C least.2.1 a),by omega,fun _ => by omega⟩

/-- Either a particular leaf already gives the full saving, or every minimum
    circuit reads it at precisely one gate, an OR not reading its neighbor. -/
theorem leaf_reader (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {a b : Fin n}
    (ab : G.Adj a b) (leaf : G.degree a=1) (remaining : ∃ u v, G.Adj u v ∧ u≠a ∧ v≠a)
    (C : Circuit) (least : IsLeastAO G C) :
    PeelsAt G a ∨ ∃ g, ∃ ag : Reads C g a.val, (C.gates[g]'ag.choose).op = .or ∧
      (∀ k, Reads C k a.val → k=g) ∧ ¬Reads C g b.val := by
  classical
  obtain ⟨g,ag⟩ := raw_reader G C least.1 least.2.1 a b ab
  have zero := ZeroFold.fv_in0 C {a} a (by simp)
  have ng := ZeroFold.kill C least.1 {a} g ag.choose a.val ag.choose_spec zero
  by_cases uniq : ∀ k, Reads C k a.val → k=g
  · obtain ⟨u,v,ports,hu,hv,op⟩ := ZeroFold.two n C least.1 g ag.choose
    rcases op with op | op
    · have gz : ZeroFold.fv C {a} (n+g) = fun _ => false := by
        funext x
        rw [ZeroFold.fv_and C {a} g u v ag.choose ports hu hv op]
        have ar : a.val=u ∨ a.val=v := by simpa [ports] using ag.choose_spec
        rcases ar with e | e <;> rw [← e,zero] <;> simp
      obtain ⟨k,hk,kne,nk⟩ := second_of_zero G C least.1 least.2.1 a b ab.symm remaining g ag.choose gz
      exact Or.inl (from_two G a leaf C least ag.choose hk kne ng nk)
    · exact Or.inr ⟨g,ag,op,uniq,separate G C least.1 least.2.1 ab ag op uniq⟩
  · push Not at uniq
    obtain ⟨k,ak,kg⟩ := uniq
    exact Or.inl (from_two G a leaf C least ag.choose ak.choose kg ng
      (ZeroFold.kill C least.1 {a} k ak.choose a.val ak.choose_spec zero))

/-- For any fixed minimum circuit, at least one of the following holds:
    the leaf satisfies the deletion card for all circuits, its neighbor does,
    or the minimum circuit has the indicated restricted reader pattern. -/
theorem peel_or_few_readers (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {a b : Fin n}
    (ab : G.Adj a b) (leaf : G.degree a=1)
    (other : ∃ c, G.Adj b c ∧ c≠a) (remaining : ∃ u v, G.Adj u v ∧ u≠b ∧ v≠b)
    (C : Circuit) (least : IsLeastAO G C) :
    PeelsAt G a ∨ PeelsAt G b ∨
      ∃ g, ∃ ag : Reads C g a.val, (C.gates[g]'ag.choose).op = .or ∧
        (∀ k, Reads C k a.val → k=g) ∧ ¬Reads C g b.val ∧ (readers C b.val).card+2 ≤ G.degree b := by
  classical
  obtain ⟨c,bc,ca⟩ := other
  rcases leaf_reader G ab leaf ⟨b,c,bc,ab.ne.symm,ca⟩ C least with peel | ⟨g,ag,op,uniq,ng⟩
  · exact Or.inl peel
  right
  by_cases few : (readers C b.val).card+2 ≤ G.degree b
  · exact Or.inr ⟨g,ag,op,uniq,ng,few⟩
  left
  have only (t : Fin n) (h : G.Adj a t) : t=b := by
    have one : (G.neighborFinset a).card ≤ 1 := by simpa using leaf.le
    exact Finset.card_le_one.mp one t ((G.mem_neighborFinset _ _).mpr h)
      b ((G.mem_neighborFinset _ _).mpr ab)
  obtain ⟨D,dao,dc,ds⟩ := cut_joint_readers G C least.1 least.2.1 ab only remaining ag op uniq
  intro E eao ec
  have le := least.2.2 E eao ec
  refine ⟨D,dao,dc.trans ?_,by omega,fun _ => by omega⟩
  funext x
  simp [graphFun,SimpleGraph.deleteIncidenceSet]

end VertexPeel.PendantObstruction

#print axioms VertexPeel.PendantObstruction.peel_or_few_readers
