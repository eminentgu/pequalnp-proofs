import ThreeGatePeel

namespace VertexPeel.CountReaders
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadTwo
open MixedFold SideReaders SidePeel PendantCross ThreeGatePeel

noncomputable def readers (C : Circuit) (w : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range C.size).filter fun i => Reads C i w

theorem mem_readers (C : Circuit) (w i : ℕ) : i ∈ readers C w ↔ Reads C i w := by
  classical
  simp only [readers,Finset.mem_filter,Finset.mem_range]
  exact ⟨And.right,fun h => ⟨h.choose,h⟩⟩

/-- If a leaf has a unique OR reader, this gate cannot also read its neighbor:
    the output distinguishes the neighbor alone from the adjacent pair. -/
theorem separate (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (ao : IsAO2 n C)
    (cor : circuitFun n C = graphFun G ∅) {a b : Fin n} (edge : G.Adj a b)
    {g : ℕ} (ag : Reads C g a.val) (o : (C.gates[g]'ag.choose).op = .or)
    (uniq : ∀ k, Reads C k a.val → k = g) : ¬Reads C g b.val := by
  intro bg
  let x := bits {a,b}
  let y := bits {b,b}
  have diff : wval C x C.output ≠ wval C y C.output := by
    change circuitFun n C _ ≠ circuitFun n C _
    rw [cor]
    intro h
    exact G.loopless.irrefl b ((pair_iff G b b).mp (h.symm.trans ((pair_iff G a b).mpr edge)))
  obtain ⟨k,hk,_,dk,t,ht,read⟩ := crosses_diff C ao {a.val} x y (by
    intro s hs
    have sa : s≠a := by rintro rfl; simp at hs
    simp [x,y,bits,sa]) diff (by simpa using no_raw_output G cor a)
  obtain rfl : k=g := uniq k ⟨hk,Finset.mem_singleton.mp ht ▸ read⟩
  obtain ⟨u,v,ports,hu,hv,_⟩ := ZeroFold.two n C ao k hk
  have pos : b.val = u ∨ b.val = v := by simpa [ports] using bg.choose_spec
  apply dk
  rw [ZeroFold.wval_gate C x k u v hk ports hu hv,ZeroFold.wval_gate C y k u v hk ports hu hv,o]
  rcases pos with e | e <;> rw [← e,ZeroFold.wval_in,ZeroFold.wval_in] <;> simp [x,y,bits,GateOp.eval]

/-- At a pendant edge with singly OR-read leaf a, setting b=0 and a=1 omits
    every direct reader of b plus at least two further gates. -/
theorem cut_joint_readers (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (ao : IsAO2 n C) (cor : circuitFun n C = graphFun G ∅) {a b : Fin n}
    (ab : G.Adj a b) (only : ∀ t, G.Adj a t → t=b)
    (remaining : ∃ u v, G.Adj u v ∧ u≠b ∧ v≠b) {g : ℕ} (ag : Reads C g a.val)
    (o : (C.gates[g]'ag.choose).op = .or) (uniq : ∀ k, Reads C k a.val → k = g) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun (G.deleteIncidenceSet b) ∅ ∧
      D.size + (readers C b.val).card + 2 ≤ C.size := by
  classical
  let r := assign a b true
  have ra : val C r a.val = fun _ => true := raw_a C ab.ne true
  have cb : Const (val C r b.val) := ⟨_,raw_b C _ _ _⟩
  have cg : Const (val C r (n+g)) :=
    canal C ao r ag.choose ag.choose_spec (by simpa [o] using ra)
  let B := readers C b.val
  let S := B.filter fun i => Const (val C r (n+i))
  let X := insert a.val (insert (n+g) (S.image (n+·)))
  have Xconst (t : ℕ) (hx : t ∈ X) : Const (val C r t) := by
    rcases Finset.mem_insert.mp hx with e | hh
    · exact e ▸ ⟨_,ra⟩
    rcases Finset.mem_insert.mp hh with e | hh
    · exact e ▸ cg
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hh
    exact (Finset.mem_filter.mp hi).2
  have out : C.output ∉ X := fun h => residual_nonconstant G C cor only remaining true (Xconst _ h)
  obtain ⟨x,y,agree,diff⟩ := sensitive G C cor ab.symm
  obtain ⟨k,hk,off,t,ht,port⟩ := crosses C ao X x y
    (fun v hv => agree v (by rintro rfl; exact hv (by simp [X]))) diff out
  have ng : g ∉ B := fun h => separate G C ao cor ab ag o uniq ((mem_readers ..).mp h)
  have kg : k ≠ g := by rintro rfl; exact off (by simp [X])
  have kn : k ∉ B := by
    intro kb
    have bothc : Const (val C r (n+k)) := by
      have neq : b.val ≠ t := by
        rintro eq
        rw [← eq] at ht
        rcases Finset.mem_insert.mp ht with e | hh
        · exact ab.ne (Fin.ext e.symm)
        rcases Finset.mem_insert.mp hh with e | hh
        · have := b.isLt; omega
        obtain ⟨i,_,e⟩ := Finset.mem_image.mp hh
        have := b.isLt
        change n+i=b.val at e
        omega
      exact both C ao r hk neq ((mem_readers ..).mp kb).choose_spec port cb (Xconst t ht)
    exact off (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨k,Finset.mem_filter.mpr ⟨kb,bothc⟩,rfl⟩)))
  let A := (Finset.range C.size).filter (New C r)
  have dk : k ∉ A := fun h => kill C ao r hk port (Xconst t ht) (Finset.mem_filter.mp h).2
  have dg : g ∉ A := fun h => (Finset.mem_filter.mp h).2.2.2 cg
  have dis : Disjoint A B := Finset.disjoint_left.mpr (by
    intro i hi bi
    have read := (mem_readers C b.val i).mp bi
    exact kill C ao r read.choose read.choose_spec cb (Finset.mem_filter.mp hi).2)
  have sub : insert k (insert g (A ∪ B)) ⊆ Finset.range C.size := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Finset.mem_range.mpr hk
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Finset.mem_range.mpr ag.choose
    rcases Finset.mem_union.mp hi with hi | hi <;> exact (Finset.mem_filter.mp hi).1
  have budget := Finset.card_le_card sub
  simp [kg,kn,ng,dk,dg,Finset.card_union_of_disjoint dis] at budget
  obtain ⟨D,dao,dc,sz⟩ := compile C ao r (raw_inputs C a b true)
    (residual_nonconstant G C cor only remaining true)
  change D.size ≤ A.card at sz
  exact ⟨D,dao,dc.trans (eval_cut G C cor only true), by change D.size+B.card+2 ≤ _; omega⟩

end VertexPeel.CountReaders

#print axioms VertexPeel.CountReaders.cut_joint_readers
