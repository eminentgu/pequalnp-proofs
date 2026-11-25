import PendantObstruction

namespace VertexPeel.CubicJoint
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadTwo
open MixedFold SideReaders SidePeel PendantCross ThreeGatePeel CountReaders CoverCircuit PendantObstruction

/-- All gates already known to be constant after the mixed restriction can
    be charged together with a further gate detected by leaf sensitivity. -/
theorem extra_fold (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (ao : IsAO2 n C) (cor : circuitFun n C = graphFun G ∅) {a b : Fin n} (ab : G.Adj a b)
    (only : ∀ t, G.Adj a t → t=b) (remaining : ∃ u v, G.Adj u v ∧ u≠b ∧ v≠b)
    (S : Finset ℕ) (bounded : S ⊆ Finset.range C.size)
    (const : ∀ i ∈ S, Const (val C (assign a b true) (n+i))) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun (G.deleteIncidenceSet b) ∅ ∧
      D.size + S.card + 1 ≤ C.size := by
  classical
  let r := assign a b true
  let X := insert a.val (S.image (n+·))
  have xc (t : ℕ) (ht : t∈X) : Const (val C r t) := by
    rcases Finset.mem_insert.mp ht with e | hp
    · exact e ▸ ⟨_, raw_a C ab.ne true⟩
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    exact const i hi
  have out : C.output ∉ X := fun hx => residual_nonconstant G C cor only remaining true (xc _ hx)
  obtain ⟨x,y,eq,diff⟩ := sensitive G C cor ab.symm
  obtain ⟨k,hk,off,t,ht,port⟩ := crosses C ao X x y
    (fun v hv => eq v (by rintro rfl; exact hv (by simp [X]))) diff out
  let A := (Finset.range C.size).filter (New C r)
  have nk : k ∉ A := fun h => kill C ao r hk port (xc _ ht) (Finset.mem_filter.mp h).2
  have ks : k ∉ S := fun h => off (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k,h,rfl⟩))
  have dis : Disjoint A S := Finset.disjoint_left.mpr (by
    intro i hi si
    exact (Finset.mem_filter.mp hi).2.2.2 (const i si))
  have sub : insert k (A ∪ S) ⊆ Finset.range C.size := by
    intro i hi
    rcases Finset.mem_insert.mp hi with e | hh
    · exact e ▸ Finset.mem_range.mpr hk
    exact (Finset.mem_union.mp hh).elim (fun ai => (Finset.mem_filter.mp ai).1) (fun si => bounded si)
  have budget := Finset.card_le_card sub
  simp [nk,ks,Finset.card_union_of_disjoint dis] at budget
  obtain ⟨D,dao,dc,ds⟩ := compile C ao r (raw_inputs C a b true)
    (residual_nonconstant G C cor only remaining true)
  change D.size ≤ A.card at ds
  exact ⟨D,dao,dc.trans (eval_cut G C cor only true),by omega⟩

private theorem mono_wire (C : Circuit) (ao : IsAO2 n C) (x y : Fin n → Bool)
    (le : ∀ i, x i = true → y i = true) (w : ℕ) : wval C x w = true → wval C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases raw : w < n
    · simpa [ZeroFold.wval_in C x ⟨w,raw⟩,ZeroFold.wval_in C y ⟨w,raw⟩] using le ⟨w,raw⟩
    by_cases past : n+C.gates.length ≤ w
    · simp [ZeroFold.wval_past C x w past]
    obtain ⟨j,rfl⟩ : ∃ j, w=n+j := ⟨w-n,by omega⟩
    have hj : j < C.gates.length := by omega
    obtain ⟨u,v,ports,hu,hv,op⟩ := ZeroFold.two n C ao j hj
    rw [ZeroFold.wval_gate C x j u v hj ports hu hv,ZeroFold.wval_gate C y j u v hj ports hu hv]
    rcases op with op | op
    · simp only [op,GateOp.eval,List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true]
      exact fun h => ⟨ih u hu h.1,ih v hv h.2⟩
    · simp only [op,GateOp.eval,List.any_cons,List.any_nil,Bool.or_false,Bool.or_eq_true]
      exact Or.imp (ih u hu) (ih v hv)

/-- Before a variable's unique reader, every other wire is independent of it. -/
private theorem prior (C : Circuit) (ao : IsAO2 n C) (a : Fin n) {j : ℕ}
    (unique : ∀ k, Reads C k a.val → k=j) (x y : Fin n → Bool)
    (eq : ∀ i, i≠a → x i=y i) (w : ℕ) (prior : w<n+j) (ne : w≠a.val) : wval C x w=wval C y w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases raw : w < n
    · erw [ZeroFold.wval_in C x ⟨w,raw⟩,ZeroFold.wval_in C y ⟨w,raw⟩]
      exact eq ⟨w,raw⟩ (fun e => ne (congrArg Fin.val e))
    by_cases past : n+C.gates.length ≤ w
    · rw [ZeroFold.wval_past C x w past,ZeroFold.wval_past C y w past]
    obtain ⟨k,rfl⟩ : ∃ k, w=n+k := ⟨w-n,by omega⟩
    have hk : k < C.gates.length := by omega
    obtain ⟨u,v,ports,hu,hv,op⟩ := ZeroFold.two n C ao k hk
    have free (t : ℕ) (hit : t ∈ C.gates[k].inputs) : t ≠ a.val := by
      rintro rfl
      have := unique k ⟨hk,hit⟩
      omega
    rw [ZeroFold.wval_gate C x k u v hk ports hu hv,ZeroFold.wval_gate C y k u v hk ports hu hv,
      ih u hu (by omega) (free u (by simp [ports])),ih v hv (by omega) (free v (by simp [ports]))]

/-- A singly-read neighbor fed into b AND u needs a direct connection from
    the leaf's unique OR gate. Otherwise deleting b saves at least four gates. -/
theorem four_of_indirect (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (ao : IsAO2 n C) (cor : circuitFun n C = graphFun G ∅) {a b : Fin n} (ab : G.Adj a b)
    (only : ∀ t, G.Adj a t → t=b) (remaining : ∃ u v, G.Adj u v ∧ u≠b ∧ v≠b)
    {g j u : ℕ} (ag : Reads C g a.val) (bor : (C.gates[g]'ag.choose).op = .or)
    (ua : ∀ k, Reads C k a.val → k=g) (bj : Reads C j b.val)
    (band : (C.gates[j]'bj.choose).op = .and) (ub : ∀ k, Reads C k b.val → k=j)
    (uj : Reads C j u) (raw_ne : u≠b.val) (indirect : u≠n+g) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun (G.deleteIncidenceSet b) ∅ ∧
      D.size + 4 ≤ C.size := by
  classical
  let x := bits {a,b}
  let y := bits {a,a}
  have diff : wval C x C.output ≠ wval C y C.output := by
    change circuitFun n C _ ≠ circuitFun n C _
    rw [cor]
    intro h
    exact G.loopless.irrefl a ((pair_iff G a a).mp (h.symm.trans ((pair_iff G a b).mpr ab)))
  have eq (i : Fin n) (ib : i≠b) : x i=y i := by simp [x,y,bits,ib]
  obtain ⟨k,hk,_,dk,t,ht,port⟩ := crosses_diff C ao {b.val} x y
    (fun i hi => eq i (by rintro rfl; simp at hi)) diff (by simpa using no_raw_output G cor b)
  obtain rfl : k=j := ub k ⟨hk,Finset.mem_singleton.mp ht ▸ port⟩
  obtain ⟨d,e,ports,hd,he,_⟩ := ZeroFold.two n C ao k hk
  have sides : d=b.val ∧ e=u ∨ d=u ∧ e=b.val := by
    have bl : b.val=d ∨ b.val=e := by simpa [ports] using bj.choose_spec
    have ul : u=d ∨ u=e := by simpa [ports] using uj.choose_spec
    grind
  have ev (z : Fin n → Bool) : wval C z (n+k) = (z b && wval C z u) := by
    rw [ZeroFold.wval_and C z k d e hk ports hd he band]
    rcases sides with ⟨h,l⟩ | ⟨h,l⟩
    · rw [h,l,ZeroFold.wval_in]
    · rw [h,l,ZeroFold.wval_in,Bool.and_comm]
  have up : u<n+k := by rcases sides with ⟨h,l⟩ | ⟨h,l⟩ <;> omega
  have uy : wval C y u = true := by
    have e := prior C ao b ub x y eq u up raw_ne
    rw [ev x,ev y] at dk
    simpa [x,y,bits,ab.ne.symm,e] using dk
  let r := assign a b true
  have cu : val C r u = fun _ => true := by
    funext z
    exact mono_wire C ao y (r z) (fun i h => by
      have ia : i=a := by simpa [y,bits] using h
      simp [r,assign,ia,ab.ne]) u uy
  have gk : g≠k := by rintro rfl; simp [band] at bor
  have lower : n ≤ u := by
    by_contra! raw
    have atA := ZeroFold.wval_in C y ⟨u,raw⟩
    have uv : (⟨u,raw⟩ : Fin n) = a := by simpa [y,bits] using atA.symm.trans uy
    have e := ua k ⟨hk,(congrArg Fin.val uv) ▸ uj.choose_spec⟩
    exact gk e.symm
  obtain ⟨i,rfl⟩ : ∃ i, u=n+i := ⟨u-n,by omega⟩
  have ik : i<k := by omega
  have ig : i≠g := by omega
  let S : Finset ℕ := {g,k,i}
  have sc : S.card=3 := by simp [S,gk,ig.symm,Nat.ne_of_gt ik]
  have bdd : S ⊆ Finset.range C.size := by
    intro h hh
    simp [S] at hh
    rcases hh with rfl | rfl | rfl <;> apply Finset.mem_range.mpr
    · exact ag.choose
    · exact hk
    · exact Nat.lt_trans ik hk
  have cg : Const (val C r (n+g)) := canal C ao r ag.choose ag.choose_spec
    (by simpa [bor] using raw_a C ab.ne true)
  have ck : Const (val C r (n+k)) := canal C ao r hk bj.choose_spec
    (by simpa [band] using raw_b C a b true)
  have cst (h : ℕ) (hh : h∈S) : Const (val C r (n+h)) := by
    simp [S] at hh
    rcases hh with rfl | rfl | rfl
    · exact cg
    · exact ck
    · exact ⟨_,cu⟩
  obtain ⟨D,dao,dc,ds⟩ := extra_fold G C ao cor ab only remaining S bdd cst
  exact ⟨D,dao,dc,by omega⟩

private theorem no_repeat (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (least : IsLeastAO G C) {j w : ℕ} (hj : j < C.gates.length) (hw : w<n+j) :
    C.gates[j].inputs ≠ [w,w] := by
  classical
  intro twice
  have bad : ¬ZeroFold.Mg C (∅ : Finset (Fin n)) j := by
    rintro ⟨_,new,_⟩
    apply new w hw
    funext x
    obtain ⟨_,_,_,_,_,op⟩ := ZeroFold.two n C least.1 j hj
    rcases op with op | op
    · simp [ZeroFold.fv_and C ∅ j w w hj twice hw hw op]
    · simp [ZeroFold.fv_or C ∅ j w w hj twice hw hw op]
  obtain ⟨D,dao,dc,ds⟩ := ZeroFold.compile C least.1 (∅ : Finset (Fin n))
  have same : ZeroFold.fv C (∅ : Finset (Fin n)) C.output = circuitFun n C := by
    funext x
    change wval C (ZeroFold.zr ∅ x) C.output = wval C x C.output
    apply congrArg (fun z => wval C z C.output)
    funext i
    simp [ZeroFold.zr]
  have le := least.2.2 D dao (dc.trans (same.trans least.2.1))
  have sub : (Finset.range C.size).filter (ZeroFold.Mg C (∅ : Finset (Fin n))) ⊂ Finset.range C.size :=
    Finset.ssubset_iff_of_subset (Finset.filter_subset _ _ ) |>.mpr
      ⟨j, Finset.mem_range.mpr hj, by simp [bad]⟩
  have strict := Finset.card_lt_card sub
  simp only [Finset.card_range] at strict
  omega

/-- At a cubic neighbor, simultaneous failure at leaf and neighbor forces two
    unique readers in every least circuit. An AND reading the neighbor must
    have the leaf's OR as its other input. -/
theorem cubic_reader_shape (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {a b : Fin n}
    (ab : G.Adj a b) (leaf : G.degree a=1) (cubic : G.degree b=3)
    (other : ∃ c, G.Adj b c ∧ c≠a) (remaining : ∃ u v, G.Adj u v ∧ u≠b ∧ v≠b)
    (C : Circuit) (least : IsLeastAO G C) :
    PeelsAt G a ∨ PeelsAt G b ∨ ∃ g, ∃ ag : Reads C g a.val, ∃ j, ∃ bj : Reads C j b.val,
      (C.gates[g]'ag.choose).op = .or ∧ (∀ k, Reads C k a.val → k=g) ∧ ¬Reads C g b.val ∧
      (∀ k, Reads C k b.val → k=j) ∧
      ((C.gates[j]'bj.choose).op = .or ∨ ((C.gates[j]'bj.choose).op = .and ∧ Reads C j (n+g))) := by
  classical
  rcases peel_or_few_readers G ab leaf other remaining C least with ha | hb | ⟨g,ag,op,ua,ng,few⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl hb)
  right
  obtain ⟨j,bj⟩ := raw_reader G C least.1 least.2.1 b a ab.symm
  have small : (readers C b.val).card ≤ 1 := by omega
  have ub (k : ℕ) (bk : Reads C k b.val) : k=j :=
    Finset.card_le_one.mp small k ((mem_readers ..).mpr bk) j ((mem_readers ..).mpr bj)
  obtain ⟨d,e,ports,hd,he,opj⟩ := ZeroFold.two n C least.1 j bj.choose
  rcases opj with band | bor
  · by_cases direct : Reads C j (n+g)
    · exact Or.inr ⟨g,ag,j,bj,op,ua,ng,ub,Or.inr ⟨band,direct⟩⟩
    left
    have de : d≠e := by rintro rfl; exact no_repeat G C least bj.choose hd ports
    have bl : b.val=d ∨ b.val=e := by simpa [ports] using bj.choose_spec
    obtain ⟨u,read,ne⟩ : ∃ u, Reads C j u ∧ u≠b.val := by
      rcases bl with bd | be
      · exact ⟨e,⟨bj.choose,by simp [ports]⟩,by omega⟩
      · exact ⟨d,⟨bj.choose,by simp [ports]⟩,by omega⟩
    have only (t : Fin n) (h : G.Adj a t) : t=b := by
      have one : (G.neighborFinset a).card ≤ 1 := by simpa using leaf.le
      exact Finset.card_le_one.mp one t ((G.mem_neighborFinset _ _).mpr h)
        b ((G.mem_neighborFinset _ _).mpr ab)
    obtain ⟨D,dao,dc,ds⟩ := four_of_indirect G C least.1 least.2.1 ab only remaining ag op ua bj band ub
      read ne (fun eq => direct (eq ▸ read))
    intro E eao ec
    have lim := least.2.2 E eao ec
    refine ⟨D,dao,dc.trans ?_,by omega,fun _ => by omega⟩
    funext x
    simp [graphFun,SimpleGraph.deleteIncidenceSet]
  · exact Or.inr ⟨g,ag,j,bj,op,ua,ng,ub,Or.inl bor⟩

/-- If the only reader of b is b OR u, the signal u already implies an edge
    surviving deletion of b. This holds on every input, including at a=0. -/
theorem single_or_core (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (ao : IsAO2 n C) (cor : circuitFun n C = graphFun G ∅) {a b : Fin n} (ab : G.Adj a b)
    (only : ∀ t, G.Adj a t → t=b) {j u : ℕ} (bj : Reads C j b.val)
    (bor : (C.gates[j]'bj.choose).op = .or) (ub : ∀ k, Reads C k b.val → k=j)
    (uj : Reads C j u) (raw_ne : u≠b.val) (x : Fin n → Bool) (on : wval C x u=true) :
    graphFun (G.deleteIncidenceSet b) ∅ x = true := by
  classical
  let z := assign a b true x
  let y := Function.update z b true
  let x₀ := Function.update x b false
  obtain ⟨d,e,ports,hd,he,_⟩ := ZeroFold.two n C ao j bj.choose
  have sides : d=b.val ∧ e=u ∨ d=u ∧ e=b.val := by
    have bl : b.val=d ∨ b.val=e := by simpa [ports] using bj.choose_spec
    have ul : u=d ∨ u=e := by simpa [ports] using uj.choose_spec
    grind
  have ev (s : Fin n → Bool) : wval C s (n+j) = (s b || wval C s u) := by
    rw [ZeroFold.wval_or C s j d e bj.choose ports hd he bor]
    rcases sides with ⟨h,l⟩ | ⟨h,l⟩
    · rw [h,l,ZeroFold.wval_in]
    · rw [h,l,ZeroFold.wval_in,Bool.or_comm]
  have up : u<n+j := by rcases sides with ⟨h,l⟩ | ⟨h,l⟩ <;> omega
  have on₀ : wval C x₀ u=true := (prior C ao b ub x x₀
    (fun i ne => by simp [x₀,ne]) u up raw_ne).symm.trans on
  have onz : wval C z u=true := mono_wire C ao x₀ z (by
    intro i hi
    by_cases ib : i=b
    · simp [x₀,ib] at hi
    by_cases ia : i=a
    · simp [z,assign,ia,ab.ne]
    · simpa [x₀,z,assign,ib,ia] using hi) u on₀
  have pos : wval C y C.output=true := by
    change circuitFun n C y=true
    rw [cor]
    simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,
      decide_eq_true_eq]
    exact ⟨a,b,ab,by simp [y,z,assign,ab.ne],by simp [y]⟩
  by_contra off
  have neg : wval C z C.output ≠ true := by
    exact fun hx => off ((congrFun (eval_cut G C cor only true) x).symm.trans hx)
  obtain ⟨k,hk,_,dk,t,ht,p⟩ := crosses_diff C ao {b.val} z y
    (fun i hh => by have ib : i≠b := by rintro rfl; simp at hh
                    simp [y,ib]) (fun h => neg (h.trans pos)) (by simpa using no_raw_output G cor b)
  obtain rfl : k=j := ub k ⟨hk,Finset.mem_singleton.mp ht ▸ p⟩
  exact dk (by simp [ev,onz,y])

end VertexPeel.CubicJoint

#print axioms VertexPeel.CubicJoint.cubic_reader_shape
#print axioms VertexPeel.CubicJoint.single_or_core
