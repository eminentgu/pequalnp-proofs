import PEqualNP.Outside.L_meta_4846

namespace PEqualNP.Research.OwnershipMasking

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4846

def Ready {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∃ u v, G.Adj u v ∧ Owns n C k u v

private def shift (cut w : ℕ) := if w < cut then w else w - 1

private def shiftGate (cut : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (shift cut)⟩

private lemma lookup_shift (pre post : List Bool) (v : Bool) (i : ℕ)
    (hne : i ≠ pre.length) :
    (pre ++ post).getD (shift pre.length i) false =
      (pre ++ [v] ++ post).getD i false := by
  by_cases h : i < pre.length
  · simp only [shift,h,ite_true]
    rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (by simp; omega),
      List.getD_append _ _ _ _ h]
  · have old : pre.length + 1 ≤ i := by omega
    have newLt : pre.length ≤ i - 1 := by omega
    simp only [shift,h,ite_false,List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right newLt,
      List.getElem?_append_right (show (pre ++ [v]).length ≤ i by simpa using old)]
    simp
    congr 2
    omega

private lemma run_shift (pre post : List Bool) (v : Bool) (gs : List Gate)
    (hu : ∀ g ∈ gs, pre.length ∉ g.inputs) :
    ∃ ext : List Bool,
      wf (gs.map (shiftGate pre.length)) (pre ++ post) = pre ++ ext ∧
      wf gs (pre ++ [v] ++ post) = pre ++ [v] ++ ext := by
  induction gs generalizing post with
  | nil => exact ⟨post,rfl,rfl⟩
  | cons g gs ih =>
    let t := g.op.eval (g.inputs.map fun i => (pre ++ [v] ++ post).getD i false)
    have eq : (shiftGate pre.length g).op.eval
        ((shiftGate pre.length g).inputs.map fun i => (pre ++ post).getD i false) = t := by
      apply congrArg g.op.eval
      simp only [shiftGate,List.map_map]
      apply List.map_congr_left
      intro i hi
      exact lookup_shift pre post v i (fun h => hu g (.head _) (h ▸ hi))
    obtain ⟨ext,hnew,hold⟩ := ih (post++[t]) (fun q h => hu q (.tail _ h))
    refine ⟨ext,?_,?_⟩
    · change wf (gs.map (shiftGate pre.length)) ((pre++post)++[_]) = _
      rw [eq,List.append_assoc]; exact hnew
    · change wf gs (((pre++[v])++post)++[t]) = _
      rw [List.append_assoc]; exact hold

private lemma used_later {n : ℕ} (C : Circuit) (hmin : IsMinimalMonoCircuit n C)
    (j : ℕ) (hj : j < C.gates.length) :
    C.output = n+j ∨ ∃ (k : ℕ) (hk : k < C.gates.length), j < k ∧ n+j ∈ C.gates[k].inputs := by
  classical
  by_contra! hall
  let pre := C.gates.take j
  let post := C.gates.drop (j+1)
  let g := C.gates[j]
  have lp : pre.length = j := by simp [pre,Nat.min_eq_left hj.le]
  have splitG : C.gates = pre ++ g :: post := by
    rw [show g :: post = C.gates.drop j by
      simp [g,post]]
    exact (List.take_append_drop ..).symm
  have notRead : ∀ q ∈ post, n+j ∉ q.inputs := by
    intro q hq
    obtain ⟨k,hk,hget⟩ := List.mem_iff_getElem.mp hq
    have bound : j+1+k < C.gates.length := by
      change k < (C.gates.drop (j+1)).length at hk
      rw [List.length_drop] at hk
      omega
    have hq' : C.gates[j+1+k] = q := by simpa [post] using hget
    simpa [hq'] using hall.2 (j+1+k) bound (by omega)
  let D : Circuit := ⟨pre ++ post.map (shiftGate (n+j)),shift (n+j) C.output⟩
  have legal : Monotone2 D := by
    intro q hq
    rcases List.mem_append.mp hq with h | h
    · exact hmin.1 q (List.mem_of_mem_take h)
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp h
      simpa [shiftGate] using hmin.1 r (List.mem_of_mem_drop hr)
  have same : circuitFun n D = circuitFun n C := by
    funext x
    let w := wf pre (List.ofFn x)
    have len : w.length = n+j := by simp [w,wf_len,lp]
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨ext,hnew,hold⟩ := run_shift w [] v post (by simpa [len] using notRead)
    simp only [List.append_nil,len] at hnew hold
    change (wf (pre ++ post.map (shiftGate (n+j))) (List.ofFn x)).getD _ _ =
      (wf C.gates (List.ofFn x)).getD _ _
    rw [splitG]
    have wf_app (a b : List Gate) (ww : List Bool) : wf (a++b) ww = wf b (wf a ww) := by
      simp [wf,List.foldl_append]
    rw [wf_app, wf_app]
    change (wf (post.map (shiftGate (n+j))) w).getD _ _ = (wf post (w++[v])).getD _ _
    rw [hnew,hold]
    simpa [len] using lookup_shift w ext v C.output (by simpa [len] using hall.1)
  have le := hmin.2 D legal same
  change C.gates.length ≤ (pre ++ post.map _).length at le
  simp only [List.length_append,List.length_map,lp,post,List.length_drop] at le
  omega

private lemma op_at {C : Circuit} {k : ℕ} (hk : k < C.gates.length) :
    (gateAt C k).op = C.gates[k].op := by
  rw [gateAt, List.getD_eq_getElem _ _ hk]

private lemma src_val {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i k : ℕ}
    (hik : i < k) (hk : k < C.gates.length) :
    (wf (C.gates.take k) (List.ofFn x)).getD (n+i) false = gateVal n C i x := by
  exact (wire_take C.gates (List.ofFn x) k (n+i) (by simp; omega) hk.le).symm

private lemma cone_extend {n : ℕ} (C : Circuit) {j i k : ℕ}
    (hk : k < C.gates.length) (hik : i < k) (hr : n+i ∈ C.gates[k].inputs)
    (path : j = i ∨ InCone n C j i) : InCone n C j k := by
  apply (cone_iff n C.gates k hk j).2
  refine ⟨n+i,hr,by omega,by omega,?_⟩
  rw [show n+i-n=i by omega]
  exact path

private lemma and_input {n : ℕ} (C : Circuit) {k i : ℕ} (hk : k < C.gates.length)
    (op : (gateAt C k).op = .and) (hik : i < k) (hr : n+i ∈ C.gates[k].inputs)
    (x : Fin n → Bool) (h : gateVal n C k x = true) : gateVal n C i x = true := by
  rw [valf n C x k hk, ← op_at hk, op] at h
  change List.all _ id = true at h
  have mem := List.mem_map_of_mem (f := fun s => (wf (C.gates.take k) (List.ofFn x)).getD s false) hr
  rw [← src_val C x hik hk]
  exact List.all_eq_true.mp h _ mem

private lemma or_input {n : ℕ} (C : Circuit) {k i : ℕ} (hk : k < C.gates.length)
    (op : (gateAt C k).op = .or) (hik : i < k) (hr : n+i ∈ C.gates[k].inputs)
    (x : Fin n → Bool) (h : gateVal n C i x = true) : gateVal n C k x = true := by
  rw [valf n C x k hk, ← op_at hk, op]
  apply List.any_eq_true.mpr
  refine ⟨_, List.mem_map_of_mem (f := fun s => (wf (C.gates.take k) (List.ofFn x)).getD s false) hr, ?_⟩
  exact (src_val C x hik hk).trans h

/-- In a ready circuit a later AND cannot directly read an earlier AND. -/
theorem no_direct_and {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} (ready : Ready G C)
    {i k : ℕ} (hik : i < k) (hk : k < C.gates.length)
    (opI : (gateAt C i).op = .and) (opK : (gateAt C k).op = .and) :
    n+i ∉ C.gates[k].inputs := by
  intro hr
  obtain ⟨u,v,_,own⟩ := ready k hk opK
  have hi := and_input C hk opK hik hr _ own.2.2.1
  have hf := own.2.2.2 i hik (cone_extend C hk hik hr (Or.inl rfl)) opI
  simp [hf] at hi

private lemma masking_step {n : ℕ} (C : Circuit) (hmin : IsMinimalMonoCircuit n C)
    (x : Fin n → Bool) (out : circuitFun n C x = false) {j : ℕ}
    (hj : j < C.gates.length) (on : gateVal n C j x = true) :
    ∃ (k i : ℕ) (hk : k < C.gates.length), i < k ∧ (j = i ∨ InCone n C j i) ∧
      n+i ∈ C.gates[k].inputs ∧ gateVal n C i x = true ∧
      InCone n C j k ∧ (gateAt C k).op = .and ∧ gateVal n C k x = false := by
  suffices H : ∀ d i, C.gates.length-i = d → i < C.gates.length →
      (j = i ∨ InCone n C j i) → gateVal n C i x = true →
      ∃ (k i : ℕ) (hk : k < C.gates.length), i < k ∧ (j = i ∨ InCone n C j i) ∧
      n+i ∈ C.gates[k].inputs ∧ gateVal n C i x = true ∧
      InCone n C j k ∧ (gateAt C k).op = .and ∧ gateVal n C k x = false by
    exact H _ j rfl hj (Or.inl rfl) on
  intro d
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    intro i hdi hi path hv
    rcases used_later C hmin i hi with stop | ⟨k,hk,hik,hr⟩
    · change (C.wires _).getD C.output false = false at out
      rw [stop] at out
      change (C.wires _).getD (n+i) false = true at hv
      exact Bool.noConfusion (out.symm.trans hv)
    · have pred := cone_extend C hk hik hr path
      cases val : gateVal n C k x with
      | true => exact ih _ (by omega) k rfl hk (.inr pred) val
      | false =>
        have ops := (hmin.1 _ (List.getElem_mem hk)).1
        change C.gates[k].op = .and ∨ C.gates[k].op = .or at ops
        rw [← op_at hk] at ops
        rcases ops with ha | ho
        · exact ⟨k,i,hk,hik,path,hr,hv,pred,ha,val⟩
        · have good := or_input C hk ho hik hr x hv
          simp [val] at good

private lemma nonedge_output {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {u v : Fin n} (hn : ¬G.Adj u v) :
    graphFun G ∅ (pairInput u v) = false := by
  have noEdge : ¬∃ a b : Fin n, G.Adj a b ∧ pairInput u v a = true ∧ pairInput u v b = true := by
    rintro ⟨a,b,hab,ha,hb⟩
    simp [pairInput] at ha hb
    rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
    · exact G.irrefl hab
    · exact hn hab
    · exact hn hab.symm
    · exact G.irrefl hab
  simp [graphFun,noEdge]

private lemma pair_eq_of_edge_eq {n : ℕ} {a b c d : Fin n} (h : s(a,b) = s(c,d)) :
    pairInput a b = pairInput c d := by
  funext z
  have hm : z ∈ s(a,b) ↔ z ∈ s(c,d) := by rw [h]
  apply decide_eq_decide.mpr
  simpa only [Sym2.mem_iff] using hm

/-- A bad AND in a least ready circuit leaks a nonedge. A later AND in its cone rejects that
assignment and owns a third edge. On the third edge the initial AND is false. -/
theorem third_edge_mask {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hmin : IsMinimalMonoCircuit n C) (four : PEqualNP.TopForm.NoFourCycle G)
    (hf : circuitFun n C = graphFun G ∅) (ready : Ready G C) {j : ℕ} {a b c d : Fin n}
    (hab : G.Adj a b) (hcd : G.Adj c d) (one : Owns n C j a b) (two : Owns n C j c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    ∃ (u v : Fin n) (k : ℕ) (p q : Fin n),
      ¬G.Adj u v ∧ gateVal n C j (pairInput u v) = true ∧
      j < k ∧ InCone n C j k ∧ gateVal n C k (pairInput u v) = false ∧
      G.Adj p q ∧ Owns n C k p q ∧ gateVal n C j (pairInput p q) = false ∧
      s(p,q) ≠ s(a,b) ∧ s(p,q) ≠ s(c,d) ∧ n+j ∉ (gateAt C k).inputs := by
  obtain ⟨u,v,hn,on⟩ :=
    PEqualNP.Outside.L_meta_4846 n G C four hmin.1 j a b c d hab hcd hac had hbc hbd one two
  have off : circuitFun n C (pairInput u v) = false := by rw [hf,nonedge_output G hn]
  obtain ⟨k,_,_,_,_,_,_,path,op,ko⟩ := masking_step C hmin _ off one.1 on
  have hk := cone_lt n C.gates j k path
  have hjk := cone_idx n C.gates k j path
  obtain ⟨p,q,hpq,own⟩ := ready k hk op
  have jo := own.2.2.2 j hjk path one.2.1
  refine ⟨u,v,k,p,q,hn,on,hjk,path,ko,hpq,own,jo,?_,?_,?_⟩
  · intro h
    rw [pair_eq_of_edge_eq h] at jo
    simp [one.2.2.1] at jo
  · intro h
    rw [pair_eq_of_edge_eq h] at jo
    simp [two.2.2.1] at jo
  · rw [gateAt,List.getD_eq_getElem _ _ hk]
    exact no_direct_and ready hjk hk one.2.1 op

/-- The last true gate before a mask is an OR. The mask has a different, earlier wire
which distinguishes the leaking assignment from its owned edge. -/
theorem masking_inputs {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hmin : IsMinimalMonoCircuit n C) (ready : Ready G C) {j : ℕ}
    (hj : j < C.gates.length) (oj : (gateAt C j).op = .and) (x : Fin n → Bool)
    (on : gateVal n C j x = true) (off : circuitFun n C x = false) :
    ∃ (k i w : ℕ) (p q : Fin n), j < i ∧ i < k ∧ InCone n C j i ∧ InCone n C j k ∧
      (gateAt C i).op = .or ∧ (gateAt C k).op = .and ∧
      n+i ∈ (gateAt C k).inputs ∧ w ∈ (gateAt C k).inputs ∧ w ≠ n+i ∧ w < n+k ∧
      G.Adj p q ∧ Owns n C k p q ∧ gateVal n C j (pairInput p q) = false ∧
      gateVal n C i x = true ∧ gateVal n C i (pairInput p q) = true ∧
      gateVal n C k x = false ∧
      (wf (C.gates.take k) (List.ofFn x)).getD w false = false ∧
      (wf (C.gates.take k) (List.ofFn (pairInput p q))).getD w false = true := by
  obtain ⟨k,i,hk,hik,path,hr,flux,jk,ok,mask⟩ := masking_step C hmin x off hj on
  have hi := hik.trans hk
  have oi : (gateAt C i).op = .or := by
    have ops := (hmin.1 _ (List.getElem_mem hi)).1
    change C.gates[i].op = .and ∨ C.gates[i].op = .or at ops
    rw [← op_at hi] at ops
    exact ops.resolve_left (fun ha => no_direct_and ready hik hk ha ok hr)
  have ji : InCone n C j i := by
    rcases path with heq|hji
    · subst i; rw [oj] at oi; cases oi
    · exact hji
  obtain ⟨p,q,hpq,owned⟩ := ready k hk ok
  have itrue := and_input C hk ok hik hr _ owned.2.2.1
  have jfalse := owned.2.2.2 j (cone_idx n C.gates k j jk) jk oj
  have raw : ∃ w ∈ C.gates[k].inputs,
      (wf (C.gates.take k) (List.ofFn x)).getD w false = false := by
    by_contra! h
    rw [valf n C x k hk, ← op_at hk,ok] at mask
    change List.all _ id = false at mask
    have allT : (C.gates[k].inputs.map fun w =>
        (wf (C.gates.take k) (List.ofFn x)).getD w false).all id = true := by
      apply List.all_eq_true.mpr
      intro t mem
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp mem
      simpa only [id_eq,Bool.not_eq_false] using h _ hw
    exact Bool.noConfusion (mask.symm.trans allT)
  obtain ⟨w,hw,wx⟩ := raw
  have wy : (wf (C.gates.take k) (List.ofFn (pairInput p q))).getD w false = true := by
    have ownT := owned.2.2.1
    rw [valf n C _ k hk, ← op_at hk,ok] at ownT
    exact List.all_eq_true.mp ownT _ (List.mem_map_of_mem hw)
  have nw : w ≠ n+i := by
    rintro rfl
    rw [src_val C x hik hk] at wx
    exact Bool.noConfusion (wx.symm.trans flux)
  have early : w < n+k := by
    by_contra! h
    have len : (wf (C.gates.take k) (List.ofFn (pairInput p q))).length = n+k := by
      simp [wf_len,Nat.min_eq_left hk.le]
    rw [List.getD_eq_default _ _ (len ▸ h)] at wy
    cases wy
  have geq : gateAt C k = C.gates[k] := by rw [gateAt,List.getD_eq_getElem _ _ hk]
  exact ⟨k,i,w,p,q,cone_idx n C.gates i j ji,hik,ji,jk,oi,ok,geq ▸ hr,geq ▸ hw,nw,early,
    hpq,owned,jfalse,flux,itrue,mask,wx,wy⟩

/-- A ready minimum circuit for a graph with at most two edges has no bad gate. -/
theorem no_bad_of_le_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hmin : IsMinimalMonoCircuit n C) (four : PEqualNP.TopForm.NoFourCycle G)
    (hf : circuitFun n C = graphFun G ∅) (ready : Ready G C) (few : G.edgeFinset.card ≤ 2)
    {j : ℕ} {a b c d : Fin n} (hab : G.Adj a b) (hcd : G.Adj c d)
    (one : Owns n C j a b) (two : Owns n C j c d) :
    a = c ∨ a = d ∨ b = c ∨ b = d := by
  by_contra! disjoint
  obtain ⟨_,_,_,p,q,_,_,_,_,_,hpq,_,_,hp,hc,_⟩ :=
    third_edge_mask G C hmin four hf ready hab hcd one two
      disjoint.1 disjoint.2.1 disjoint.2.2.1 disjoint.2.2.2
  have hdiff : s(a,b) ≠ s(c,d) := by
    intro eq
    have hm : a ∈ s(c,d) := eq ▸ Sym2.mem_mk_left a b
    exact (Sym2.mem_iff.mp hm).elim disjoint.1 disjoint.2.1
  let S : Finset (Sym2 (Fin n)) := {s(p,q),s(a,b),s(c,d)}
  have sub : S ⊆ G.edgeFinset := by
    intro t ht
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl|rfl|rfl
    · simpa using hpq
    · simpa using hab
    · simpa using hcd
  have count : S.card = 3 := by simp [S,hp,hc,hdiff]
  have hle := Finset.card_le_card sub
  omega

def Bad {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (j : ℕ) : Prop :=
  ∃ a b c d : Fin n, G.Adj a b ∧ G.Adj c d ∧ Owns n C j a b ∧ Owns n C j c d ∧
    a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d

private lemma intersecting_star {n : ℕ} (G : SimpleGraph (Fin n))
    (tri : ∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a)
    (E : Fin n → Fin n → Prop) (valid : ∀ u v, E u v → G.Adj u v)
    (ne : ∃ a b, E a b)
    (meet : ∀ a b c d, E a b → E c d → a=c ∨ a=d ∨ b=c ∨ b=d) :
    ∃ z, ∀ a b, E a b → a=z ∨ b=z := by
  obtain ⟨a,b,ab⟩ := ne
  by_cases ha : ∀ c d, E c d → c=a ∨ d=a
  · exact ⟨a,ha⟩
  push Not at ha
  obtain ⟨c,d,cd,hca,hda⟩ := ha
  refine ⟨b,?_⟩
  intro u v uv
  have m1 := meet a b c d ab cd
  have m2 := meet a b u v ab uv
  have m3 := meet c d u v cd uv
  have e1 := valid a b ab
  have e2 := valid c d cd
  have e3 := valid u v uv
  have e1' := e1.symm
  have e2' := e2.symm
  have e3' := e3.symm
  grind

/-- The last bad gate has a strictly later masking AND. The owned graph edges of that AND
form a nonempty star. -/
theorem last_bad_star_mask {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hmin : IsMinimalMonoCircuit n C) (four : PEqualNP.TopForm.NoFourCycle G)
    (tri : ∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a)
    (hf : circuitFun n C = graphFun G ∅) (ready : Ready G C) (bad : ∃ j, Bad G C j) :
    ∃ (j k : ℕ) (u v p q z : Fin n), Bad G C j ∧ (∀ t, Bad G C t → t ≤ j) ∧
      j < k ∧ InCone n C j k ∧ ¬G.Adj u v ∧ gateVal n C j (pairInput u v) = true ∧
      gateVal n C k (pairInput u v) = false ∧ G.Adj p q ∧ Owns n C k p q ∧
      gateVal n C j (pairInput p q) = false ∧
      ∀ a b, G.Adj a b → Owns n C k a b → a=z ∨ b=z := by
  classical
  let badGates := (Finset.range C.gates.length).filter (Bad G C)
  have member (t : ℕ) (bt : Bad G C t) : t ∈ badGates := by
    have witness := bt
    obtain ⟨_,_,_,_,_,_,ot,_⟩ := witness
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ot.1,bt⟩
  obtain ⟨m,bm⟩ := bad
  have ne : badGates.Nonempty := ⟨m,member m bm⟩
  let j := badGates.max' ne
  have bj : Bad G C j := (Finset.mem_filter.mp (badGates.max'_mem ne)).2
  have last (t : ℕ) (bt : Bad G C t) : t ≤ j := badGates.le_max' t (member t bt)
  have witness := bj
  obtain ⟨a,b,c,d,hab,hcd,one,two,hac,had,hbc,hbd⟩ := witness
  obtain ⟨u,v,k,p,q,nonedge,on,jk,path,off,hpq,own,joff,_⟩ :=
    third_edge_mask G C hmin four hf ready hab hcd one two hac had hbc hbd
  let E := fun a b => G.Adj a b ∧ Owns n C k a b
  have meet (e f g h : Fin n) (hef : E e f) (hgh : E g h) :
      e=g ∨ e=h ∨ f=g ∨ f=h := by
    by_contra! hd
    have bk : Bad G C k := ⟨e,f,g,h,hef.1,hgh.1,hef.2,hgh.2,hd⟩
    exact Nat.not_le_of_lt jk (last k bk)
  obtain ⟨z,center⟩ := intersecting_star G tri E (fun _ _ h => h.1) ⟨p,q,hpq,own⟩ meet
  exact ⟨j,k,u,v,p,q,z,bj,last,jk,path,nonedge,on,off,hpq,own,joff,
    fun a b ea oa => center a b ⟨ea,oa⟩⟩

end PEqualNP.Research.OwnershipMasking
