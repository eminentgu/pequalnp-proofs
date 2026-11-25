import PEqualNP.Outside.L_meta_4846

namespace PetersenResearch.OwnershipMasking

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

private lemma masking_gate {n : ℕ} (C : Circuit) (hmin : IsMinimalMonoCircuit n C)
    (x : Fin n → Bool) (out : circuitFun n C x = false) {j : ℕ}
    (hj : j < C.gates.length) (on : gateVal n C j x = true) :
    ∃ k, InCone n C j k ∧ (gateAt C k).op = .and ∧ gateVal n C k x = false := by
  suffices H : ∀ d i, C.gates.length-i = d → i < C.gates.length →
      (j = i ∨ InCone n C j i) → gateVal n C i x = true →
      ∃ k, InCone n C j k ∧ (gateAt C k).op = .and ∧ gateVal n C k x = false by
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
        · exact ⟨k,pred,ha,val⟩
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
  obtain ⟨k,path,op,ko⟩ := masking_gate C hmin _ off one.1 on
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

end PetersenResearch.OwnershipMasking
