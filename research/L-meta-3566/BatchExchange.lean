import Equivalence
import PEqualNP.Outside.L_meta_2668
import PEqualNP.Outside.L_meta_2573
import PEqualNP.MetaComplexity.Helpers.LocGraph

namespace VertexPeel.BatchExchange

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.MetaComplexity.CoverPromise PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2668 (bypass bypass_mono bypass_length bypass_eval_rel opMono_reverse val_ge gateAt_mem)
open VertexPeel.CoverCircuit

def valid : Nat → List Nat → Prop
  | _, [] => True
  | m, i::is => i < m ∧ valid (m-1) is

/-- The gate positions here refer to the current circuit. Supplying the original
positions in decreasing order erases any prescribed set, preserving its lower indices. -/
def cut (n : Nat) (C : Circuit) : List Nat → Circuit
  | [] => C
  | k::ks => cut n (bypass n C k (n+C.size)) ks

theorem cut_spec {n : Nat} (C : Circuit) (mono : Monotone2 C) (ks : List Nat)
    (ok : valid C.size ks) :
    Monotone2 (cut n C ks) ∧ (cut n C ks).size + ks.length = C.size ∧
    ∀ x, circuitFun n (cut n C ks) x = true → circuitFun n C x = true := by
  induction ks generalizing C with
  | nil => exact ⟨mono,by simp [cut],fun _ h => h⟩
  | cons k ks ih =>
    obtain ⟨hk,tail⟩ := ok
    let D := bypass n C k (n+C.size)
    have sz : D.size = C.size-1 := bypass_length ..
    obtain ⟨dm,dsize,down⟩ := ih D (bypass_mono mono) (sz.symm ▸ tail)
    refine ⟨dm,?_,?_⟩
    · change (cut n D ks).size + (k::ks).length = C.size
      rw [List.length_cons]; omega
    · intro x on
      have h := down x on
      apply bypass_eval_rel (R := fun a b => b=true → a=true) (fun _ => id) opMono_reverse
        (n:=n) (C:=C) (x:=List.ofFn x) (by simp) (fun j hj => (mono _ (gateAt_mem hj)).1) hk
        (Or.inr le_rfl) _ h
      rw [val_ge (n:=n) (by simp) le_rfl]
      intro contra
      contradiction

/-- An actual loss means that the *whole* cut circuit rejects the two-vertex input. -/
def loss {n : Nat} (G : SimpleGraph (Fin n)) (D : Circuit) : SimpleGraph (Fin n) where
  Adj a b := G.Adj a b ∧ circuitFun n D (pairInput a b) = false
  symm.symm a b h := by
    have eq : pairInput b a = pairInput a b := funext (fun i => by simp only [pairInput,or_comm])
    exact ⟨h.1.symm,eq ▸ h.2⟩
  loopless.irrefl a h := h.1.ne rfl

instance {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit) :
    DecidableRel (loss G D).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

private theorem loss_completion {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Circuit) (dm : Monotone2 D)
    (down : ∀ x, circuitFun n D x = true → graphFun G ∅ x = true) (x : Fin n → Bool) :
    (circuitFun n D x || graphFun (loss G D) ∅ x) = graphFun G ∅ x := by
  cases hx : graphFun G ∅ x with
  | false =>
    have off : circuitFun n D x = false := Bool.eq_false_iff.mpr (fun on => Bool.noConfusion ((down x on).symm.trans hx))
    have empty : graphFun (loss G D) ∅ x = false := by
      apply Bool.eq_false_iff.mpr
      intro on
      obtain ⟨a,b,e,ha,hb⟩ : ∃ a b, (loss G D).Adj a b ∧ x a=true ∧ x b=true := by simpa [graphFun] using on
      have onG : graphFun G ∅ x = true := by simpa [graphFun] using (show ∃ i j, G.Adj i j ∧ x i=true ∧ x j=true from ⟨a,b,e.1,ha,hb⟩)
      exact Bool.noConfusion (onG.symm.trans hx)
    simp [off,empty]
  | true =>
    obtain ⟨a,b,edge,ha,hb⟩ : ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true := by simpa [graphFun] using hx
    cases pair : circuitFun n D (pairInput a b) with
    | false =>
      have yes : graphFun (loss G D) ∅ x = true := by simpa [graphFun] using
        (show ∃ i j, (loss G D).Adj i j ∧ x i=true ∧ x j=true from ⟨a,b,⟨edge,pair⟩,ha,hb⟩)
      simp [yes]
    | true =>
      have on := PEqualNP.Outside.L_meta_2573.eval_mono D dm (pairInput a b) x (by
        intro i hi
        simp only [pairInput,decide_eq_true_eq] at hi
        rcases hi with rfl|rfl <;> assumption) pair
      change circuitFun n D x = true at on
      simp [on]

private theorem finish {n} (D : Circuit) (dm : Monotone2 D) (g : (Fin n → Bool) → Bool) (s : Nat)
    (builder : Bld n (fun _ => True) g s) :
    ∃ A : Circuit, Monotone2 A ∧ A.size ≤ D.size+s+1 ∧
      ∀ x, circuitFun n A x = (circuitFun n D x || g x) := by
  let m := n + D.gates.length
  obtain ⟨gs,o,legal,budget,earlier,ev,_⟩ := builder m (by simp [m])
  let top := m+gs.length
  let port := if D.output < m then D.output else top+1
  let gate : Gate := ⟨.or,[port,o]⟩
  let A : Circuit := ⟨(D.gates++gs)++[gate],top⟩
  refine ⟨A,?_,?_,?_⟩
  · intro h mem
    change h ∈ (D.gates ++ gs) ++ [gate] at mem
    rcases List.mem_append.mp mem with e|e
    · rcases List.mem_append.mp e with q|q
      · exact dm h q
      · obtain ⟨op,ar⟩ := legal.1 h q
        exact ⟨op,ar.le⟩
    · obtain rfl := List.mem_singleton.mp e
      simp [gate]
  · simp [A,Circuit.size] at budget ⊢
    omega
  · intro x
    let w := D.wires (List.ofFn x)
    have wl : w.length = m := by change (wiresFrom _ _).length = _; simp [length_wiresFrom,m]
    let v := wiresFrom gs w
    have vl : v.length=top := by simp [v,top,length_wiresFrom,wl]
    have inputs : (fun i : Fin n => w.getD i.val false) = x := by
      funext i
      change (wiresFrom D.gates (List.ofFn x)).getD i.val false = x i
      rw [getD_wiresFrom _ _ _ (by simp),getD_ofFn]
    have gr : v.getD o false = g x := (ev w wl).trans (congrArg g inputs)
    have dr : v.getD port false = circuitFun n D x := by
      by_cases h : D.output < m
      · simp only [port,ite_eq_left h]
        exact getD_wiresFrom gs w D.output (wl.symm ▸ h)
      · simp only [port,ite_eq_right h]
        change v.getD (top+1) false = w.getD D.output false
        rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
    change (wiresFrom ((D.gates++gs)++[gate]) (List.ofFn x)).getD top false = _
    rw [wiresFrom_append,wiresFrom_append]
    change (v ++ [gate.op.eval (gate.inputs.map (fun i => v.getD i false))]).getD top false = _
    rw [← vl,getD_snoc_eq]
    change (v.getD port false || (v.getD o false || false)) = _
    rw [dr,gr,Bool.or_false]

/-- Restoring the genuinely lost edges gives a physical full-input circuit, even when
the surviving circuit has invalid wire references or uses the removed gates at many readers. -/
theorem patch {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit)
    (dm : Monotone2 D) (down : ∀ x, circuitFun n D x = true → graphFun G ∅ x = true)
    (T : Finset (Fin n)) (cover : IsVertexCover (loss G D) T) :
    ∃ A : Circuit, Monotone2 A ∧ circuitFun n A = graphFun G ∅ ∧
      A.size ≤ D.size + (loss G D).edgeFinset.card + T.card := by
  classical
  let F := loss G D
  by_cases nonempty : F.edgeFinset.Nonempty
  · have coverE : ∀ e ∈ F.edgeFinset, ∃ t ∈ T, t ∈ e := by
      intro e
      refine Sym2.ind (fun a b => ?_) e
      intro edge
      have ab : F.Adj a b := by simpa using edge
      rcases cover a b ab with aT|bT
      · exact ⟨a,aT,Sym2.mem_mk_left ..⟩
      · exact ⟨b,bT,Sym2.mem_mk_right ..⟩
    have builder := bld_edges n (fun _ => True) T F.edgeFinset nonempty coverE (fun _ _ => True.intro)
    obtain ⟨A,am,size,sem⟩ := finish D dm _ _ builder
    have div (x : Fin n → Bool) : decide (∃ e ∈ F.edgeFinset, ∀ v ∈ e, x v = true) = graphFun F ∅ x := by
      simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or]
      apply decide_eq_decide.mpr
      constructor
      · rintro ⟨e,he,on⟩
        revert he on
        refine Sym2.ind (fun a b => ?_) e
        intro he on
        exact ⟨a,b,by simpa using he,on a (Sym2.mem_mk_left ..),on b (Sym2.mem_mk_right ..)⟩
      · rintro ⟨a,b,e,ha,hb⟩
        refine ⟨s(a,b),by simpa using e,?_⟩
        intro v hv
        rcases Sym2.mem_iff.mp hv with rfl|rfl <;> assumption
    refine ⟨A,am,funext (fun x => ?_),?_⟩
    · rw [sem,div]
      exact loss_completion G D dm down x
    · have pos := Finset.card_pos.mpr nonempty
      change A.size ≤ D.size + F.edgeFinset.card + T.card
      omega
  · have emp : F.edgeFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp nonempty
    refine ⟨D,dm,funext (fun x => ?_),by omega⟩
    have zero : graphFun F ∅ x = false := by
      have absent (a b) : ¬ F.Adj a b := fun adj => by
        have e : s(a,b) ∈ F.edgeFinset := by simpa using adj
        simp [emp] at e
      simp [graphFun,absent]
    have r := loss_completion G D dm down x
    simpa only [show graphFun (loss G D) ∅ x = false from zero,Bool.or_false] using r

/-- Global expansion on every adaptive collection of erased gate positions.
A minimum circuit cannot spare more gates than a star cover of the genuinely lost edges costs. -/
theorem batch_bound {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (least : IsMinimalMonoCircuit n C) (correct : circuitFun n C = graphFun G ∅)
    (ks : List Nat) (ok : valid C.size ks) :
    ks.length ≤ (loss G (cut n C ks)).edgeFinset.card + Loc.tau (loss G (cut n C ks)) := by
  let D := cut n C ks
  obtain ⟨dm,sz,down⟩ := cut_spec C least.1 ks ok
  obtain ⟨T,cover,card⟩ := Loc.tau_attained (loss G D)
  obtain ⟨A,am,sem,bound⟩ := patch G D dm (fun x h => (congrFun correct x) ▸ down x h) T cover
  have lower := least.2 A am (sem.trans correct.symm)
  change D.size + ks.length = C.size at sz
  change ks.length ≤ (loss G D).edgeFinset.card + Loc.tau (loss G D)
  omega

#print axioms batch_bound
end VertexPeel.BatchExchange
