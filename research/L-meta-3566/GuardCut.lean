import Normalization
import ZeroFold
import PEqualNP.Outside.L_meta_2573

namespace VertexPeel.GuardCut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.ReadTwo PEqualNP.TopForm PEqualNP.MetaComplexity.CoverPromise
open VertexPeel.ZeroFold

private def blank : Gate := ⟨.or,[]⟩

private noncomputable def edit (keep : ℕ → Prop) (j : ℕ) (g : Gate) : Gate := by
  classical
  exact if g.op = .and ∧ ¬keep j then blank else g

noncomputable def mask (C : Circuit) (keep : ℕ → Prop) : Circuit :=
  ⟨C.gates.mapIdx (edit keep), C.output⟩

@[simp] private theorem len (C : Circuit) (K : ℕ → Prop) : (mask C K).gates.length = C.gates.length := by
  simp [mask]

private theorem at_mask (C : Circuit) (K) {j} (hj : j < C.gates.length) :
    (mask C K).gates[j]'(by simpa using hj) = edit K j C.gates[j] := by simp [mask]

theorem same_node {n : ℕ} (C : Circuit) (K : ℕ → Prop) (x : Fin n → Bool)
    {j a b} (hj : j < C.gates.length) (ports : C.gates[j].inputs = [a,b])
    (ha : a < n+j) (hb : b < n+j) (keep : ¬(C.gates[j].op = .and ∧ ¬K j)) :
    wval (mask C K) x (n+j) = C.gates[j].op.eval [wval (mask C K) x a,wval (mask C K) x b] := by
  have hit := at_mask C K hj
  simp only [edit,ite_eq_right keep] at hit
  rw [wval_gate _ x j a b (by simpa using hj) (hit.symm ▸ ports) ha hb,hit]

private theorem dead_node {n : ℕ} (C : Circuit) (K : ℕ → Prop) (x : Fin n → Bool)
    {j} (hj : j < C.gates.length) (del : C.gates[j].op = .and ∧ ¬ K j) :
    wval (mask C K) x (n+j) = false := by
  obtain ⟨P,h,_⟩ := run_new sB (List.ofFn x) (mask C K).gates false j (by simpa using hj)
  rw [List.length_ofFn] at h
  change (run sB (List.ofFn x) (mask C K).gates).getD (n+j) false = false
  rw [h,at_mask C K hj]
  simp [edit,del,sB,blank,GateOp.eval]

theorem legal {n : ℕ} (C : Circuit) (ao : IsAO2 n C) (K : ℕ → Prop) : Monotone2 (mask C K) := by
  intro g mem
  obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp mem
  have idx : j < C.gates.length := by simpa using hj
  rw [at_mask C K idx]
  by_cases e : C.gates[j].op = .and ∧ ¬K j
  · simp [edit,e,blank]
  · simp only [edit,ite_eq_right e]
    exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ao.1 _ (List.getElem_mem idx),
      (ao.2.2 _ (List.getElem_mem idx)).le⟩

/-- Opening fewer AND gates can only decrease every wire. -/
theorem compare {n : ℕ} (C : Circuit) (ao : IsAO2 n C) {K L : ℕ → Prop}
    (sub : ∀ j, K j → L j) (x : Fin n → Bool) (w : ℕ) :
    wval (mask C K) x w = true → wval (mask C L) x w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro on
    by_cases raw : w<n
    · let i : Fin n := ⟨w,raw⟩
      exact (wval_in _ x i).trans ((wval_in _ x i).symm.trans on)
    by_cases past : n+C.gates.length ≤ w
    · rw [wval_past _ x w (by simpa using past)] at on; contradiction
    obtain ⟨j,rfl⟩ : ∃ j, w=n+j := ⟨w-n,by omega⟩
    have hj : j < C.gates.length := by omega
    obtain ⟨a,b,ports,ha,hb,op⟩ := two n C ao j hj
    by_cases ek : C.gates[j].op = .and ∧ ¬K j
    · rw [dead_node _ _ _ hj ek] at on; contradiction
    have el : ¬(C.gates[j].op=.and ∧ ¬L j) := fun h => ek ⟨h.1,fun hk => h.2 (sub j hk)⟩
    rw [same_node _ _ _ hj ports ha hb ek] at on
    rw [same_node _ _ _ hj ports ha hb el]
    rcases op with o|o
    · simp [o,GateOp.eval] at on ⊢
      exact ⟨ih _ ha on.1,ih _ hb on.2⟩
    · simp [o,GateOp.eval] at on ⊢
      exact on.imp (ih _ ha) (ih _ hb)

theorem unmasked (C : Circuit) : mask C (fun _ => True) = C := by
  cases C with
  | mk gates out =>
    unfold mask
    congr 1
    apply List.ext_getElem
    · simp
    · intro i hi h
      simp [edit]

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
/-- These are precisely the rows inspected by the clean-gate counting theorem. -/
def Small (x : Fin n → Bool) : Prop :=
  x = (fun _ => false) ∨ (∃ u : Fin n, x = fun z => decide (z=u)) ∨
    ∃ u v : Fin n, x = fun z => decide (z=u ∨ z=v)

def Guard (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, Small x → wval C x w = true → graphFun G ∅ x = true

/-- Preserve all original OR paths, retaining exactly those AND gates certified by Guard. -/
noncomputable abbrev guarded := mask C (fun j => Guard G C (n+j))
noncomputable abbrev linearPart (C : Circuit) := mask C (fun _ => False)

def EdgeBoundary (u v : Fin n) : Prop :=
  ∀ j (hj : j < C.gates.length), C.gates[j].op = .and →
    Guard G C (n+j) → wval C (pairInput u v) (n+j) = true →
      ∀ p ∈ C.gates[j].inputs, Guard G C p ∨ wval (linearPart C) (pairInput u v) p = true

def Boundary : Prop := ∀ u v, G.Adj u v → EdgeBoundary G C u v

private theorem lower (ao : IsAO2 n C) (x : Fin n → Bool) (w) :
    wval (guarded G C) x w = true → wval C x w = true := by
  simpa only [unmasked] using compare C ao (K := fun j => Guard G C (n+j)) (L := fun _ => True) (fun _ _ => trivial) x w

theorem guarded_edge (ao : IsAO2 n C) {u v : Fin n} (bd : EdgeBoundary G C u v)
    (w : ℕ) : Guard G C w → wval C (pairInput u v) w = true → wval (guarded G C) (pairInput u v) w = true := by
  let x := pairInput u v
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro gd on
    by_cases raw : w<n
    · let i : Fin n := ⟨w,raw⟩
      exact (wval_in _ x i).trans ((wval_in _ x i).symm.trans on)
    by_cases past : n+C.gates.length ≤ w
    · rw [wval_past _ _ w past] at on; contradiction
    obtain ⟨j,rfl⟩ : ∃ j, w=n+j := ⟨w-n,by omega⟩
    have hj : j < C.gates.length := by omega
    obtain ⟨a,b,ports,ha,hb,op⟩ := two n C ao j hj
    rw [same_node C _ _ hj ports ha hb (fun h => h.2 gd)]
    rcases op with o|o
    · have on' := on
      rw [wval_and C _ _ _ _ hj ports ha hb o,Bool.and_eq_true] at on'
      have port (p) (mem : p ∈ C.gates[j].inputs) (lt : p<n+j) (hit : wval C x p=true) :
          wval (guarded G C) x p=true := by
        rcases bd j hj o gd on p mem with g|l
        · exact ih p lt g hit
        · exact compare C ao (fun _ (h : False) => h.elim) x p l
      simpa [o,GateOp.eval] using
        (And.intro (port a (by simp [ports]) ha on'.1) (port b (by simp [ports]) hb on'.2))
    · have guards : Guard G C a ∧ Guard G C b := by
        constructor <;> intro y hy h <;> apply gd y hy <;> rw [wval_or C _ _ _ _ hj ports ha hb o] <;> simp [h]
      rw [wval_or C _ _ _ _ hj ports ha hb o,Bool.or_eq_true] at on
      simpa [o,GateOp.eval] using on.imp (ih a ha guards.1) (ih b hb guards.2)

theorem correct_of_kept (ao : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅)
    (kept : ∀ u v, G.Adj u v → wval (guarded G C) (pairInput u v) C.output=true) :
    circuitFun n (guarded G C) = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact fun on => (congrFun ok x).symm ▸ lower G C ao x C.output on
  · intro on
    obtain ⟨u,v,edge,hu,hv⟩ : ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true := by simpa [graphFun] using on
    have hit := kept u v edge
    apply PEqualNP.Outside.L_meta_2573.eval_mono (guarded G C) (legal C ao _) _ x _ hit
    intro i hi
    rcases (show i=u ∨ i=v by simpa [pairInput] using hi) with rfl|rfl <;> assumption

theorem correct_mask (ao : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅) (bd : Boundary G C) :
    circuitFun n (guarded G C) = graphFun G ∅ := by
  apply correct_of_kept G C ao ok
  intro u v edge
  have pair : graphFun G ∅ (pairInput u v) = true := by
    simp [graphFun]
    exact ⟨u,v,edge,by simp [pairInput],by simp [pairInput]⟩
  have gd : Guard G C C.output := fun y _ hy => (congrFun ok y).symm.trans hy
  exact guarded_edge G C ao (bd u v edge) C.output gd ((congrFun ok _).trans pair)

/-- Any correct guarded mask certifies the original gate budget. -/
theorem cover_of_correct_mask (ao : IsAO2 n C) (sq : NoFourCycle G)
    (correct : circuitFun n (guarded G C) = graphFun G ∅) :
    ∃ T : Finset (Fin n), IsVertexCover G T ∧ G.edgeFinset.card + T.card ≤ C.size + 1 := by
  let D := guarded G C
  have clean (j : Fin D.gates.length) (x : Fin n → Bool) (small : Small x) (op : (D.gates.get j).op = .and)
      (on : (D.wires (List.ofFn x)).getD (n+j.val) false = true) : graphFun G ∅ x = true := by
    have hi : j.val < C.gates.length := by simpa [D] using j.isLt
    have hg := at_mask C (fun k => Guard G C (n+k)) hi
    change D.gates[j.val].op = .and at op
    rw [hg] at op
    by_cases bad : C.gates[j.val].op = .and ∧ ¬ Guard G C (n+j.val)
    · simp [edit,bad,blank] at op
    · have gd : Guard G C (n+j.val) := by
        simp only [edit,ite_eq_right bad] at op
        by_contra ng
        exact bad ⟨op,ng⟩
      exact gd x small (lower G C ao x _ on)
  have cycle (a b c d : Fin n) (ac : a≠c) (bd' : b≠d) :
      ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
    rintro ⟨ab,bc,cd,da⟩
    exact bd' (Finset.card_le_one.mp (sq a c ac) b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ab,bc.symm⟩)
      d (Finset.mem_filter.mpr ⟨Finset.mem_univ _,da.symm,cd⟩))
  have h := PEqualNP.Outside.L_meta_7241.pairCleanBound n G cycle D.gates D.output
    (fun g hg => by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using legal C ao _ g hg)
    (fun x => by change circuitFun n (guarded G C) x = _; simpa [graphFun] using congrFun correct x)
    (fun j x small op on => by simpa [graphFun] using clean j x small op on)
  simpa [D,guarded,mask,Circuit.size,IsVertexCover] using h
theorem cover_bound (ao : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅) (sq : NoFourCycle G)
    (bd : Boundary G C) :
    ∃ T : Finset (Fin n), IsVertexCover G T ∧ G.edgeFinset.card + T.card ≤ C.size + 1 :=
  cover_of_correct_mask G C ao sq (correct_mask G C ao ok bd)

/-- Every undersized circuit loses an actual edge upon cutting its unsafe AND gates. -/
theorem lost_edge (ao : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅) (sq : NoFourCycle G)
    (short : C.size+1 < G.edgeFinset.card + Loc.tau G) :
    ∃ u v, G.Adj u v ∧ wval (guarded G C) (pairInput u v) C.output=false := by
  by_contra! no
  obtain ⟨T,c,small⟩ := cover_of_correct_mask G C ao sq (correct_of_kept G C ao ok (by
    intro u v edge
    simpa using no u v edge))
  have := Loc.tau_le G T c
  omega
#print axioms lost_edge
#print axioms cover_bound
end VertexPeel.GuardCut
