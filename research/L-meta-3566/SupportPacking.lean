import BatchExchange
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Sort

namespace VertexPeel.BatchExchange

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.MetaComplexity.CoverPromise PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2668 (bypass bypass_mono bypass_length bypass_val_lt bypass_eval_eq val_ge gateAt_mem)

theorem sorted_valid {s : Nat} {ks : List Nat} (order : ks.Pairwise (· > ·))
    (inside : ∀ i ∈ ks, i<s) : valid s ks := by
  induction ks generalizing s with
  | nil => trivial
  | cons k ks ih =>
    obtain ⟨lt,descending⟩ := List.pairwise_cons.mp order
    have hk := inside k (List.mem_cons_self ..)
    refine ⟨hk,ih descending ?_⟩
    intro i hi
    have := lt i hi
    omega

/-- Erasing gates in decreasing order preserves the output on each assignment
where every erased gate was false in the original, unmodified circuit. -/
theorem cut_off {n : Nat} (C : Circuit) (mono : Monotone2 C) (ks : List Nat)
    (order : ks.Pairwise (· > ·)) (inside : ∀ i ∈ ks, i<C.size) (x : Fin n → Bool)
    (off : ∀ i ∈ ks, gateVal n C i x = false) : circuitFun n (cut n C ks) x = circuitFun n C x := by
  induction ks generalizing C with
  | nil => rfl
  | cons k ks ih =>
    obtain ⟨before,sort⟩ := List.pairwise_cons.mp order
    have hk := inside k (List.mem_cons_self ..)
    let D := bypass n C k (n+C.size)
    have size : D.size = C.size-1 := bypass_length ..
    have same : circuitFun n D x = circuitFun n C x := by
      apply bypass_eval_eq (n:=n) (by simp) (fun j hj => (mono _ (gateAt_mem hj)).1) hk (Or.inr le_rfl)
      exact (off k (List.mem_cons_self ..)).trans (val_ge (n:=n) (by simp) le_rfl).symm
    apply Eq.trans _ same
    apply ih D (bypass_mono mono) sort
    · intro i hi
      have := before i hi
      omega
    · intro i hi
      have lt := before i hi
      have eq := bypass_val_lt (n:=n) (C:=C) (i:=n+C.size) (x:=List.ofFn x) (by simp) hk (n+i) (by omega)
      exact eq.trans (off i (List.mem_cons_of_mem _ hi))

def row {n} (e : Sym2 (Fin n)) (v : Fin n) : Bool := decide (v ∈ e)

theorem row_mk {n : Nat} (a b : Fin n) : row s(a,b) = pairInput a b := by
  funext v
  simp [row,pairInput,Sym2.mem_iff]

/-- Original graph edges on which the selected gate is true. -/
def support {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (i : Fin C.size) :=
  G.edgeFinset.filter (fun e => gateVal n C i.val (row e) = true)

private def endpoints {n : Nat} (T : Finset (Fin n)) (E : Finset (Sym2 (Fin n))) :=
  T.filter fun v => ∃ e ∈ E, v ∈ e

/-- Original gates firing only on F satisfy a Hall-type expansion bound, without
testing the circuit again after each deletion or assuming a private fan-out. -/
theorem union_bound {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (least : IsMinimalMonoCircuit n C) (correct : circuitFun n C = graphFun G ∅)
    (T : Finset (Fin n)) (cover : IsVertexCover G T) (S : Finset (Fin C.size)) :
    S.card ≤ (S.biUnion (support G C)).card +
      (endpoints T (S.biUnion (support G C))).card := by
  classical
  let U := S.image Fin.val
  let ks := U.sort (· ≥ ·)
  have order : ks.Pairwise (· > ·) := U.sortedGT_sort.pairwise
  have member (j) : j ∈ ks ↔ ∃ i ∈ S, Fin.val i = j := by simp only [ks,Finset.mem_sort,U,Finset.mem_image]
  have inside (j) (hj : j ∈ ks) : j < C.size := by
    obtain ⟨i,_,rfl⟩ := (member j).mp hj
    exact i.isLt
  have ksize : ks.length=S.card := by simp [ks,U,Finset.card_image_of_injective _ Fin.val_injective]
  let D := cut n C ks
  let F := loss G D
  let E := S.biUnion (support G C)
  have inc : F.edgeFinset ⊆ E := by
    intro e
    refine Sym2.ind (fun a b => ?_) e
    intro hab
    have hadj : F.Adj a b := by simpa using hab
    by_contra absent
    have off (i : Nat) (hi : i ∈ ks) : gateVal n C i (pairInput a b) = false := by
      obtain ⟨j,hj,rfl⟩ := (member i).mp hi
      apply Bool.eq_false_iff.mpr
      intro on
      apply absent (Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_filter.mpr ⟨by simpa using hadj.1, (row_mk a b).symm ▸ on⟩⟩)
    have eq := cut_off C least.1 ks order inside (pairInput a b) off
    have yes : circuitFun n C (pairInput a b) = true := by
      rw [correct]
      simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq]
      exact ⟨a,b,hadj.1,by simp [pairInput],by simp [pairInput]⟩
    exact Bool.noConfusion (hadj.2.symm.trans (eq.trans yes))
  have covers : IsVertexCover F (endpoints T E) := by
    intro a b ab
    have e : s(a,b) ∈ E := inc (by simpa using ab)
    exact (cover a b ab.1).imp (fun h => Finset.mem_filter.mpr ⟨h,_,e,Sym2.mem_mk_left ..⟩)
      (fun h => Finset.mem_filter.mpr ⟨h,_,e,Sym2.mem_mk_right ..⟩)
  have bound := batch_bound G C least correct ks (sorted_valid order inside)
  change ks.length ≤ F.edgeFinset.card + Loc.tau F at bound
  rw [ksize] at bound
  exact bound.trans (Nat.add_le_add (Finset.card_le_card inc) (Loc.tau_le F _ covers))

/-- A gate gets either an edge where it fires, or a cover vertex incident to such
an edge. All chosen resources are distinct, simultaneously across the whole minimum circuit. -/
theorem global_assignment {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (least : IsMinimalMonoCircuit n C) (correct : circuitFun n C = graphFun G ∅)
    (T : Finset (Fin n)) (cover : IsVertexCover G T) :
    ∃ f : Fin C.size → Sym2 (Fin n) ⊕ Fin n, Function.Injective f ∧
      ∀ j, (∃ e ∈ support G C j, f j = Sum.inl e) ∨
        ∃ v ∈ T, (∃ e ∈ support G C j, v ∈ e) ∧ f j = Sum.inr v := by
  classical
  let edges := support G C
  let options (j : Fin C.size) := (edges j).disjSum (endpoints T (edges j))
  have expand (S : Finset (Fin C.size)) : S.card ≤ (S.biUnion options).card := by
    have bound := union_bound G C least correct T cover S
    let E := S.biUnion edges
    have eq : E.disjSum (endpoints T E) ⊆ S.biUnion options := by
      intro q hq
      rcases Finset.mem_disjSum.mp hq with ⟨e,he,rfl⟩|⟨v,hv,rfl⟩
      · obtain ⟨j,hj,act⟩ := Finset.mem_biUnion.mp he
        exact Finset.mem_biUnion.mpr ⟨j,hj,Finset.inl_mem_disjSum.mpr act⟩
      · obtain ⟨inT,e,he,inc⟩ := Finset.mem_filter.mp hv
        obtain ⟨j,hj,act⟩ := Finset.mem_biUnion.mp he
        exact Finset.mem_biUnion.mpr ⟨j,hj,Finset.inr_mem_disjSum.mpr (Finset.mem_filter.mpr ⟨inT,e,act,inc⟩)⟩
    exact bound.trans ((Finset.card_disjSum ..) ▸ Finset.card_le_card eq)
  obtain ⟨f,inj,valid⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' options).mp expand
  refine ⟨f,inj,?_⟩
  intro j
  rcases Finset.mem_disjSum.mp (valid j) with ⟨e,he,eq⟩|⟨v,hv,eq⟩
  · exact Or.inl ⟨e,he,eq.symm⟩
  · obtain ⟨t,inc⟩ := Finset.mem_filter.mp hv
    exact Or.inr ⟨v,t,inc,eq.symm⟩

#print axioms cut_off
#print axioms union_bound
#print axioms global_assignment
end VertexPeel.BatchExchange
