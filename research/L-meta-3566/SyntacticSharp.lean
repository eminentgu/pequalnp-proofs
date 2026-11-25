import GuardCut
import PEqualNP.Defs.SyntacticMultilinear

namespace VertexPeel.SyntacticSharp
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.ReadTwo PEqualNP.TopForm PEqualNP.MetaComplexity.CoverPromise
  PEqualNP.SyntacticMultilinear
open VertexPeel.ZeroFold VertexPeel.GuardCut

variable {n : ℕ} (C : Circuit)

private def join (R : List (Finset (Fin n))) (g : Gate) :=
  g.inputs.foldr (fun w acc => R.getD w ∅ ∪ acc) ∅

private lemma supp_in (i : Fin n) : support n C i = {i} := by
  change (run join (List.ofFn fun k : Fin n => ({k} : Finset (Fin n))) C.gates).getD i ∅ = _
  rw [run_old _ _ _ _ _ (by simp),List.getD_eq_getElem _ _ (by simp)]
  simp

private lemma supp_node {j a b} (hj : j < C.gates.length) (ports : C.gates[j].inputs = [a,b])
    (ha : a < n+j) (hb : b < n+j) :
    support n C (n+j) = support n C a ∪ support n C b := by
  obtain ⟨P,h,prev⟩ := run_new join (List.ofFn fun k : Fin n => ({k} : Finset (Fin n))) C.gates ∅ j hj
  rw [List.length_ofFn] at h prev
  change (run join _ C.gates).getD (n+j) ∅ = _
  rw [h]
  simp only [join,ports,List.foldr_cons,List.foldr_nil,Finset.union_empty]
  rw [prev a ha,prev b hb]
  rfl

private lemma separated (hm : IsSyntMultilinear n C) {j a b} (hj : j<C.gates.length)
    (ports : C.gates[j].inputs = [a,b]) (ha : a<n+j) (hb : b<n+j) (op : C.gates[j].op=.and) :
    Disjoint (support n C a) (support n C b) := by
  have h := hm j hj (by simpa only [gateAt_eq C j hj] using op)
  simpa [AndOperandsDisjoint,gateAt_eq C j hj,ports,operandSupport,ha,hb] using h

def Active (x : Fin n → Bool) (w : ℕ) (i : Fin n) := i ∈ support n C w ∧ x i=true

/-- Only true AND gates and the active input coordinates of this row are tested. -/
def SeparatedOn (x : Fin n → Bool) : Prop :=
  ∀ j (hj : j<C.gates.length) a b, C.gates[j].inputs = [a,b] →
    C.gates[j].op=.and → wval C x (n+j)=true →
    ∀ i, Active C x a i → Active C x b i → False

private lemma separated_on_of_multilinear (ao : IsAO2 n C) (hm : IsSyntMultilinear n C)
    (x : Fin n → Bool) : SeparatedOn C x := by
  intro j hj a b ports op _ i ai bi
  have back := ao.2.1 j hj
  rw [gateAt_eq C j hj,ports] at back
  exact Finset.disjoint_left.mp (separated C hm hj ports (back a (by simp)) (back b (by simp)) op) ai.1 bi.1

private lemma has_input (ao : IsAO2 n C) (x : Fin n → Bool) (w) :
    wval C x w = true → ∃ i, Active C x w i := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    by_cases raw : w<n
    · let i : Fin n := ⟨w,raw⟩
      exact ⟨i,by change i ∈ support n C i; rw [supp_in C i]; simp,(wval_in C x i).symm.trans h⟩
    by_cases past : n+C.gates.length ≤ w
    · rw [wval_past _ _ w past] at h; contradiction
    obtain ⟨j,rfl⟩ : ∃ j,w=n+j := ⟨w-n,by omega⟩
    have hj : j<C.gates.length := by omega
    obtain ⟨a,b,ports,ha,hb,op⟩ := two n C ao j hj
    have any : wval C x a = true ∨ wval C x b = true := by
      rcases op with o|o
      · rw [wval_and C _ _ _ _ hj ports ha hb o,Bool.and_eq_true] at h; exact Or.inl h.1
      · rwa [wval_or C _ _ _ _ hj ports ha hb o,Bool.or_eq_true] at h
    rcases any with va|vb
    · obtain ⟨i,hi,hit⟩ := ih a ha va
      exact ⟨i,by rw [supp_node C hj ports ha hb]; exact Finset.mem_union_left _ hi,hit⟩
    · obtain ⟨i,hi,hit⟩ := ih b hb vb
      exact ⟨i,by rw [supp_node C hj ports ha hb]; exact Finset.mem_union_right _ hi,hit⟩

/-- A true wire lacking an active OR-only path must see two different active inputs. -/
private lemma linear_or_two (ao : IsAO2 n C) (x : Fin n → Bool) (localSep : SeparatedOn C x) (w) :
    wval C x w = true → wval (linearPart C) x w = true ∨
      ∃ i k, i ≠ k ∧ Active C x w i ∧ Active C x w k := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    by_cases raw : w<n
    · let i : Fin n := ⟨w,raw⟩
      exact Or.inl ((wval_in _ x i).trans ((wval_in C x i).symm.trans h))
    by_cases past : n+C.gates.length ≤ w
    · rw [wval_past _ _ w past] at h; contradiction
    obtain ⟨j,rfl⟩ : ∃ j,w=n+j := ⟨w-n,by omega⟩
    have hj : j<C.gates.length := by omega
    obtain ⟨a,b,ports,ha,hb,op⟩ := two n C ao j hj
    have liftA {i} (h : Active C x a i) : Active C x (n+j) i :=
      ⟨(supp_node C hj ports ha hb) ▸ Finset.mem_union_left _ h.1,h.2⟩
    have liftB {i} (h : Active C x b i) : Active C x (n+j) i :=
      ⟨(supp_node C hj ports ha hb) ▸ Finset.mem_union_right _ h.1,h.2⟩
    rcases op with o|o
    · have live := h
      rw [wval_and C _ _ _ _ hj ports ha hb o,Bool.and_eq_true] at h
      obtain ⟨i,ai⟩ := has_input C ao x a h.1
      obtain ⟨k,bk⟩ := has_input C ao x b h.2
      exact Or.inr ⟨i,k,fun e => localSep j hj a b ports o live i ai (e ▸ bk),
        liftA ai,liftB bk⟩
    · rw [wval_or C _ _ _ _ hj ports ha hb o,Bool.or_eq_true] at h
      have eqn := same_node C (fun _ => False) x hj ports ha hb (by simp [o])
      simp only [o,GateOp.eval] at eqn
      rcases h with va|vb
      · rcases ih a ha va with l|⟨i,k,ne,ai,ak⟩
        · exact Or.inl (by rw [eqn]; simp [l])
        · exact Or.inr ⟨i,k,ne,liftA ai,liftA ak⟩
      · rcases ih b hb vb with l|⟨i,k,ne,bi,bk⟩
        · exact Or.inl (by rw [eqn]; simp [l])
        · exact Or.inr ⟨i,k,ne,liftB bi,liftB bk⟩

private lemma pair_linear (ao : IsAO2 n C) (u v : Fin n) (localSep : SeparatedOn C (pairInput u v)) (a b : ℕ)
    (dis : ∀ i, Active C (pairInput u v) a i → Active C (pairInput u v) b i → False) (va : wval C (pairInput u v) a = true)
    (vb : wval C (pairInput u v) b = true) : wval (linearPart C) (pairInput u v) a = true := by
  rcases linear_or_two C ao _ localSep a va with l|⟨i,k,ne,ai,ak⟩
  · exact l
  obtain ⟨z,bz⟩ := has_input C ao _ b vb
  have mem {t} (ht : pairInput u v t=true) : t=u ∨ t=v := by simpa [pairInput] using ht
  have sepI : i≠z := fun e => dis i ai (e ▸ bz)
  have sepK : k≠z := fun e => dis k ak (e ▸ bz)
  rcases mem ai.2 with h|h <;> rcases mem ak.2 with g|g <;> rcases mem bz.2 with f|f <;> grind

theorem boundary_of_separated_edges (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ao : IsAO2 n C) (sep : ∀ u v, G.Adj u v → SeparatedOn C (pairInput u v)) : Boundary G C := by
  intro u v edge j hj op _ on p hp
  obtain ⟨a,b,ports,ha,hb,_⟩ := two n C ao j hj
  have localSep := sep u v edge
  have dis := localSep j hj a b ports op on
  rw [wval_and C _ _ _ _ hj ports ha hb op,Bool.and_eq_true] at on
  rcases (show p=a ∨ p=b by simpa [ports] using hp) with rfl|rfl
  · exact Or.inr (pair_linear C ao u v localSep _ _ dis on.1 on.2)
  · exact Or.inr (pair_linear C ao u v localSep _ _ (fun i hi hk => dis i hk hi) on.2 on.1)

theorem boundary_of_multilinear (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ao : IsAO2 n C) (hm : IsSyntMultilinear n C) : Boundary G C :=
  boundary_of_separated_edges C G ao (fun _ _ _ => separated_on_of_multilinear C ao hm _)

/-- A violation forces an actual edge on which a firing AND reuses a live endpoint. -/
theorem collision_of_short (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ao : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅) (sq : NoFourCycle G)
    (short : C.size + 1 < G.edgeFinset.card + Loc.tau G) :
    ∃ u v, G.Adj u v ∧ ∃ (j : ℕ) (hj : j<C.gates.length) (a b : ℕ),
      C.gates[j].inputs=[a,b] ∧ C.gates[j].op=.and ∧ wval C (pairInput u v) (n+j)=true ∧
      ∃ i, (i=u ∨ i=v) ∧ i ∈ support n C a ∧ i ∈ support n C b := by
  classical
  by_contra! no
  have sep : ∀ u v, G.Adj u v → SeparatedOn C (pairInput u v) := by
    intro u v adj j hj a b ports op live i ai bi
    exact no u v adj j hj a b ports op live i (by simpa [pairInput] using ai.2) ai.1 bi.1
  obtain ⟨T,c,b⟩ := cover_bound G C ao ok sq (boundary_of_separated_edges C G ao sep)
  have m := Loc.tau_le G T c
  omega

/-- Sharp total gate lower bound for syntactically multilinear binary circuits on C4-free graphs. -/
theorem cover_bound_multilinear (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ao : IsAO2 n C) (hm : IsSyntMultilinear n C) (ok : circuitFun n C = graphFun G ∅)
    (sq : NoFourCycle G) :
    ∃ T : Finset (Fin n), IsVertexCover G T ∧ G.edgeFinset.card + T.card ≤ C.size + 1 :=
  cover_bound G C ao ok sq (boundary_of_multilinear C G ao hm)
#print axioms collision_of_short
#print axioms cover_bound_multilinear
end VertexPeel.SyntacticSharp
