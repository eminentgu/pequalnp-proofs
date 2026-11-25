import PrivateReaderWidth
import PhysicalWitnessWidth
import SingletonOrCone

namespace VertexPeel.LocalReaders
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadTwo
open VertexPeel.ZeroFold VertexPeel.RowGraph VertexPeel.SideReaders VertexPeel.WrongSupports
open PEqualNP.Outside.L615Aux.Wires (point)
open VertexPeel.AndSeparation
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

/-- At a sole OR reader in a cleaned circuit, its other operand already needs
at least degree(a)-1 distinct physical AND gates in its own subcircuit. -/
theorem exclusive_or_ands (sq : NoFourCycle G) (ao : IsAO2 n C) (ok : circuitFun n C=graphFun G ∅)
    (normal : OrClosed G C) (a : Fin n) (r : ℕ) (hr : r<C.gates.length)
    (unique : ∀ k (hk : k<C.gates.length), a.val∈C.gates[k].inputs → k=r)
    (d : ℕ) (other : d≠a.val) (back : d<n+r) (op : C.gates[r].op=.or)
    (ports : C.gates[r].inputs=[a.val,d] ∨ C.gates[r].inputs=[d,a.val]) :
    G.degree a ≤ (andCone (n:=n) C d).card+1 :=
  exclusive_or_width G C sq ao ok normal a r hr unique d other back op ports (width_of_and_cone C ao d)

/-- At a sole AND reader, the other operand accepts each individual neighbor.
This direction does not require square-freeness or a normalized minimum. -/
theorem exclusive_and_neighbors (ao : IsAO2 n C) (ok : circuitFun n C=graphFun G ∅)
    (a : Fin n) (r : ℕ) (hr : r<C.gates.length)
    (unique : ∀ k (hk : k<C.gates.length), a.val∈C.gates[k].inputs → k=r)
    (d : ℕ) (other : d≠a.val) (back : d<n+r) (op : C.gates[r].op=.and)
    (ports : C.gates[r].inputs=[a.val,d] ∨ C.gates[r].inputs=[d,a.val]) :
    ∀ t, G.Adj a t → Active C d {t} := by
  classical
  intro t edge
  let X : Finset (Fin n) := {a,t}
  let Y : Finset (Fin n) := {t}
  have same (v : Fin n) (h : v≠a) : point X v=point Y v := by simp [point,X,Y,h]
  have diff : wval C (point X) C.output ≠ wval C (point Y) C.output := by
    change circuitFun n C _ ≠ circuitFun n C _
    rw [ok]
    have pos : graphFun G ∅ (point X)=true := by
      apply (pair_iff G a t).mpr edge
    have neg : graphFun G ∅ (point Y)≠true := by
      intro h
      apply G.loopless.irrefl t
      apply (pair_iff G t t).mp
      change graphFun G ∅ (point {t,t})=true
      simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self t)] using h
    exact fun e => neg (e ▸ pos)
  obtain ⟨k,hk,⟨v,hv,read⟩,changeAt⟩ := changed_reader C ao (point X) (point Y) {a}
    (fun v hv => same v (by simpa using hv)) diff (fun v _ => no_raw_output G ok v)
  have ve : v=a := Finset.mem_singleton.mp hv
  have kr := unique k hk (ve ▸ read)
  have eval (Z : Finset (Fin n)) : wval C (point Z) (n+r)=(point Z a && wval C (point Z) d) := by
    rcases ports with p|p
    · rw [wval_and _ _ _ _ _ hr p (by omega) back op,wval_in C _ a]
    · rw [wval_and _ _ _ _ _ hr p back (by omega) op,wval_in C _ a,Bool.and_comm]
  rw [kr,eval,eval] at changeAt
  have dx : wval C (point X) d=true := by simpa [point,X,Y,edge.ne] using changeAt
  have skip (k) (hk : k<C.gates.length) (early : k<r) (t) (read : t∈C.gates[k].inputs) : t∉({a.val}:Finset ℕ) := by
    intro mem
    have e := Finset.mem_singleton.mp mem
    exact (Nat.ne_of_lt early) (unique k hk (e ▸ read))
  have equal := prefix_agree C ao {a.val} r skip (point X) (point Y)
    (fun v h => same v (by intro eq; exact h (eq ▸ Finset.mem_singleton_self _))) d back (by simpa using other)
  exact equal.symm.trans dx

/-- Distinct centers have at most one common neighbor in a square-free graph.
This bounds the loss when one operand is shared by several private AND readers. -/
theorem neighborhood_union (sq : NoFourCycle G) (A : Finset (Fin n)) :
    ∑ a∈A, G.degree a ≤ (A.biUnion (fun v => G.neighborFinset v)).card + A.card.choose 2 := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A fresh ih =>
    let N := G.neighborFinset a
    let U := A.biUnion (fun v => G.neighborFinset v)
    have small (b) (hb : b∈A) : (N ∩ G.neighborFinset b).card ≤ 1 := by
      have ab : a≠b := fun e => fresh (e ▸ hb)
      apply (Finset.card_le_card _).trans (sq a b ab)
      intro v hv
      obtain ⟨u,w⟩ := Finset.mem_inter.mp hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(G.mem_neighborFinset _ _).mp u,(G.mem_neighborFinset _ _).mp w⟩
    have cover : N ∩ U ⊆ A.biUnion (fun b => N ∩ G.neighborFinset b) := by
      intro v hv
      obtain ⟨left,right⟩ := Finset.mem_inter.mp hv
      obtain ⟨b,hb,hit⟩ := Finset.mem_biUnion.mp right
      exact Finset.mem_biUnion.mpr ⟨b,hb,Finset.mem_inter.mpr ⟨left,hit⟩⟩
    have inter : (N∩U).card ≤ A.card := calc
      _ ≤ _ := Finset.card_le_card cover
      _ ≤ ∑ b∈A, (N ∩ G.neighborFinset b).card := Finset.card_biUnion_le
      _ ≤ ∑ _b∈A, 1 := Finset.sum_le_sum small
      _ = _ := by simp
    have merge := Finset.card_union_add_card_inter N U
    have size : N.card=G.degree a := G.card_neighborFinset_eq_degree a
    rw [Finset.sum_insert fresh,Finset.biUnion_insert,Finset.card_insert_of_notMem fresh,Nat.choose_succ_succ' _ 1,Nat.choose_one_right]
    change G.degree a+(∑ b∈A, G.degree b) ≤ (N∪U).card+(A.card+A.card.choose 2)
    change _ ≤ U.card+A.card.choose 2 at ih
    omega

/-- The variable's sole occurrence is an AND with the specified other wire. -/
def SoleAndOperand (a : Fin n) (d : ℕ) : Prop :=
  ∃ (r : ℕ) (hr : r<C.gates.length), (∀ k (hk : k<C.gates.length), a.val∈C.gates[k].inputs → k=r) ∧
    d≠a.val ∧ d<n+r ∧ C.gates[r].op=.and ∧
    (C.gates[r].inputs=[a.val,d] ∨ C.gates[r].inputs=[d,a.val])

/-- All neighbors of all centers with one common operand must reach that
operand through its physical OR gates. This counts a shared gate only once. -/
theorem shared_operand_ors (ao : IsAO2 n C) (ok : circuitFun n C=graphFun G ∅)
    (A : Finset (Fin n)) (d : ℕ) (guard : ∀ a∈A, SoleAndOperand C a d) :
    (A.biUnion (fun v => G.neighborFinset v)).card ≤ (RowCharge.orAncestors n C d).card+1 := by
  apply RowCharge.singleton_or_ancestors C ao
  intro t ht
  obtain ⟨a,ha,mem⟩ := Finset.mem_biUnion.mp ht
  obtain ⟨r,hr,unique,other,back,op,ports⟩ := guard a ha
  have on := exclusive_and_neighbors G C ao ok a r hr unique d other back op ports t
    ((G.mem_neighborFinset a t).mp mem)
  have singleton : point {t}=(fun i => decide (i=t)) := by funext i; simp [point]
  change wval C (point {t}) d=true at on
  exact singleton ▸ on

/-- If one wire feeds the sole AND readers of several variables, its OR cost
pays the sum of their degrees up to at most one overlap per pair of centers. -/
theorem shared_operand_degrees (sq : NoFourCycle G) (ao : IsAO2 n C) (ok : circuitFun n C=graphFun G ∅)
    (A : Finset (Fin n)) (d : ℕ) (guard : ∀ a∈A, SoleAndOperand C a d) :
    (∑ a∈A, G.degree a) ≤ (RowCharge.orAncestors n C d).card+1+A.card.choose 2 :=
  (neighborhood_union G sq A).trans (Nat.add_le_add_right (shared_operand_ors G C ao ok A d guard) _)

theorem exclusive_and_ors (ao : IsAO2 n C) (ok : circuitFun n C=graphFun G ∅)
    (a : Fin n) (d : ℕ) (guard : SoleAndOperand C a d) : G.degree a ≤ (RowCharge.orAncestors n C d).card+1 := by
  simpa using shared_operand_ors G C ao ok {a} d (by simpa using guard)

#print axioms shared_operand_ors
#print axioms shared_operand_degrees
#print axioms exclusive_and_ors

#print axioms neighborhood_union

#print axioms exclusive_or_ands
#print axioms exclusive_and_neighbors
end VertexPeel.LocalReaders
