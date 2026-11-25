import LocalReaders
import PortTransversal
import WrongSupportCircuit

namespace VertexPeel.LocalReaders
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadTwo
open VertexPeel.ZeroFold VertexPeel.RowGraph VertexPeel.SideReaders VertexPeel.WrongSupports
open PEqualNP.Outside.L615Aux.Wires (point)

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

/-- An independent set activating the only reader of a missing variable must
block every neighbor of that variable. Otherwise adding an unblocked neighbor
and then the variable changes the answer while the sole reader stays true. -/
theorem sole_reader_blocks (ao : IsAO2 n C) (ok : circuitFun n C=graphFun G ∅)
    (a : Fin n) (r : ℕ) (unique : ∀ k (hk : k<C.gates.length), a.val∈C.gates[k].inputs → k=r)
    (I : Finset (Fin n)) (indep : ∀ u∈I, ∀ v∈I, ¬G.Adj u v)
    (onI : wval C (point I) (n+r)=true) :
    ∀ t, G.Adj a t → ∃ y∈I, G.Adj y t := by
  classical
  intro t at'
  by_contra! avoid
  let J := insert t I
  let K := insert a J
  have noEdge : ¬∃ u v, G.Adj u v ∧ point J u=true ∧ point J v=true := by
    rintro ⟨u,v,uv,hu,hv⟩
    simp only [point,decide_eq_true_eq,J,Finset.mem_insert] at hu hv
    rcases hu with rfl|hu <;> rcases hv with rfl|hv
    · exact (G.loopless.irrefl _) uv
    · exact avoid _ hv uv.symm
    · exact avoid _ hu uv
    · exact indep _ hu _ hv uv
  have different : wval C (point J) C.output ≠ wval C (point K) C.output := by
    change circuitFun n C _ ≠ circuitFun n C _
    rw [ok]
    have neg : graphFun G ∅ (point J)=false := by simp [graphFun,noEdge]
    have pos : graphFun G ∅ (point K)=true := by
      simp [graphFun]
      exact ⟨a,t,at',by simp [K,point],by simp [K,J,point]⟩
    rw [neg,pos]; decide
  obtain ⟨k,hk,⟨v,hv,read⟩,changeAt⟩ := changed_reader C ao (point J) (point K) {a}
    (by
      intro v hv
      have h : v≠a := by simpa using hv
      simp [K,point,h]) different (fun v _ => no_raw_output G ok v)
  have ve : v=a := Finset.mem_singleton.mp hv
  have kr := unique k hk (ve ▸ read)
  have onJ := active_mono C ao (n+r) (Finset.subset_insert t I) onI
  have onK := active_mono C ao (n+r) (Finset.subset_insert a J) onJ
  exact changeAt (kr ▸ onJ.trans onK.symm)

/-- A square-free graph forces at least degree(a) active inputs in every
independent certificate for the sole reader that excludes a. -/
theorem sole_reader_width (sq : NoFourCycle G) (ao : IsAO2 n C) (ok : circuitFun n C=graphFun G ∅)
    (a : Fin n) (r : ℕ) (unique : ∀ k (hk : k<C.gates.length), a.val∈C.gates[k].inputs → k=r)
    (I : Finset (Fin n)) (absent : a∉I) (indep : ∀ u∈I, ∀ v∈I, ¬G.Adj u v)
    (onI : wval C (point I) (n+r)=true) : G.degree a ≤ I.card := by
  by_contra! small
  obtain ⟨t,adj,avoid⟩ := NeighborPorts.unblocked G sq I a absent small
  obtain ⟨v,hv,block⟩ := sole_reader_blocks G C ao ok a r unique I indep onI t adj
  exact avoid v hv block

/-- Any AND-depth bound on a sole reader that already lights on an independent
input excluding a limits the degree of a, regardless of fanout. -/
theorem sole_reader_depth (sq : NoFourCycle G) (ao : IsAO2 n C) (ok : circuitFun n C=graphFun G ∅)
    (a : Fin n) (r : ℕ) (unique : ∀ k (hk : k<C.gates.length), a.val∈C.gates[k].inputs → k=r)
    (I : Finset (Fin n)) (absent : a∉I) (indep : ∀ u∈I, ∀ v∈I, ¬G.Adj u v)
    (onI : Active C (n+r) I) {d : ℕ} (depth : AndDepth n C (n+r) d) : G.degree a ≤ 2^d := by
  obtain ⟨W,sub,bound,active⟩ := width_of_andDepth C ao depth I onI
  exact (sole_reader_width G C sq ao ok a r unique W (fun h => absent (sub h))
    (fun x hx y hy => indep x (sub hx) y (sub hy)) active).trans bound

/-- The other operand of an exclusive OR in a cleaned circuit accepts some
independent input without a. Every such input must guard all neighbors of a. -/
theorem exclusive_or_guard (ao : IsAO2 n C) (ok : circuitFun n C=graphFun G ∅)
    (normal : OrClosed G C) (a : Fin n) (r : ℕ) (hr : r<C.gates.length)
    (unique : ∀ k (hk : k<C.gates.length), a.val∈C.gates[k].inputs → k=r)
    (d : ℕ) (other : d≠a.val) (back : d<n+r) (op : C.gates[r].op=.or)
    (ports : C.gates[r].inputs=[a.val,d] ∨ C.gates[r].inputs=[d,a.val]) :
    (∃ I : Finset (Fin n), a∉I ∧ (∀ u∈I, ∀ v∈I, ¬G.Adj u v) ∧ Active C d I) ∧
    (∀ I : Finset (Fin n), (∀ u∈I, ∀ v∈I, ¬G.Adj u v) → Active C d I →
      ∀ t, G.Adj a t → ∃ y∈I, G.Adj y t) := by
  classical
  have act (x : Fin n → Bool) (hit : x a=true ∨ wval C x d=true) : wval C x (n+r)=true := by
    rcases ports with p|p
    · rw [wval_or C x r a.val d hr p (by omega) back op,wval_in C x a,Bool.or_eq_true]; exact hit
    · rw [wval_or C x r d a.val hr p back (by omega) op,wval_in C x a,Bool.or_eq_true]; exact hit.symm
  have rd : d∈C.gates[r].inputs := by rcases ports with p|p <;> simp [p]
  constructor
  · have unsound : ¬∀ x : Fin n → Bool, wval C x d=true → graphFun G ∅ x=true := by
      intro safe
      have on := normal r hr op d rd safe (bits {a,a}) (act _ (Or.inl (by simp [bits])))
      exact (G.loopless.irrefl _) ((pair_iff G a a).mp on)
    push Not at unsound
    obtain ⟨x,hit,negative⟩ := unsound
    let I := Finset.univ.filter fun v => v≠a ∧ x v=true
    refine ⟨I,by simp [I],?_,?_⟩
    · intro u hu v hv uv
      apply negative
      simp [graphFun]
      exact ⟨u,v,uv,(Finset.mem_filter.mp hu).2.2,(Finset.mem_filter.mp hv).2.2⟩
    · have skip (k) (hk : k<C.gates.length) (early : k<r) (t) (read : t∈C.gates[k].inputs) : t∉({a.val}:Finset ℕ) := by
        intro mem
        have same := Finset.mem_singleton.mp mem
        exact (Nat.ne_of_lt early) (unique k hk (same ▸ read))
      have equal := prefix_agree C ao {a.val} r skip x (point I) (by
        intro v hv
        have ne : v≠a := by intro eq; exact hv (eq ▸ Finset.mem_singleton_self _)
        cases val : x v <;> simp [point,I,ne,val]) d back (by simpa using other)
      exact equal.symm.trans hit
  · intro I indep onI
    exact sole_reader_blocks G C ao ok a r unique I indep (act _ (Or.inr onI))

/-- The width of the other operand of an exclusive OR in a cleaned circuit is
at least the variable's degree, even when the circuit shares arbitrary wires. -/
theorem exclusive_or_width (sq : NoFourCycle G) (ao : IsAO2 n C) (ok : circuitFun n C=graphFun G ∅)
    (normal : OrClosed G C) (a : Fin n) (r : ℕ) (hr : r<C.gates.length)
    (unique : ∀ k (hk : k<C.gates.length), a.val∈C.gates[k].inputs → k=r)
    (d : ℕ) (other : d≠a.val) (back : d<n+r) (op : C.gates[r].op=.or)
    (ports : C.gates[r].inputs=[a.val,d] ∨ C.gates[r].inputs=[d,a.val])
    {k : ℕ} (width : WitnessWidth (Active (n:=n) C d) k) : G.degree a ≤ k := by
  obtain ⟨⟨I,absent,indep,onI⟩,blocks⟩ := exclusive_or_guard G C ao ok normal a r hr unique d other back op ports
  obtain ⟨W,sub,bound,onW⟩ := width I onI
  by_contra! tooFew
  obtain ⟨t,adj,avoid⟩ := NeighborPorts.unblocked G sq W a (fun h => absent (sub h)) (by omega)
  obtain ⟨v,hv,block⟩ := blocks W (fun x hx y hy => indep x (sub hx) y (sub hy)) onW t adj
  exact avoid v hv block

#print axioms exclusive_or_guard
#print axioms exclusive_or_width

#print axioms sole_reader_blocks
#print axioms sole_reader_width
#print axioms sole_reader_depth
end VertexPeel.LocalReaders
