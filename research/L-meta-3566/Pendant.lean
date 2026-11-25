import Leaves

namespace VertexPeel.Leaves

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.CoverPromise PEqualNP.TopForm PEqualNP.ReadK
open CoverCircuit ZeroFold SidePeel SideReaders

private theorem hasReader {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a u : Fin n) (edge : G.Adj u a) (C : Circuit) (ao : IsAO2 n C)
    (correct : circuitFun n C = graphFun G ∅) :
    ∃ j, ∃ hj : j < C.gates.length, a.val ∈ C.gates[j].inputs := by
  obtain ⟨x,y,agree,diff⟩ := sensitive G C correct edge
  obtain ⟨j,hj,_,t,ht,reads⟩ := crosses C ao {a.val} x y
    (by intro b hb; exact agree b (fun eq => hb (by simp [eq]))) diff
    (by simpa using no_raw_output G correct a)
  exact ⟨j,hj,Finset.mem_singleton.mp ht ▸ reads⟩

private theorem twoSavings {n : ℕ} (C : Circuit) (ao : IsAO2 n C) (Z : Finset (Fin n))
    (j k : ℕ) (hj : j < C.size) (hk : k < C.size) (ne : j ≠ k)
    (mj : ¬ Mg C Z j) (mk : ¬ Mg C Z k) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = fv C Z C.output ∧ D.size + 2 ≤ C.size := by
  classical
  let F := (Finset.range C.size).filter (Mg C Z)
  have sub : insert j (insert k F) ⊆ Finset.range C.size := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Finset.mem_range.mpr hj
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Finset.mem_range.mpr hk
    exact (Finset.mem_filter.mp hi).1
  have counted := Finset.card_le_card sub
  simp [F,ne,mj,mk] at counted
  obtain ⟨D,d,s,c⟩ := ZeroFold.compile C ao Z
  exact ⟨D,d,s,by omega⟩

-- When both vertices are essential, zeroing the two saves two gates if an edge survives.
theorem twoInputs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : Fin n) (edge : G.Adj a b) (other : ∃ u v, G.Adj u v ∧ u ≠ a ∧ u ≠ b ∧ v ≠ a ∧ v ≠ b)
    (C : Circuit) (ao : IsAO2 n C) (correct : circuitFun n C = graphFun G ∅) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = fv C {a,b} C.output ∧ D.size + 2 ≤ C.size := by
  classical
  let Z : Finset (Fin n) := {a,b}
  obtain ⟨j,hj,rj⟩ := hasReader G a b edge.symm C ao correct
  obtain ⟨k,hk,rk⟩ := hasReader G b a edge C ao correct
  have za : fv C Z a.val = fun _ => false := fv_in0 C Z a (by simp [Z])
  have zb : fv C Z b.val = fun _ => false := fv_in0 C Z b (by simp [Z])
  have mj := kill C ao Z j hj a.val rj za
  by_cases ne : j ≠ k
  · exact twoSavings C ao Z j k hj hk ne mj (kill C ao Z k hk b.val rk zb)
  have same := not_ne_iff.mp ne
  subst k
  obtain ⟨u,v,inputs,hu,hv,op⟩ := two n C ao j hj
  have ha : a.val = u ∨ a.val = v := by simpa [inputs] using rj
  have hb : b.val = u ∨ b.val = v := by simpa [inputs] using rk
  have diffab : a.val ≠ b.val := fun e => edge.ne (Fin.ext e)
  have zeros : (fv C Z u = fun _ => false) ∧ (fv C Z v = fun _ => false) := by
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact False.elim (diffab (ha.trans hb.symm))
    · exact ⟨ha ▸ za,hb ▸ zb⟩
    · exact ⟨hb ▸ zb,ha ▸ za⟩
    · exact False.elim (diffab (ha.trans hb.symm))
  have off : fv C Z (n+j) = fun _ => false := by
    funext x
    rcases op with op | op
    · rw [fv_and C Z j u v hj inputs hu hv op,zeros.1,zeros.2]
      rfl
    · rw [fv_or C Z j u v hj inputs hu hv op,zeros.1,zeros.2]
      rfl
  obtain ⟨s,t,st,sa,sb,ta,tb⟩ := other
  have residual : fv C Z C.output ≠ fun _ => false := by
    intro e
    have h := congrFun e (bits {s,t})
    have fixed : zr Z (bits {s,t}) = bits {s,t} := by
      funext i
      by_cases hia : i = a
      · subst i
        simp [zr,Z,bits,sa.symm,ta.symm]
      by_cases hib : i = b
      · subst i
        simp [zr,Z,bits,sb.symm,tb.symm]
      simp [zr,Z,hia,hib]
    change circuitFun n C (zr Z (bits {s,t})) = false at h
    rw [fixed,correct,(pair_iff G s t).mpr st] at h
    cases h
  have distinct : C.output ≠ n+j := fun e => residual (e ▸ off)
  obtain ⟨x,y,eq,different⟩ := sensitive G C correct edge.symm
  obtain ⟨l,hl,out,w,hw,read⟩ := crosses C ao {a.val,n+j} x y (by
    intro i hi
    apply eq
    rintro rfl
    simp at hi) different (by simp [no_raw_output G correct a,distinct])
  have lj : j ≠ l := by rintro rfl; simp at out
  have wz : fv C Z w = fun _ => false := by
    rcases Finset.mem_insert.mp hw with e | e
    · exact e ▸ za
    · exact (Finset.mem_singleton.mp e) ▸ off
  exact twoSavings C ao Z j l hj hl lj mj (kill C ao Z l hl w read wz)

theorem isolatedEdgeAt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : Fin n) (adj : G.Adj a b) (onlyA : ∀ v, G.Adj a v → v = b)
    (onlyB : ∀ v, G.Adj b v → v = a) (edges : 2 ≤ G.edgeFinset.card) :
    0 < G.degree a ∧ ∀ C : Circuit, IsAO2 n C →
      circuitFun n C = graphFun G ∅ → SavesAt G a C := by
  classical
  have single : G.neighborFinset a = {b} := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_singleton]
    exact ⟨onlyA v,fun e => e ▸ adj⟩
  have deg : G.degree a = 1 := by
    change (G.neighborFinset a).card = 1
    rw [single,Finset.card_singleton]
  have other : ∃ u v, G.Adj u v ∧ u ≠ a ∧ u ≠ b ∧ v ≠ a ∧ v ≠ b := by
    have rem : 0 < (G.deleteIncidenceSet a).edgeFinset.card := by
      rw [G.card_edgeFinset_deleteIncidenceSet,deg]; omega
    obtain ⟨e,he⟩ := Finset.card_pos.mp rem
    revert he
    refine Sym2.ind (fun u v => ?_) e
    intro he
    have h : (G.deleteIncidenceSet a).Adj u v := by simpa using he
    obtain ⟨huv,ua,va⟩ := SimpleGraph.deleteIncidenceSet_adj.mp h
    exact ⟨u,v,huv,ua,fun e => va (onlyB v (e ▸ huv)),va,fun e => ua (onlyB u (e ▸ huv.symm))⟩
  refine ⟨by omega,?_⟩
  intro C ao cor
  obtain ⟨D,d,ev,bound⟩ := twoInputs G a b adj other C ao cor
  have same : fv C {a,b} C.output = fv C {a} C.output := by
    funext x
    change circuitFun n C (zr {a,b} x) = circuitFun n C (zr {a} x)
    rw [cor]
    simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or]
    apply decide_eq_decide.mpr
    simp only [zr,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨u,v,h,hu,hv⟩
      refine ⟨u,v,h,?_,?_⟩
      · by_cases ua : u = a <;> by_cases ub : u = b <;> simp_all
      · by_cases va : v = a <;> by_cases vb : v = b <;> simp_all
    · rintro ⟨u,v,h,hu,hv⟩
      have ua : u ≠ a := by rintro rfl; simp at hu
      have va : v ≠ a := by rintro rfl; simp at hv
      have ub : u ≠ b := fun eq => va (onlyB v (eq ▸ h))
      have vb : v ≠ b := fun eq => ua (onlyB u (eq ▸ h.symm))
      exact ⟨u,v,h,by simpa [ua,ub] using hu,by simpa [va,vb] using hv⟩
  exact ⟨D,d,ev.trans (same.trans (restrict_correct G C cor a)),by omega,fun _ => by omega⟩

theorem isolatedEdge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : Fin n) (adj : G.Adj a b) (onlyA : ∀ v, G.Adj a v → v = b)
    (onlyB : ∀ v, G.Adj b v → v = a) (edges : 2 ≤ G.edgeFinset.card) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C →
      circuitFun n C = graphFun G ∅ → SavesAt G z C :=
  ⟨a, isolatedEdgeAt G a b adj onlyA onlyB edges⟩

end VertexPeel.Leaves

#print axioms VertexPeel.Leaves.twoInputs
#print axioms VertexPeel.Leaves.isolatedEdge
