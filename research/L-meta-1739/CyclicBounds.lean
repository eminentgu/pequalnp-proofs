import LeafCharge
import PEqualNP.Outside.L_meta_217
import PEqualNP.Outside.L_meta_4837

namespace Research.CyclicBounds

open SimpleGraph Research.LeafCharge PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4837_aux
open GraphCircuit4837
open scoped Classical

def NoSquare {n} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)

theorem noSquareOfDesk {n} {G : SimpleGraph (Fin n)}
    (h : ∀ a b c d, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) : NoSquare G := by
  rintro a b c d ac bd ⟨ab,bc,cd,da⟩
  exact h a b c d ab.ne ac da.ne.symm bc.ne bd cd.ne ab bc cd da

theorem noSquareWalk {n} {G : SimpleGraph (Fin n)} (h : NoSquare G) :
    GraphInduction4837.noFour G := by
  intro v w hc len
  have distinct (i j : ℕ) (hi : i<4) (hj : j<4) (hne : i≠j) : w.getVert i ≠ w.getVert j := by
    intro e
    apply hne
    exact hc.getVert_injOn' (show i ≤ w.length-1 by omega) (show j ≤ w.length-1 by omega) e
  have adj (i : ℕ) (hi : i<4) := w.adj_getVert_succ (show i < w.length by omega)
  apply h _ _ _ _ (distinct 0 2 (by decide) (by decide) (by decide))
    (distinct 1 3 (by decide) (by decide) (by decide))
  refine ⟨adj 0 (by decide),adj 1 (by decide),adj 2 (by decide),?_⟩
  simpa [← len] using (show G.Adj (w.getVert 3) (w.getVert 4) from adj 3 (by decide))

def coverFloor {n} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∀ S : Finset (Fin n), CoverPromise.IsVertexCover G S → k ≤ S.card

private theorem floorDelete {n} {G : SimpleGraph (Fin n)} {k : ℕ} (p : Fin n)
    (floor : coverFloor G k) : coverFloor (G.deleteIncidenceSet p) (k-1) := by
  intro S hS
  have cov : CoverPromise.IsVertexCover G (insert p S) := by
    intro i j hij
    by_cases hi : i=p
    · simp [hi]
    by_cases hj : j=p
    · simp [hj]
    have := hS i j (G.deleteIncidenceSet_adj.mpr ⟨hij,hi,hj⟩)
    simpa [hi,hj] using this
  have := floor _ cov
  have := Finset.card_insert_le p S
  omega

theorem gateIndices (gs : List Gate) :
    ∃ A : Finset ℕ, A ⊆ Finset.range gs.length ∧ A.card = ands gs ∧
    ∀ j g, gs[j]? = some g → (j ∈ A ↔ isAnd g.op = true) := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨∅,by simp, rfl,by simp⟩
  | append_singleton gs g ih =>
    obtain ⟨A,sub,card,mem⟩ := ih
    have fresh : gs.length ∉ A := fun h => Nat.lt_irrefl _ (Finset.mem_range.mp (sub h))
    use if isAnd g.op then insert gs.length A else A
    constructor
    · intro i hi
      simp only [List.length_append,List.length_singleton,Finset.mem_range]
      split at hi
      · rcases Finset.mem_insert.mp hi with rfl|h
        · omega
        · have := Finset.mem_range.mp (sub h); omega
      · have := Finset.mem_range.mp (sub hi); omega
    constructor
    · cases h : isAnd g.op <;> simp [h,ands,fresh] <;> exact card
    · intro j q hj
      by_cases lt : j < gs.length
      · rw [List.getElem?_append_left lt] at hj
        cases h : isAnd g.op <;> simp [Nat.ne_of_lt lt,mem j q hj]
      · have bound := (List.getElem?_eq_some_iff.mp hj).1
        simp at bound
        have : j = gs.length := by omega
        subst j
        simp at hj
        subst q
        cases h : isAnd g.op <;> simp [fresh]

theorem leafRestriction {n} {G : SimpleGraph (Fin n)} {C : Circuit} {l p : Fin n}
    (lp : G.Adj l p) (leaf : ∀ i, G.Adj l i → i=p) (hm : Monotone2 C) (hs : detects G C) :
    ∃ D : Circuit, Monotone2 D ∧ ands D.gates < ands C.gates ∧ detects (G.deleteIncidenceSet p) D := by
  let a := fun i : Fin n => decide (i=p)
  let b := fun i : Fin n => decide (i=l ∨ i=p)
  have hd (i : Fin n) : a i ≠ b i → i=l := by
    contrapose!
    intro hl
    simp [a,b,hl]
  have ha : C.eval (List.ofFn a) = false := by
    rw [Bool.eq_false_iff]
    rintro h
    obtain ⟨i,j,hij,hi,hj⟩ := (hs a).mp h
    exact hij.ne ((of_decide_eq_true hi).trans (of_decide_eq_true hj).symm)
  have hb : C.eval (List.ofFn b) = true := (hs b).mpr ⟨l,p,lp,by simp [b],by simp [b]⟩
  have spec (x : Fin n → Bool) : C.eval (List.ofFn (pin l p x)) = true ↔
      ∃ i j, (G.deleteIncidenceSet p).Adj i j ∧ x i = true ∧ x j = true := by
    rw [hs]
    have hp : pin l p x p = false := by simp [pin,lp.ne.symm]
    constructor
    · rintro ⟨i,j,hij,hi,hj⟩
      have ip : i≠p := by rintro rfl; simp [hp] at hi
      have jp : j≠p := by rintro rfl; simp [hp] at hj
      have il : i≠l := by rintro rfl; exact jp (leaf j hij)
      have jl : j≠l := by rintro rfl; exact ip (leaf i hij.symm)
      exact ⟨i,j,G.deleteIncidenceSet_adj.mpr ⟨hij,ip,jp⟩,by simpa [pin,il,ip] using hi,
        by simpa [pin,jl,jp] using hj⟩
    · rintro ⟨i,j,e,hi,hj⟩
      obtain ⟨hij,ip,jp⟩ := G.deleteIncidenceSet_adj.mp e
      have il : i≠l := by rintro rfl; exact jp (leaf j hij)
      have jl : j≠l := by rintro rfl; exact ip (leaf i hij.symm)
      exact ⟨i,j,hij,by simpa [pin,il,ip] using hi,by simpa [pin,jl,jp] using hj⟩
  obtain ⟨D,hmD,lt,eval⟩ := restrictAnd C l p hm a b hd (by simp [ha,hb])
    ⟨fun _ => false,by rw [Bool.eq_false_iff]; simp [spec]⟩
  exact ⟨D,hmD,lt,fun x => (eval x ▸ spec x)⟩

/-- Each step isolates the neighbour of a leaf by deleting all its incident edges. -/
inductive LeafCore {n} : SimpleGraph (Fin n) → Prop where
  | small (G) (S : Finset (Fin n)) (cov : CoverPromise.IsVertexCover G S) (bound : S.card ≤ 5) :
      LeafCore G
  | peel {G : SimpleGraph (Fin n)} (l p : Fin n) (edge : G.Adj l p)
      (leaf : ∀ i, G.Adj l i → i = p) (next : LeafCore (G.deleteIncidenceSet p)) : LeafCore G

theorem andBound {n} {G : SimpleGraph (Fin n)} (core : LeafCore G) (hf : NoSquare G)
    {k : ℕ} (floor : coverFloor G k) (C : Circuit) (hm : Monotone2 C) (hs : detects G C) :
    k ≤ ands C.gates := by
  induction core generalizing C k with
  | small G S cov bound =>
    obtain ⟨A,_,size,mem⟩ := gateIndices C.gates
    rw [←size]
    apply PEqualNP.Outside.L_meta_217 n k G C ((floor S cov).trans bound) hf floor hm hs A
    intro j g hj op
    exact (mem j g hj).mpr (by simp [op,isAnd])
  | @peel G l p lp leaf next ih =>
    obtain ⟨D,hmD,lt,hsD⟩ := leafRestriction lp leaf hm hs
    have small := ih (fun a b c d ac bd e => hf a b c d ac bd
      ⟨(G.deleteIncidenceSet_adj.mp e.1).1, (G.deleteIncidenceSet_adj.mp e.2.1).1,
       (G.deleteIncidenceSet_adj.mp e.2.2.1).1, (G.deleteIncidenceSet_adj.mp e.2.2.2).1⟩)
      (floorDelete p floor) D hmD hsD
    omega

theorem totalBound {n} {G : SimpleGraph (Fin n)} (core : LeafCore G) (hf : NoSquare G)
    (sparse : GraphInduction4837.sparse G) {k : ℕ} (floor : coverFloor G k)
    (C : Circuit) (hm : Monotone2 C) (hs : detects G C) :
    G.edgeSet.ncard + k ≤ C.size + 1 := by
  obtain ⟨A,sub,size,mem⟩ := gateIndices C.gates
  have a := andBound core hf floor C hm hs
  have o := PEqualNP.Outside.L_meta_4837 n G C (Finset.range C.gates.length \ A) sparse
    (noSquareWalk hf) hm hs (by
      intro j g hj op
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_range.mpr (List.getElem?_eq_some_iff.mp hj).1,?_⟩
      intro m
      have bad := (mem j g hj).mp m
      simp [op,isAnd] at bad)
  rw [Finset.card_sdiff_of_subset sub, Finset.card_range] at o
  have cardle := Finset.card_le_card sub
  rw [Finset.card_range] at cardle
  change G.edgeSet.ncard + k ≤ C.gates.length + 1
  omega

end Research.CyclicBounds
