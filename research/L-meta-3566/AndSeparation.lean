import ReusedRows

namespace VertexPeel.AndSeparation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.Core
open VertexPeel.ZeroFold VertexPeel.RowCharge VertexPeel.RowGraph VertexPeel.ReusedCone VertexPeel.ReusedRows

variable {n : ℕ} (C : Circuit)

/-- An AND that can be kept false on each input only by choosing opposite children. -/
def opposing (x y : Fin n → Bool) (j : ℕ) : Prop :=
  isAnd C j ∧ wval C x (in0 C j) ≠ wval C y (in0 C j) ∧
    wval C x (in0 C j) = wval C y (in1 C j) ∧
    wval C x (in1 C j) = wval C y (in0 C j)

/-- If a wire rejects x and y but accepts a probe contained in their union,
its physical cone contains an oppositely oriented AND. -/
theorem opposing_ancestor (hc : IsAO2 n C) (x y z : Fin n → Bool)
    (cover : ∀ i, z i = true → x i = true ∨ y i = true) (w : ℕ)
    (hx : wval C x w = false) (hy : wval C y w = false) (hz : wval C z w = true) :
    ∃ j, Reaches n C w (n+j) ∧ opposing C x y j := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w < n
    · let i : Fin n := ⟨w,raw⟩
      rcases cover i ((wval_in C z i) ▸ hz) with h|h
      · exact ((Bool.false_ne_true <| hx.symm.trans ((wval_in C x i).trans h))).elim
      · exact ((Bool.false_ne_true <| hy.symm.trans ((wval_in C y i).trans h))).elim
    by_cases past : n+C.size ≤ w
    · rw [wval_past C z w past] at hz
      contradiction
    let j := w-n
    have hj : j < C.gates.length := by dsimp [j]; change ¬ n+C.gates.length ≤ w at past; omega
    have eq : w = n+j := by dsimp [j]; omega
    obtain ⟨a,b,ab,ha,hb,op⟩ := two n C hc j hj
    have descend (k : ℕ) (hk : k < n+j) (side : k = a ∨ k = b)
        (xo : wval C x k = false) (yo : wval C y k = false) (zo : wval C z k = true) :
        ∃ i, Reaches n C w (n+i) ∧ opposing C x y i := by
      obtain ⟨i,path,h⟩ := ih k (by omega) xo yo zo
      have step : Reads n C w k := ⟨j,hj,eq,by simpa [gateAt_eq C j hj,ab] using side⟩
      exact ⟨i,(Relation.ReflTransGen.single step).trans path,h⟩
    rcases op with hand|hor
    · rw [eq,wval_and C x j a b hj ab ha hb hand] at hx
      rw [eq,wval_and C y j a b hj ab ha hb hand] at hy
      rw [eq,wval_and C z j a b hj ab ha hb hand,Bool.and_eq_true] at hz
      by_cases fa : wval C x a = false ∧ wval C y a = false
      · exact descend a ha (Or.inl rfl) fa.1 fa.2 hz.1
      by_cases fb : wval C x b = false ∧ wval C y b = false
      · exact descend b hb (Or.inr rfl) fb.1 fb.2 hz.2
      refine ⟨j,eq ▸ Relation.ReflTransGen.refl,⟨hj,by simpa [gateAt_eq C j hj] using hand⟩,?_⟩
      simp only [in0,in1,gateAt_eq C j hj,ab,List.getD_cons_zero,List.getD_cons_succ]
      cases ax : wval C x a <;> cases bx : wval C x b <;>
        cases ay : wval C y a <;> cases by' : wval C y b <;> simp_all
    · rw [eq,wval_or C x j a b hj ab ha hb hor,Bool.or_eq_false_iff] at hx
      rw [eq,wval_or C y j a b hj ab ha hb hor,Bool.or_eq_false_iff] at hy
      rw [eq,wval_or C z j a b hj ab ha hb hor,Bool.or_eq_true] at hz
      exact hz.elim (descend a ha (Or.inl rfl) hx.1 hy.1) (descend b hb (Or.inr rfl) hx.2 hy.2)

noncomputable def andCone (w : ℕ) : Finset ℕ := by
  classical
  exact (cone n C w C.size).filter (isAnd C)

noncomputable def signature (w : ℕ) (x : Fin n → Bool) : Finset ℕ :=
  (andCone (n := n) C w).filter fun j => wval C x (in0 C j) = true

/-- Pairwise union-separable zeroes inject into the bit patterns of the actual cone's ANDs. -/
theorem pattern_bound {ι : Type*} (hc : IsAO2 n C) (w : ℕ) (U : Finset ι) (test : ι → Fin n → Bool)
    (off : ∀ i ∈ U, wval C (test i) w = false)
    (sep : ∀ i ∈ U, ∀ j ∈ U, i ≠ j → ∃ z, wval C z w = true ∧
      ∀ v, z v = true → test i v = true ∨ test j v = true) :
    U.card ≤ 2 ^ (andCone (n := n) C w).card := by
  classical
  rw [← Finset.card_powerset]
  apply Finset.card_le_card_of_injOn (fun u => signature C w (test u))
  · intro u _
    exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  · intro u hu v hv eq
    by_contra ne
    obtain ⟨z,hz,cover⟩ := sep u hu v hv ne
    obtain ⟨j,path,hand,diff,_⟩ := opposing_ancestor C hc (test u) (test v) z cover w (off u hu) (off v hv) hz
    have mem : j ∈ andCone (n := n) C w := Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hand.1,path⟩,hand⟩
    have same : wval C (test u) (in0 C j) = true ↔ wval C (test v) (in0 C j) = true := by
      change signature C w (test u) = signature C w (test v) at eq
      have same := Finset.ext_iff.mp eq j
      simpa [signature,mem] using same
    exact diff (Bool.eq_iff_iff.mpr same)

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (R : Finset (Fin n))

/-- If a gate splits k different rows, the AND gates in its cone encode k distinct bit patterns. -/
theorem splitting_rows_bound (hc : IsAO2 n C) (four : NoFourCycle G) (U : Finset (Fin n))
    (right : ∀ u ∈ U, G.neighborFinset u ⊆ R) (j : ℕ) (split : ∀ u ∈ U, j ∈ rowGates G R C u) :
    U.card ≤ 2 ^ (andCone (n := n) C (n+j)).card := by
  classical
  apply pattern_bound C hc (n+j) U (rowBase G R) (fun u hu => (Finset.mem_filter.mp (split u hu)).2.2.1)
  intro u hu v hv ne
  obtain ⟨a,b,ha,hb,distinct⟩ := split_pair G R C hc u j (split u hu)
  have outside : ∃ t ∈ seen G C u (n+j), ¬ G.Adj v t := by
    by_contra! inc
    let T := Finset.univ.filter (fun i => G.Adj u i ∧ G.Adj v i)
    have incl (i : Fin n) (hi : i ∈ seen G C u (n+j)) : i ∈ T :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(G.mem_neighborFinset u i).mp (Finset.mem_filter.mp hi).1,inc i hi⟩
    exact distinct (Finset.card_le_one.mp (four u v ne) _ (incl a ha) _ (incl b hb))
  obtain ⟨t,st,nonedge⟩ := outside
  refine ⟨pairInput u t,(Finset.mem_filter.mp st).2,?_⟩
  intro i on
  rcases (show i = u ∨ i = t by simpa [pairInput] using on) with rfl|rfl
  · exact Or.inl (by simp [rowBase])
  · exact Or.inr (by simp [rowBase,right u hu (Finset.mem_filter.mp st).1,nonedge])

end VertexPeel.AndSeparation
