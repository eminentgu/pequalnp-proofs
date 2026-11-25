import Pseudoforest

namespace VertexPeel.OrderedMatching

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.Core PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_1774 PEqualNP.MetaComplexity.CoverPromise
open VertexPeel.AndSeparation VertexPeel.RowGraph VertexPeel.RowCharge VertexPeel.CoverCircuit

variable {n k : ℕ}

/-- Each accepted union of two rejected inputs forces an AND with opposite input
ports. If the first input of each pair lies below both inputs of every later pair,
a monotone wire cannot switch orientation a second time. -/
theorem staircase (C : Circuit) (ao : IsAO2 n C) (w : ℕ)
    (x y z : Fin k → Fin n → Bool)
    (offX : ∀ i, wval C (x i) w = false) (offY : ∀ i, wval C (y i) w = false)
    (on : ∀ i, wval C (z i) w = true)
    (union : ∀ i v, z i v = true → x i v = true ∨ y i v = true)
    (chain : ∀ i j, i < j → ∀ v, x i v = true → x j v = true ∧ y j v = true) :
    k ≤ (andCone (n:=n) C w).card := by
  classical
  have find (i : Fin k) := opposing_ancestor C ao (x i) (y i) (z i) (union i) w (offX i) (offY i) (on i)
  choose J path prop using find
  have diff (i j : Fin k) (ij : i < j) : J i ≠ J j := by
    intro eq
    obtain ⟨_,ne,cross,other⟩ := prop i
    obtain ⟨_,ne',cross',other'⟩ := prop j
    rw [← eq] at ne' cross' other'
    have someOn : wval C (x i) (in0 C (J i)) = true ∨ wval C (x i) (in1 C (J i)) = true := by
      rw [other]
      cases h : wval C (x i) (in0 C (J i)) <;> cases g : wval C (y i) (in0 C (J i)) <;> simp_all
    have persist (u : ℕ) (hu : wval C (x i) u = true) :
        wval C (x j) u = true ∧ wval C (y j) u = true :=
      ⟨wire_mono C ao (fun v hv => (chain i j ij v hv).1) _ hu,
       wire_mono C ao (fun v hv => (chain i j ij v hv).2) _ hu⟩
    rcases someOn with ha|hb
    · obtain ⟨p,q⟩ := persist _ ha
      exact ne' (p.trans q.symm)
    · obtain ⟨p,q⟩ := persist _ hb
      exact ne' ((cross'.trans q).trans (other'.symm.trans p).symm)
  have incl (i : Fin k) : J i ∈ andCone (n:=n) C w :=
    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (prop i).1.1,path i⟩,(prop i).1⟩
  have count := Finset.card_le_card_of_injOn (s:=Finset.univ) J (fun i _ => incl i) (by
    intro i _ j _ eq
    rcases lt_trichotomy i j with h|h|h
    · exact (diff i j h eq).elim
    · exact h
    · exact (diff j i h eq.symm).elim)
  simpa using count

/-- A matching ordered so that each later right endpoint misses every earlier left endpoint.
The right endpoints need not constitute an independent set. -/
def Witness (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ a b : Fin k → Fin n, (∀ i, G.Adj (a i) (b i)) ∧
    (∀ i j, ¬ G.Adj (a i) (a j)) ∧ (∀ i j, i < j → ¬G.Adj (a i) (b j))

theorem and_lower (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : Witness G k) (C : Circuit) (ao : IsAO2 n C) (correct : circuitFun n C = graphFun G ∅) :
    k ≤ (andCone (n:=n) C C.output).card := by
  classical
  obtain ⟨a,b,edge,ind,ord⟩ := h
  let x (i : Fin k) (v : Fin n) : Bool := decide (∃ r ≤ i, a r=v)
  let y (i : Fin k) (v : Fin n) : Bool := decide (v = b i ∨ ∃ r < i, a r=v)
  let z (i : Fin k) (v : Fin n) : Bool := decide (v = a i ∨ v = b i)
  have eval (p : Fin n → Bool) : wval C p C.output = graphFun G ∅ p := congrFun correct p
  apply staircase C ao C.output x y z
  · intro i
    rw [eval]
    have off : ¬ ∃ u v, G.Adj u v ∧ x i u = true ∧ x i v = true := by
      rintro ⟨u,v,uv,hu,hv⟩
      obtain ⟨p,_,rfl⟩ := of_decide_eq_true hu
      obtain ⟨q,_,rfl⟩ := of_decide_eq_true hv
      exact ind p q uv
    simp [graphFun,off]
  · intro i
    rw [eval]
    have off : ¬ ∃ u v, G.Adj u v ∧ y i u = true ∧ y i v = true := by
      rintro ⟨u,v,uv,hu,hv⟩
      rcases of_decide_eq_true hu with rfl|⟨p,hp,rfl⟩ <;>
        rcases of_decide_eq_true hv with rfl|⟨q,hq,rfl⟩
      · exact uv.ne rfl
      · exact ord q i hq uv.symm
      · exact ord p i hp uv
      · exact ind p q uv
    simp [graphFun,off]
  · intro i
    rw [eval]
    have e : ∃ u v, G.Adj u v ∧ z i u = true ∧ z i v = true :=
      ⟨a i,b i,edge i,by simp [z],by simp [z]⟩
    simp [graphFun,e]
  · intro i v hv
    rcases of_decide_eq_true hv with rfl|rfl
    · exact Or.inl (decide_eq_true ⟨i,le_rfl,rfl⟩)
    · exact Or.inr (decide_eq_true (Or.inl rfl))
  · intro i j lt v hv
    obtain ⟨r,ri,eq⟩ := of_decide_eq_true hv
    exact ⟨decide_eq_true ⟨r,ri.trans lt.le,eq⟩,decide_eq_true (Or.inr ⟨r,lt_of_le_of_lt ri lt,eq⟩)⟩

private theorem no_four_walk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (sq : NoFourCycle G)
    (v : Fin n) (w : G.Walk v v) (cy : w.IsCycle) : w.length ≠ 4 := by
  intro len
  obtain ⟨c⟩ := (SimpleGraph.cycleGraph_isContained_iff (by decide : 2 < 4)).2 ⟨v,w,cy,len⟩
  have adj (a b : Fin 4) (ab : (SimpleGraph.cycleGraph 4).Adj a b) : G.Adj (c a) (c b) :=
    c.toHom.map_rel' ab
  have ac := fun h => (by decide : (0 : Fin 4) ≠ 2) (c.injective h)
  have ne := fun h => (by decide : (1 : Fin 4) ≠ 3) (c.injective h)
  exact ne (Finset.card_le_one.mp (sq (c 0) (c 2) ac) (c 1)
    (by simp [adj 0 1 (by decide),adj 2 1 (by decide)]) (c 3)
    (by simp [adj 0 3 (by decide),adj 2 3 (by decide)]))

theorem numerical {n k : ℕ} (G : SimpleGraph (Fin n)) [base : DecidableRel G.Adj]
    (sq : NoFourCycle G) (sparse : Pseudoforest.Sparse G) (witness : Witness G k) :
    StableExtension.Numerical G k := by
  intro inst C mono correct
  have same : inst=base := Subsingleton.elim _ _
  subst inst
  classical
  have zero : circuitFun n C (fun _ => false) = false :=
    (congrFun correct _).trans (by simp [graphFun])
  obtain ⟨E,ao,smaller,same⟩ := PEqualNP.Outside.L_meta_4342 n C mono zero
  have ec := same.trans correct
  let A := andCone (n := n) E E.output
  have andBound : k ≤ A.card := and_lower G witness E ao ec
  have sub : A ⊆ Finset.range E.size := by
    intro i h
    have hand := (Finset.mem_filter.mp h).2
    exact Finset.mem_range.mpr hand.1
  let rest := Finset.range E.size \ A
  have reads (j : ℕ) (g : Gate) (atj : E.gates[j]? = some g) (hor : g.op = .or) : j ∈ rest := by
    obtain ⟨hj,rfl⟩ := List.getElem?_eq_some_iff.mp atj
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hj,?_⟩
    intro h
    have hand := (Finset.mem_filter.mp (show j ∈ (andCone (n := n) E E.output) from h)).2
    have op := hand.2
    change (gateAt E j).op = .and at op
    simp [gateAt,hj,hor] at op
  have em : Monotone2 E := fun g hg =>
    ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ao.1 g hg,(ao.2.2 g hg).le⟩
  have eval (x : Fin n → Bool) : E.eval (List.ofFn x) = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    have hh := congrFun ec x
    change E.eval (List.ofFn x) = graphFun G ∅ x at hh
    simp [hh,graphFun]
  have eb := PEqualNP.Outside.L_meta_599 n G E rest sparse (no_four_walk G sq) em eval reads
  have cardE : G.edgeSet.ncard = G.edgeFinset.card := by rw [← SimpleGraph.coe_edgeFinset,Set.ncard_coe_finset]
  have remaining := Finset.card_sdiff_add_card_eq_card sub
  change rest.card + A.card = _ at remaining
  rw [Finset.card_range] at remaining
  omega

/-- A witness at the minimum cover number pays for the full ownership exchange. -/
theorem ownership {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (sq : NoFourCycle G) (sparse : Pseudoforest.Sparse G) (witness : Witness G (Loc.tau G)) : StepAt G := by
  intro C minimum correct _ positive
  obtain ⟨S,c,sc⟩ := Loc.tau_attained G
  have bound := numerical G sq sparse witness C minimum.1 correct
  apply coveredDescent G C S c _ positive
  rw [Set.ncard_eq_toFinset_card']
  change G.edgeFinset.card + S.card - 1 ≤ C.size
  omega

/-- The selected vertex works on every correct circuit, even when disjoint parts share gates. -/
theorem vertex_deletion {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (sq : NoFourCycle G) (sparse : Pseudoforest.Sparse G) (witness : Witness G (Loc.tau G))
    (edges : 2 ≤ G.edgeFinset.card) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C →
      circuitFun n C = graphFun G ∅ → SavesAt G z C := by
  obtain ⟨z,hz,rem⟩ := nonemptyCut G edges
  obtain ⟨S,c,sc⟩ := Loc.tau_attained G
  refine ⟨z,hz,?_⟩
  intro C ao correct
  have mono : Monotone2 C := fun g hg =>
    ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ao.1 g hg,(ao.2.2 g hg).le⟩
  have bound := numerical G sq sparse witness C mono correct
  exact atVertexOfCoverBound G z rem C ⟨S,c,by omega⟩

#print axioms numerical
#print axioms ownership
#print axioms vertex_deletion
#print axioms staircase
#print axioms and_lower
end VertexPeel.OrderedMatching
