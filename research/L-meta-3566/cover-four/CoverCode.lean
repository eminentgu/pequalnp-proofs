import CriticalSupport
import Mathlib.Data.Fintype.Sum

namespace VertexPeel.CoverCode

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.CoverPromise PEqualNP.TopForm
open VertexPeel.CoverKernel

abbrev Vertex (t : ℕ) (cols : Finset (Finset (Fin t))) := Fin t ⊕ {S // S ∈ cols}

/-- A labeled cover, followed by one outside vertex for every selected neighborhood. -/
def graph {t : ℕ} (inside : SimpleGraph (Fin t)) (cols : Finset (Finset (Fin t))) :
    SimpleGraph (Vertex t cols) where
  Adj
    | .inl i, .inl j => inside.Adj i j
    | .inl i, .inr s => i ∈ s.val
    | .inr s, .inl i => i ∈ s.val
    | .inr _, .inr _ => False
  symm.symm := by
    rintro (i|s) (j|q) h
    · exact h.symm
    · exact h
    · exact h
    · exact h
  loopless.irrefl := by
    rintro (i|s) h
    · exact inside.loopless.irrefl i h
    · exact h

/-- The full outside neighborhoods distinguish vertices: two common neighbors form
a four-cycle, and a shared single neighbor gives twin leaves. -/
private theorem rows_injective {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (sq : NoFourCycle G) (noTwins : ¬TwinLeaves G) (active : ∀ a, 0 < G.degree a)
    {a b : Fin n} (h : G.neighborFinset a = G.neighborFinset b) : a = b := by
  by_contra ne
  have incl : G.neighborFinset a ⊆ Finset.univ.filter (fun v => G.Adj a v ∧ G.Adj b v) := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(G.mem_neighborFinset _ _).mp hv,
      (G.mem_neighborFinset _ _).mp (h ▸ hv)⟩
  have le := (Finset.card_le_card incl).trans (sq _ _ ne)
  have pos : 0 < (G.neighborFinset a).card := by simpa using active a
  obtain ⟨u,hu⟩ := Finset.card_eq_one.mp (show (G.neighborFinset a).card = 1 by omega)
  exact noTwins ⟨a,b,u,ne,hu,h.symm.trans hu⟩

/-- An arbitrary reduced graph having a t-element cover has a regular encoding by
choose(t,2) internal edge flags and (2^t−1) exterior neighborhood flags.
The equivalence reconstructs the entire graph after isolated vertices have been removed. -/
theorem exists_code {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (K : Finset (Fin n)) (cover : IsVertexCover G K) (size : K.card = t)
    (sq : NoFourCycle G) (noTwins : ¬TwinLeaves G) (active : ∀ a, 0 < G.degree a) :
    ∃ (inside : SimpleGraph (Fin t)) (cols : Finset (Finset (Fin t))),
      ∅ ∉ cols ∧ Nonempty (G ≃g graph inside cols) := by
  classical
  let p := (K.equivFinOfCardEq size).symm
  let label (i : Fin t) : Fin n := (p i).val
  let row (v : Fin n) := Finset.univ.filter fun i : Fin t => G.Adj v (label i)
  let E := Kᶜ
  let cols := E.image row
  let I := G.comap label
  have lift {v : Fin n} (mem : v ∈ K) : ∃ i, label i = v := by
    obtain ⟨i,eq⟩ := p.surjective ⟨v,mem⟩
    exact ⟨i,congrArg Subtype.val eq⟩
  have within {v w} (hv : v ∈ E) (hw : G.Adj v w) : w ∈ K :=
    (cover v w hw).resolve_left (Finset.mem_compl.mp hv)
  have row_eq (i : Fin t) (v : Fin n) : i ∈ row v ↔ G.Adj v (label i) := by simp [row]
  have inc {a b : Fin n} (ha : a ∈ E) (same : row a = row b) :
      G.neighborFinset a ⊆ G.neighborFinset b := by
    intro v hv
    have av := (G.mem_neighborFinset a v).mp hv
    obtain ⟨i,rfl⟩ := lift (within ha av)
    exact (G.mem_neighborFinset _ _).mpr ((row_eq i b).mp (same ▸ (row_eq i a).mpr av))
  have inj {a b : Fin n} (ha : a ∈ E) (hb : b ∈ E) (same : row a = row b) : a=b :=
    rows_injective G sq noTwins active (Finset.Subset.antisymm (inc ha same) (inc hb same.symm))
  have nz : ∅ ∉ cols := by
    intro nil
    obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp nil
    obtain ⟨w,edge⟩ := (G.degree_pos_iff_exists_adj v).mp (active v)
    obtain ⟨i,rfl⟩ := lift (within hv edge)
    have mem := (row_eq i v).mpr edge
    simp [eq] at mem
  let names : {v // v ∈ E} → {S // S ∈ cols} := fun v =>
    ⟨row v.val,Finset.mem_image.mpr ⟨v.val,v.property,rfl⟩⟩
  let e := Equiv.ofBijective names (show Function.Bijective names from ⟨by
    intro u v eq
    exact Subtype.ext (inj u.property v.property (congrArg Subtype.val eq)),by
    intro s
    obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp s.property
    exact ⟨⟨v,hv⟩,Subtype.ext eq⟩⟩)
  let unname : Vertex t cols → Fin n := Sum.elim label (fun s => (e.symm s).val)
  have name_l (i : Fin t) : unname (.inl i) ∈ K := (p i).property
  have name_r (s : {S // S ∈ cols}) : unname (.inr s) ∈ E := (e.symm s).property
  have rows (s : {S // S ∈ cols}) : row (unname (.inr s)) = s.val :=
    congrArg Subtype.val (e.apply_symm_apply s)
  have bij : Function.Bijective unname := by
    constructor
    · rintro (i|s) (j|q) eq
      · exact congrArg Sum.inl (p.injective (Subtype.ext eq))
      · exact ((Finset.mem_compl.mp (name_r q)) (eq ▸ name_l i)).elim
      · exact ((Finset.mem_compl.mp (name_r s)) (eq.symm ▸ name_l j)).elim
      · exact congrArg Sum.inr (e.symm.injective (Subtype.ext eq))
    · intro v
      by_cases hv : v ∈ K
      · obtain ⟨i,eq⟩ := lift hv
        exact ⟨.inl i,eq⟩
      · let q : {v // v ∈ E} := ⟨v,Finset.mem_compl.mpr hv⟩
        exact ⟨.inr (e q),congrArg Subtype.val (e.symm_apply_apply q)⟩
  refine ⟨I,cols,nz,⟨RelIso.symm (show graph I cols ≃g G from ⟨Equiv.ofBijective unname bij,?_⟩)⟩⟩
  rintro (i|s) (j|q)
  · exact Iff.rfl
  · change G.Adj (label i) (unname (.inr q)) ↔ i ∈ q.val
    rw [← rows q,row_eq,G.adj_comm]
  · change G.Adj (unname (.inr s)) (label j) ↔ j ∈ s.val
    rw [← rows s,row_eq]
  · change G.Adj (unname (.inr s)) (unname (.inr q)) ↔ False
    exact iff_false_intro fun edge => (Finset.mem_compl.mp (name_r q)) (within (name_r s) edge)

#print axioms exists_code
end VertexPeel.CoverCode
