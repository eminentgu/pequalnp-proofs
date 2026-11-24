import PEqualNP.Outside.L_meta_1955
import PEqualNP.Outside.L_meta_2237

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK
open scoped BigOperators Sym2

namespace PlaneReadOne

variable {N : ℕ} (I : Fin N → Fin N → Prop)

def adjacent (a b : Fin (N+N)) : Prop :=
  Fin.addCases (fun p => Fin.addCases (fun _ => False) (fun l => I p l) b)
    (fun l => Fin.addCases (fun p => I p l) (fun _ => False) b) a

def graph : SimpleGraph (Fin (N+N)) where
  Adj := adjacent I
  symm := by
    constructor
    intro a b
    induction a using Fin.addCases <;> induction b using Fin.addCases <;> simp only [adjacent,Fin.addCases_left,Fin.addCases_right] <;> tauto
  loopless := by
    constructor
    intro a
    induction a using Fin.addCases <;> simp only [adjacent,Fin.addCases_left,Fin.addCases_right] <;> tauto

noncomputable instance : DecidableRel (graph I).Adj := Classical.decRel _

private theorem cross_ne (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have eq := congrArg Fin.val h
  change p.val = N + l.val at eq
  omega

private theorem noFour
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l) : NoFourCycle (graph I) := by
  have line (a b u v : Fin N) (ne : a ≠ b) (hu : I a u ∧ I b u) (hv : I a v ∧ I b v) :
      u = v := (unique a b ne).unique hu hv
  have point (a b u v : Fin N) (ne : u ≠ v) (ha : I a u ∧ I a v) (hb : I b u ∧ I b v) :
      a = b := by
    by_contra ab
    exact ne (line a b u v ab ⟨ha.1,hb.1⟩ ⟨ha.2,hb.2⟩)
  intro a b hab
  apply Finset.card_le_one.mpr
  intro u hu v hv
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hu hv
  induction a using Fin.addCases <;> induction b using Fin.addCases <;>
    induction u using Fin.addCases <;> induction v using Fin.addCases <;>
    simp only [graph,adjacent,Fin.addCases_left,Fin.addCases_right] at hu hv <;>
    obtain ⟨hu₁,hu₂⟩ := hu <;> obtain ⟨hv₁,hv₂⟩ := hv <;> try contradiction
  all_goals
    apply congrArg _
    first
    | exact line _ _ _ _ (fun h => hab (congrArg _ h)) ⟨hu₁,hu₂⟩ ⟨hv₁,hv₂⟩
    | exact point _ _ _ _ (fun h => hab (congrArg _ h)) ⟨hu₁,hu₂⟩ ⟨hv₁,hv₂⟩

private theorem graph_eval (z : Fin (N+N) → Bool) :
    (∃ u v, (graph I).Adj u v ∧ z u = true ∧ z v = true) ↔
    ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
  constructor
  · rintro ⟨u,v,adj,hu,hv⟩
    induction u using Fin.addCases <;> induction v using Fin.addCases <;>
      simp only [graph,adjacent,Fin.addCases_left,Fin.addCases_right] at adj <;> exact ⟨_,_,adj,by assumption,by assumption⟩
  · rintro ⟨p,l,hp,hz,hl⟩
    exact ⟨Fin.castAdd N p,Fin.natAdd N l,by simpa only [graph,adjacent,Fin.addCases_left,Fin.addCases_right] using hp,hz,hl⟩

private def encode (e : Fin N × Fin N) : Sym2 (Fin (N+N)) :=
  s(Fin.castAdd N e.1, Fin.natAdd N e.2)

private theorem encode_inj : Function.Injective (@encode N) := by
  rintro ⟨p,l⟩ ⟨p',l'⟩ h
  rcases Sym2.eq_iff.mp h with h | h
  · obtain ⟨hp,hl⟩ := h
    have : p = p' := Fin.castAdd_injective _ _ hp
    have : l = l' := by simpa [Fin.ext_iff] using congrArg Fin.val hl
    congr
  · exact (cross_ne _ _ h.1).elim

private theorem edges [DecidableRel I] (q : ℕ)
    (degree : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1) :
    N*(q+1) ≤ (graph I).edgeFinset.card := by
  classical
  let pairs := ((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N))).filter
    fun e => I e.1 e.2
  have count : pairs.card = N*(q+1) := by
    change (((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N))).filter _).card = _
    rw [PEqualNP.Outside.L_meta_1955.cardR,Finset.sum_congr rfl (fun l _ => degree l)]
    simp
  have sub : pairs.image encode ⊆ (graph I).edgeFinset := by
    rintro _ h
    obtain ⟨⟨p,l⟩,hp,rfl⟩ := Finset.mem_image.mp h
    apply SimpleGraph.mem_edgeFinset.mpr
    change (graph I).Adj (Fin.castAdd N p) (Fin.natAdd N l)
    simpa only [graph,adjacent,Fin.addCases_left,Fin.addCases_right] using (Finset.mem_filter.mp hp).2
  rw [← count, ← Finset.card_image_of_injective pairs encode_inj]
  exact Finset.card_le_card sub

private theorem cover (q : ℕ) [DecidableRel I]
    (lines : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (points : ∀ p, (Finset.univ.filter fun l => I p l).card = q+1)
    (T : Finset (Fin (N+N))) (hits : ∀ u v, (graph I).Adj u v → u ∈ T ∨ v ∈ T) :
    N ≤ T.card := by
  let A := Finset.univ.filter fun p : Fin N => Fin.castAdd N p ∈ T
  let B := Finset.univ.filter fun l : Fin N => Fin.natAdd N l ∈ T
  have lower := PEqualNP.Outside.L_meta_1955.cover q I lines points A B (by
    intro p l h
    simpa [A,B] using hits (Fin.castAdd N p) (Fin.natAdd N l) (by simpa only [graph,adjacent,Fin.addCases_left,Fin.addCases_right] using h))
  let pa := A.image (Fin.castAdd N)
  let lb := B.image (Fin.natAdd N)
  have prem : Disjoint pa lb := by
    refine Finset.disjoint_left.mpr ?_
    intro v ha hb
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨l,_,eq⟩ := Finset.mem_image.mp hb
    exact cross_ne p l eq.symm
  have sub : pa ∪ lb ⊆ T := by
    intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp hp).2
    · obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp hl).2
  have natInj : Function.Injective (@Fin.natAdd N N) := by
    intro a b h
    apply Fin.ext
    simpa using congrArg Fin.val h
  have size := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint prem] at size
  change (A.image (Fin.castAdd N)).card + (B.image (Fin.natAdd N)).card ≤ T.card at size
  rw [Finset.card_image_of_injective _ (Fin.castAdd_injective _ _),
    Finset.card_image_of_injective _ natInj] at size
  omega

/-- In the plane axioms used by L-meta-2583, any read-1 realization already
    needs one gate per incidence plus one per point, except for the output offset. -/
theorem sharp (q : ℕ) [DecidableRel I] (C : Circuit) (hq : 2 ≤ q)
    (order : N = q^2+q+1)
    (lines : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
    (ao : IsAO2 (N+N) C)
    (evaluates : ∀ z : Fin (N+N) → Bool, circuitFun (N+N) C z =
      decide (∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (reads : IsReadK (N+N) C 1) : N*(q+2) ≤ C.size+1 := by
  classical
  have points := PEqualNP.Outside.L_meta_1955.lines_through q N I hq order lines unique
  have L := PEqualNP.Outside.L_meta_2237 (N+N) (graph I) C (noFour I unique) ao
    (fun z => by rw [evaluates]; exact decide_eq_decide.mpr (graph_eval I z).symm) reads
  obtain ⟨T,hits,bound⟩ := L
  have hT := cover I q lines points T hits
  have hE := edges I q lines
  calc
    N*(q+2) = N*(q+1)+N := by ring
    _ ≤ _ := by omega

/-- For a fixed input circuit, any size-preserving replacement forces the
    exact star threshold. The original circuit can have arbitrary reads. -/
theorem necessary (q : ℕ) [DecidableRel I] (C : Circuit) (hq : 2 ≤ q)
    (order : N = q^2+q+1)
    (lines : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
    (replace : ∃ D : Circuit, IsAO2 (N+N) D ∧
      (∀ z : Fin (N+N) → Bool, circuitFun (N+N) D z =
        decide (∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) ∧
      D.size ≤ C.size ∧ IsReadK (N+N) D 1) : N*(q+2) ≤ C.size+1 := by
  obtain ⟨D,ao,ev,lim,read⟩ := replace
  exact (sharp I q D hq order lines unique ao ev read).trans (Nat.add_le_add_right lim 1)

end PlaneReadOne

#print axioms PlaneReadOne.sharp
#print axioms PlaneReadOne.necessary
