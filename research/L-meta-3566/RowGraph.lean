import RowCharge

namespace VertexPeel.RowGraph

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.Core
open VertexPeel.ZeroFold VertexPeel.RowCharge

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- The negative test for row u turns on u and every non-neighbor on the right. -/
def rowBase (R : Finset (Fin n)) (u i : Fin n) : Bool := decide (i = u ∨ i ∈ R ∧ ¬ G.Adj u i)

theorem row_negative (R : Finset (Fin n)) (indep : ∀ a ∈ R, ∀ b ∈ R, ¬ G.Adj a b) (u : Fin n) :
    graphFun G ∅ (rowBase G R u) = false := by
  have off : ¬ ∃ a b, G.Adj a b ∧ rowBase G R u a = true ∧ rowBase G R u b = true := by
    rintro ⟨a,b,hab,ha,hb⟩
    simp only [rowBase,decide_eq_true_eq] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact hab.ne rfl
    · exact hb.2 hab
    · exact ha.2 hab.symm
    · exact indep a ha.1 b hb.1 hab
  simp [graphFun,off]

noncomputable abbrev rowGates (R : Finset (Fin n)) (C : Circuit) (u : Fin n) :=
  charged C (rowBase G R u) (pairInput u) (G.neighborFinset u) C.size

/-- Each row of degree d needs d−1 distinct splitting ORs in the original DAG. -/
theorem degree_bound (R : Finset (Fin n)) (indep : ∀ a ∈ R, ∀ b ∈ R, ¬ G.Adj a b)
    (C : Circuit) (hc : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅) (u : Fin n) :
    G.degree u ≤ (rowGates G R C u).card + 1 := by
  rw [← G.card_neighborFinset_eq_degree]
  apply output_bound _ _ _ _ hc
  · intro i v _ hx hp
    simp only [pairInput,decide_eq_true_eq] at hp
    exact hp.resolve_left (fun h => by subst i; simp [rowBase] at hx)
  · rw [ok]
    exact row_negative G R indep u
  · intro v hv
    have edge := (G.mem_neighborFinset u v).mp hv
    have pos : ∃ a b, G.Adj a b ∧ pairInput u v a = true ∧ pairInput u v b = true :=
      ⟨u,v,edge,by simp [pairInput],by simp [pairInput]⟩
    simp [ok,graphFun,pos]

/-- Monotonicity on each physical wire, including outputs in the interior of the DAG. -/
theorem wire_mono (C : Circuit) (hc : IsAO2 n C) {x y : Fin n → Bool}
    (le : ∀ i, x i = true → y i = true) (w : ℕ) (on : wval C x w = true) : wval C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w < n
    · let v : Fin n := ⟨w,raw⟩
      exact (wval_in C y v) ▸ le v ((wval_in C x v) ▸ on)
    by_cases past : n+C.gates.length ≤ w
    · rw [wval_past C x w past] at on
      contradiction
    let j := w-n
    have hj : j < C.gates.length := by dsimp [j]; omega
    have eq : w = n+j := by dsimp [j]; omega
    obtain ⟨a,b,hab,ha,hb,hand|hor⟩ := two n C hc j hj
    · rw [eq,wval_and C x j a b hj hab ha hb hand,Bool.and_eq_true] at on
      rw [eq,wval_and C y j a b hj hab ha hb hand,Bool.and_eq_true]
      exact ⟨ih a (by omega) on.1,ih b (by omega) on.2⟩
    · rw [eq,wval_or C x j a b hj hab ha hb hor,Bool.or_eq_true] at on
      rw [eq,wval_or C y j a b hj hab ha hb hor,Bool.or_eq_true]
      exact on.imp (ih a (by omega)) (ih b (by omega))

def singles (R : Finset (Fin n)) (C : Circuit) (w : ℕ) :=
  R.filter fun v => wval C (pairInput v v) w = true

/-- Every right singleton accepted by a wire false on the row must neighbor that row. -/
theorem singles_neighbors (R : Finset (Fin n)) (C : Circuit) (hc : IsAO2 n C) (u : Fin n) (w : ℕ)
    (off : wval C (rowBase G R u) w = false) : singles R C w ⊆ G.neighborFinset u := by
  intro v hv
  obtain ⟨hr,hon⟩ := Finset.mem_filter.mp hv
  apply (G.mem_neighborFinset u v).mpr
  by_contra hn
  have h := wire_mono C hc (x := pairInput v v) (y := rowBase G R u) (by
    intro a ha
    have eq : a = v := by simpa [pairInput] using ha
    subst a
    simp [rowBase,hr,hn]) w hon
  rw [off] at h
  contradiction

/-- A gate accepting two right singleton inputs can split at most one row of a C4-free graph. -/
theorem rich_unique (R : Finset (Fin n)) (C : Circuit) (hc : IsAO2 n C) (four : NoFourCycle G)
    {u v : Fin n} {j : ℕ} (hu : j ∈ rowGates G R C u) (hv : j ∈ rowGates G R C v)
    (rich : 2 ≤ (singles R C (n+j)).card) : u = v := by
  classical
  by_contra hne
  have off (a : Fin n) (mem : j ∈ rowGates G R C a) : wval C (rowBase G R a) (n+j) = false :=
    (Finset.mem_filter.mp mem).2.2.1
  have sub : singles R C (n+j) ⊆ Finset.univ.filter (fun i => G.Adj u i ∧ G.Adj v i) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (G.mem_neighborFinset u i).mp (singles_neighbors G R C hc u _ (off u hu) hi),
      (G.mem_neighborFinset v i).mp (singles_neighbors G R C hc v _ (off v hv) hi)⟩
  have low := (Finset.card_le_card sub).trans (four u v hne)
  omega

end VertexPeel.RowGraph
