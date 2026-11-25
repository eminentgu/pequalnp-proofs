import CoverFour
import Mathlib.Data.Finset.Sum

namespace VertexPeel.EdgeBudget
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.CoverPromise PEqualNP.TopForm
open VertexPeel.CoverThreeCore
open scoped Sym2

private theorem same_pair {α : Type} [DecidableEq α] {a b c d : α}
    (h : ({a,b} : Finset α) = {c,d}) : (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  apply Set.pair_eq_pair_iff.mp
  simpa using congrArg (fun s : Finset α => (s : Set α)) h

private theorem common_unique {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (sq : NoFourCycle G) {a b v w : Fin n} (ne : a ≠ b)
    (av : G.Adj a v) (bv : G.Adj b v) (aw : G.Adj a w) (bw : G.Adj b w) : v = w :=
  Finset.card_le_one.mp (sq a b ne) v (Finset.mem_filter.mpr ⟨Finset.mem_univ _,av,bv⟩)
    w (Finset.mem_filter.mpr ⟨Finset.mem_univ _,aw,bw⟩)

variable {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n))
private abbrev Tag (n : ℕ) := Fin n ⊕ Finset (Fin n)

/-- A first incidence outside the cover uses the vertex itself as its label.
All other incidences use unordered pairs of cover vertices. -/
private inductive Account (h : Fin n → Fin n) : Sym2 (Fin n) → Tag n → Prop
  | first (v : Fin n) : Account h s(v,h v) (.inl v)
  | internal (a b : Fin n) (ab : G.Adj a b) : Account h s(a,b) (.inr {a,b})
  | shared (v u : Fin n) (vu : G.Adj v u) (vh : G.Adj v (h v)) (ne : h v ≠ u) :
      Account h s(v,u) (.inr {h v,u})

private theorem unique_label [DecidableRel G.Adj] (tri : NoTriangles G) (sq : NoFourCycle G)
    (h : Fin n → Fin n) {a b : Sym2 (Fin n)} {x : Tag n}
    (one : Account G h a x) (two : Account G h b x) : a = b := by
  cases one with
  | first v => cases two; rfl
  | internal a b ab =>
    generalize eq : (Sum.inr {a,b} : Tag n) = k at two
    cases two with
    | first => contradiction
    | internal c d cd =>
      rcases same_pair (Sum.inr.inj eq) with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · rfl
      · exact Sym2.eq_swap
    | shared w u wu wh _ =>
      rcases same_pair (Sum.inr.inj eq) with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact (tri _ _ _ ab wu.symm wh).elim
      · exact (tri _ _ _ ab wh.symm wu).elim
  | shared v u vu vh ne =>
    generalize eq : (Sum.inr {h v,u} : Tag n) = k at two
    cases two with
    | first => contradiction
    | internal a b ab =>
      rcases same_pair (Sum.inr.inj eq) with ⟨ea,eb⟩|⟨ea,eb⟩
      · subst a; subst b; exact (tri _ _ _ vh ab vu.symm).elim
      · subst b; subst a; exact (tri _ _ _ vu ab vh.symm).elim
    | shared w y wy wh _ =>
      rcases same_pair (Sum.inr.inj eq) with ⟨eh,ey⟩|⟨eh,ey⟩
      · obtain rfl : v=w := common_unique sq ne vh.symm vu.symm (eh ▸ wh.symm) (ey ▸ wy.symm)
        subst y; rfl
      · obtain eqvw : v=w := common_unique sq ne vh.symm vu.symm (eh ▸ wy.symm) (ey ▸ wh.symm)
        exact (ne (eqvw ▸ ey.symm)).elim

/-- For every graph of girth at least five and every cover, at most one extra
edge per outside vertex remains after charging edges to distinct cover pairs. -/
theorem edges_le [DecidableRel G.Adj] (tri : NoTriangles G) (sq : NoFourCycle G)
    (cover : IsVertexCover G T) :
    G.edgeFinset.card ≤ (CoverKernel.active G \ T).card + T.card.choose 2 := by
  classical
  let h (v : Fin n) := if ok : ∃ w, G.Adj v w then ok.choose else v
  have choose {v w : Fin n} (edge : G.Adj v w) : G.Adj v (h v) := by
    have ok : ∃ w, G.Adj v w := ⟨w,edge⟩
    simpa only [h,dite_eq_left ok] using ok.choose_spec
  let Q := (CoverKernel.active G \ T).disjSum (T.powersetCard 2)
  have pair {a b : Fin n} (aT : a ∈ T) (bT : b ∈ T) (ne : a ≠ b) : (Sum.inr {a,b} : Tag n) ∈ Q := by
    apply Finset.inr_mem_disjSum.mpr
    refine Finset.mem_powersetCard.mpr ⟨?_,by simp [ne]⟩
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl|hw
    · exact aT
    · exact Finset.mem_singleton.mp hw ▸ bT
  have ext {v u : Fin n} (vu : G.Adj v u) (out : v ∉ T) :
      ∃ k ∈ Q, Account G h s(v,u) k := by
    have vh := choose vu
    by_cases hu : h v = u
    · refine ⟨.inl v,Finset.inl_mem_disjSum.mpr ?_,hu ▸ Account.first v⟩
      apply Finset.mem_sdiff.mpr
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,(G.degree_pos_iff_exists_adj v).mpr ⟨u,vu⟩⟩,out⟩
    · exact ⟨.inr {h v,u},pair ((cover v _ vh).resolve_left out) ((cover v u vu).resolve_left out) hu,
        Account.shared v u vu vh hu⟩
  have total (e : Sym2 (Fin n)) (he : e ∈ G.edgeFinset) : ∃ k ∈ Q, Account G h e k := by
    induction e using Sym2.inductionOn with
    | _ a b =>
      have ab := G.mem_edgeFinset.mp he
      change G.Adj a b at ab
      by_cases aT : a ∈ T
      · by_cases bT : b ∈ T
        · exact ⟨.inr {a,b},pair aT bT ab.ne,Account.internal a b ab⟩
        · simpa only [Sym2.eq_swap (a := b) (b := a)] using ext ab.symm bT
      · exact ext ab aT
  let assign (e : Sym2 (Fin n)) : Tag n := if he : e ∈ G.edgeFinset then (total e he).choose else .inr ∅
  have witness {e : Sym2 (Fin n)} (he : e ∈ G.edgeFinset) : assign e ∈ Q ∧ Account G h e (assign e) := by
    simpa only [assign,dite_eq_left he] using (total e he).choose_spec
  have count := Finset.card_le_card_of_injOn assign (fun e he => (witness he).1)
    (fun a ha b hb eq => unique_label G tri sq h (witness ha).2 (eq ▸ (witness hb).2))
  simpa [Q] using count

/-- The input-order bound from critical leaf reduction makes the number of edges at most t(t−1).
This estimate applies to every active graph in the finite core, including nonbipartite graphs. -/
theorem core_edges [DecidableRel G.Adj] (tri : NoTriangles G) (sq : NoFourCycle G)
    (cover : IsVertexCover G T) (active : ∀ v, 0 < G.degree v)
    (order : n ≤ T.card + T.card.choose 2) : G.edgeFinset.card ≤ T.card * (T.card-1) := by
  have full : CoverKernel.active G = Finset.univ := by
    ext i
    simp [CoverKernel.active,active i]
  have count := edges_le G T tri sq cover
  rw [full,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin] at count
  have same : T.card.choose 2 * 2 = T.card * (T.card-1) := by
    rw [Nat.choose_two_right,Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self _)]
  omega

#print axioms edges_le
#print axioms core_edges
end VertexPeel.EdgeBudget
