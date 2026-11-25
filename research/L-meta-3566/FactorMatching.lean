import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

namespace VertexPeel.FactorMatching

variable {A B : Type*}
abbrev Relation (A B : Type*) := A → B → Prop
abbrev Hits (G : Relation A B) (rows : A → Prop) (cols : B → Prop) : Prop :=
  ∃ r c, rows r ∧ cols c ∧ G r c
abbrev Exact (G H K : Relation A B) : Prop :=
  ∀ rows cols, Hits G rows cols ↔ Hits H rows cols ∧ Hits K rows cols
abbrev SquareFree (G : Relation A B) : Prop :=
  ∀ {a b c d}, a ≠ b → c ≠ d → G a c → G a d → G b c → G b d → False

/-- For one extra edge in each branch, at least one of the two crossing pairs
    must be an original edge; restrict the input to the four endpoints. -/
theorem cross (G H K : Relation A B) (exact : Exact G H K) {a c : A} {b d : B}
    (h : H a b) (nh : ¬G a b) (k : K c d) (nk : ¬G c d) : G a d ∨ G c b := by
  obtain ⟨r,s,hr,hs,edge⟩ := (exact (fun t => t=a ∨ t=c) (fun t => t=b ∨ t=d)).mpr
    ⟨⟨a,b,Or.inl rfl,Or.inl rfl,h⟩,⟨c,d,Or.inr rfl,Or.inr rfl,k⟩⟩
  rcases hr with rfl | rfl <;> rcases hs with rfl | rfl <;> tauto

/-- Exactness has a complete description in terms of pairs of extra edges. -/
theorem exact_iff (G H K : Relation A B) :
    Exact G H K ↔ (∀ a b, G a b → H a b ∧ K a b) ∧
      ∀ a b c d, H a b → ¬G a b → K c d → ¬G c d → G a d ∨ G c b := by
  constructor
  · intro e
    refine ⟨?_,fun _ _ _ _ => cross G H K e⟩
    intro a b ab
    obtain ⟨⟨r,s,ra,sb,hh⟩,⟨v,w,va,wb,kk⟩⟩ := (e (·=a) (·=b)).mp ⟨a,b,rfl,rfl,ab⟩
    exact ⟨ra ▸ sb ▸ hh,va ▸ wb ▸ kk⟩
  · rintro ⟨incl,compat⟩ rows cols
    constructor
    · rintro ⟨r,s,hr,hs,gs⟩
      exact ⟨⟨r,s,hr,hs,(incl r s gs).1⟩,⟨r,s,hr,hs,(incl r s gs).2⟩⟩
    · rintro ⟨⟨a,b,ha,hb,hh⟩,⟨c,d,hc,hd,kk⟩⟩
      by_cases g : G a b
      · exact ⟨a,b,ha,hb,g⟩
      by_cases t : G c d
      · exact ⟨c,d,hc,hd,t⟩
      exact (compat _ _ _ _ hh g kk t).elim (fun l => ⟨a,d,ha,hd,l⟩) (fun l => ⟨c,b,hc,hb,l⟩)

abbrev Row := Finset (Fin 5)

def compatible (r s : Row) : Bool :=
  decide ((r ∩ s).card ≤ 1 ∧ (rᶜ ∩ sᶜ).card ≤ 1)

def canChoose : ℕ → List Row → Bool
  | 0, _ => true
  | n+1, rows => rows.any fun r => canChoose n (rows.filter (compatible r))

private theorem choose {n : ℕ} (f : Fin n → Row) (rows : List Row) (all : ∀ i, f i ∈ rows)
    (good : ∀ i j, i ≠ j → compatible (f i) (f j) = true) : canChoose n rows = true := by
  induction n generalizing rows with
  | zero => rfl
  | succ n ih =>
    apply List.any_eq_true.mpr
    refine ⟨f 0,all 0,?_⟩
    apply ih (fun i => f i.succ)
    · intro i
      apply List.mem_filter.mpr
      exact ⟨all i.succ,good 0 i.succ (Fin.succ_ne_zero _).symm⟩
    · intro i j ne
      exact good i.succ j.succ (fun e => ne (Fin.succ_injective _ e))

private def subsets : List (Fin 5) → List Row
  | [] => [∅]
  | a :: xs =>
    let old := subsets xs
    old ++ old.map (insert a)

private theorem all_subsets (s : Row) (xs : List (Fin 5)) (incl : ∀ j ∈ s, j ∈ xs) :
    s ∈ subsets xs := by
  induction xs generalizing s with
  | nil =>
    have emp : s=∅ := Finset.eq_empty_iff_forall_notMem.mpr (by intro i h; simpa using incl i h)
    simp [subsets,emp]
  | cons a xs ih =>
    by_cases inside : a ∈ s
    · have used := ih (s.erase a) (by
        intro i hi
        obtain ⟨ne,m⟩ := Finset.mem_erase.mp hi
        exact (List.mem_cons.mp (incl i m)).resolve_left ne)
      exact List.mem_append_right _ (List.mem_map.mpr ⟨s.erase a,used,Finset.insert_erase inside⟩)
    · exact List.mem_append_left _ (ih s (by
        intro i hi
        exact (List.mem_cons.mp (incl i hi)).resolve_left (fun e => inside (e ▸ hi))))

private def allRows := subsets [0,1,2,3,4]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem noFive : canChoose 5 allRows = false := by
  decide +kernel

/-- Each of the two extra-edge sets cannot have a five-edge matching.
    The branch circuits may share any of their internal gates. -/
theorem not_two_matchings (G H K : Relation A B) (exact : Exact G H K) (sq : SquareFree G)
    (a c : Fin 5 → A) (b d : Fin 5 → B)
    (ia : Function.Injective a) (ic : Function.Injective c)
    (ib : Function.Injective b) (id' : Function.Injective d)
    (h : ∀ i, H (a i) (b i) ∧ ¬G (a i) (b i))
    (k : ∀ j, K (c j) (d j) ∧ ¬G (c j) (d j)) : False := by
  classical
  let f (i : Fin 5) : Row := Finset.univ.filter fun j => G (a i) (d j)
  have green (i j : Fin 5) (hj : j ∉ f i) : G (c j) (b i) :=
    (cross G H K exact (h i).1 (h i).2 (k j).1 (k j).2).resolve_left (fun e => hj (by simp [f,e]))
  have good (i t : Fin 5) (neq : i≠t) : compatible (f i) (f t) = true := by
    apply decide_eq_true
    constructor <;> apply Finset.card_le_one.mpr
    · intro j hj s hs
      by_contra ne
      simp [f] at hj hs
      exact sq (fun e => neq (ia e)) (fun e => ne (id' e)) hj.1 hs.1 hj.2 hs.2
    · intro j hj s hs
      by_contra ne
      simp only [Finset.mem_inter,Finset.mem_compl] at hj hs
      exact sq (fun e => ne (ic e)) (fun e => neq (ib e)) (green _ _ hj.1) (green _ _ hj.2)
        (green _ _ hs.1) (green _ _ hs.2)
  have yes := choose f allRows (fun i => all_subsets (f i) _ (by intro j _; fin_cases j <;> decide)) good
  rw [noFive] at yes
  contradiction

end VertexPeel.FactorMatching

#print axioms VertexPeel.FactorMatching.not_two_matchings
