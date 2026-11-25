import RowCharge

namespace VertexPeel.ReusedCone

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.ReadTwo PEqualNP.TopForm VertexPeel.ZeroFold

def Reads (n : ℕ) (C : Circuit) (w a : ℕ) : Prop :=
  ∃ j < C.size, w = n+j ∧ a ∈ (gateAt C j).inputs

abbrev Reaches (n : ℕ) (C : Circuit) := Relation.ReflTransGen (Reads n C)

noncomputable def cone (n : ℕ) (C : Circuit) (root t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range t).filter fun j => Reaches n C root (n+j)

/-- A single input alone affects this wire. -/
def sensitive {n : ℕ} (C : Circuit) (w : ℕ) (i : Fin n) : Prop :=
  ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧ wval C x w ≠ wval C y w

private theorem descend {n : ℕ} {C : Circuit} {t a b : ℕ} (ht : t < C.size)
    (ab : C.gates[t].inputs = [a,b]) (ha : a < n+t) (hb : b < n+t)
    (ops : C.gates[t].op = .and ∨ C.gates[t].op = .or) (i : Fin n)
    (dep : sensitive C (n+t) i) : sensitive C a i ∨ sensitive C b i := by
  obtain ⟨x,y,apart,unequal⟩ := dep
  by_cases da : wval C x a = wval C y a
  · right
    refine ⟨x,y,apart,fun db => unequal ?_⟩
    rcases ops with hand | hor
    · rw [wval_and C x t a b ht ab ha hb hand,wval_and C y t a b ht ab ha hb hand,da,db]
    · rw [wval_or C x t a b ht ab ha hb hor,wval_or C y t a b ht ab ha hb hor,da,db]
  · exact Or.inl ⟨x,y,apart,da⟩

/-- Counts physical ancestors even when two branches share an earlier gate. -/
theorem frontier_bound {n : ℕ} (C : Circuit) (hc : IsAO2 n C) (root t : ℕ) (ht : t ≤ C.size)
    (W : Finset ℕ) (prior : ∀ w ∈ W, w < n+t) (reachable : ∀ w ∈ W, Reaches n C root w)
    (U : Finset (Fin n)) (dep : ∀ i ∈ U, ∃ w ∈ W, sensitive C w i) :
    U.card ≤ (cone n C root t).card + W.card := by
  classical
  induction t generalizing W with
  | zero =>
    have mem (i : Fin n) (hi : i ∈ U) : i.val ∈ W := by
      obtain ⟨w,hw,x,y,apart,diff⟩ := dep i hi
      let a : Fin n := ⟨w,by simpa using prior w hw⟩
      have eq : a = i := by
        by_contra ne
        exact diff ((wval_in C x a).trans ((apart a ne).trans (wval_in C y a).symm))
      exact (congrArg Fin.val eq) ▸ hw
    have lower := Finset.card_le_card_of_injOn (s := U) (t := W) Fin.val mem Fin.val_injective.injOn
    simpa [cone] using lower
  | succ t ih =>
    have gt : t < C.size := by omega
    have fresh : t ∉ cone n C root t := by simp [cone]
    by_cases h : n+t ∈ W
    · obtain ⟨a,b,ab,ha,hb,ops⟩ := two n C hc t gt
      let rest := W.erase (n+t)
      let next := insert a (insert b rest)
      have r (w : ℕ) (hw : w ∈ rest) : w ∈ W ∧ w < n+t := by
        obtain ⟨ne,hin⟩ := Finset.mem_erase.mp hw
        exact ⟨hin,by have := prior w hin; omega⟩
      have pair : Reads n C (n+t) a ∧ Reads n C (n+t) b := by
        constructor <;> refine ⟨t,gt,rfl,?_⟩ <;> simp [gateAt_eq C t gt,ab]
      have before : ∀ w ∈ next, w < n+t := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl|h'; exact ha
        rcases Finset.mem_insert.mp h' with rfl|h'; exact hb
        exact (r w h').2
      have canReach : ∀ w ∈ next, Reaches n C root w := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl|h'; exact (reachable _ h).tail pair.1
        rcases Finset.mem_insert.mp h' with rfl|h'; exact (reachable _ h).tail pair.2
        exact reachable w (r w h').1
      have witness : ∀ i ∈ U, ∃ w ∈ next, sensitive C w i := by
        intro i hi
        obtain ⟨w,hw,sen⟩ := dep i hi
        by_cases eq : w = n+t
        · subst w
          rcases descend gt ab ha hb ops i sen with sa|sb
          · exact ⟨a,by simp [next],sa⟩
          · exact ⟨b,by simp [next],sb⟩
        · exact ⟨w,by simp [next,rest,eq,hw],sen⟩
      have lower := ih (Nat.le_of_lt gt) next before canReach witness
      have cut : rest.card+1 = W.card := Finset.card_erase_add_one h
      have t1 := Finset.card_insert_le b rest
      have t2 := Finset.card_insert_le a (insert b rest)
      change U.card ≤ (cone n C root t).card + (insert a (insert b rest)).card at lower
      have inc : cone n C root (t+1) = insert t (cone n C root t) := by
        simp [cone,Finset.range_add_one,Finset.filter_insert,reachable _ h]
      rw [inc,Finset.card_insert_of_notMem fresh]
      omega
    · have lower := ih (Nat.le_of_lt gt) W (fun w hw => by
        have := prior w hw
        have ne : w ≠ n+t := fun eq => h (eq ▸ hw)
        omega) reachable dep
      have sub : cone n C root t ⊆ cone n C root (t+1) := by
        intro w hw
        obtain ⟨hr,rs⟩ := Finset.mem_filter.mp hw
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hr)),rs⟩
      exact lower.trans (Nat.add_le_add_right (Finset.card_le_card sub) _)

theorem sensitive_bound {n : ℕ} (C : Circuit) (hc : IsAO2 n C) (w : ℕ) (hw : w < n+C.size)
    (U : Finset (Fin n)) (h : ∀ i ∈ U, sensitive C w i) :
    U.card ≤ (cone n C w C.size).card + 1 := by
  simpa using frontier_bound C hc w C.size (le_refl _) {w} (by simpa) (by simpa using (Relation.ReflTransGen.refl : Reaches n C w w)) U
    (fun i hi => ⟨w,by simp,h i hi⟩)

end VertexPeel.ReusedCone
