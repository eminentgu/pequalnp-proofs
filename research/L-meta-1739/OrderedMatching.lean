import CyclicBounds

namespace Research.CyclicBounds

open Research.LeafCharge PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4837_aux GraphCircuit4837
open scoped Classical

private def enable {n k : ℕ} (L : Fin k → Fin n) (s : ℕ) (x : Fin n → Bool) (v : Fin n) : Bool :=
  decide (∃ i, i.val < s ∧ L i = v) || x v

private theorem enable_succ {n k : ℕ} (L : Fin k → Fin n) (j : Fin k) (x : Fin n → Bool) :
    enable L j.val (pin (L j) (L j) x) = enable L (j.val+1) x := by
  funext v
  rw [Bool.eq_iff_iff]
  simp only [enable,Bool.or_eq_true,decide_eq_true_eq]
  by_cases hv : v=L j
  · simp [pin,hv]
    exact Or.inl ⟨j,by omega,rfl⟩
  · simp only [pin,if_neg hv]
    apply or_congr_left
    constructor
    · rintro ⟨i,hi,e⟩
      exact ⟨i,by omega,e⟩
    · rintro ⟨i,hi,e⟩
      refine ⟨i,?_,e⟩
      by_contra! bad
      have eq : i=j := Fin.ext (by omega)
      exact hv (e.symm.trans (congrArg L eq))

/-- The occupied left endpoints are independent. An earlier left endpoint cannot meet a
later right endpoint. Edges among the right endpoints and outside the matching are unrestricted. -/
theorem orderedMatchingAnd {n k : ℕ} (G : SimpleGraph (Fin n)) (L R : Fin k → Fin n)
    (edge : ∀ j, G.Adj (L j) (R j))
    (indep : ∀ i j, ¬ G.Adj (L i) (L j))
    (order : ∀ i j, i<j → ¬ G.Adj (L i) (R j))
    (C : Circuit) (hm : Monotone2 C) (det : detects G C) : k ≤ ands C.gates := by
  have emptyRow (s : ℕ) : C.eval (List.ofFn (enable L s (fun _ => false))) = false := by
    rw [Bool.eq_false_iff]
    intro yes
    obtain ⟨v,w,adj,hv,hw⟩ := (det _).mp yes
    simp only [enable,Bool.or_false,decide_eq_true_eq] at hv hw
    obtain ⟨i,_,rfl⟩ := hv
    obtain ⟨j,_,rfl⟩ := hw
    exact indep i j adj
  have stage (s : ℕ) (bound : s ≤ k) : ∃ D : Circuit, Monotone2 D ∧
      ands D.gates + s ≤ ands C.gates ∧
      ∀ x, D.eval (List.ofFn x) = C.eval (List.ofFn (enable L s x)) := by
    induction s with
    | zero =>
      exact ⟨C,hm,by omega,fun x => by have e : enable L 0 x = x := by funext i; simp [enable]
                                       rw [e]⟩
    | succ s ih =>
      let j : Fin k := ⟨s,by omega⟩
      obtain ⟨D,dm,account,values⟩ := ih (by omega)
      let a := fun i : Fin n => decide (i=R j)
      let b := pin (L j) (L j) a
      have low : D.eval (List.ofFn a) = false := by
        rw [values,Bool.eq_false_iff]
        intro yes
        obtain ⟨v,w,adj,hv,hw⟩ := (det _).mp yes
        simp only [enable,a,Bool.or_eq_true,decide_eq_true_eq] at hv hw
        rcases hv with ⟨i,hi,rfl⟩ | rfl <;> rcases hw with ⟨t,ht,rfl⟩ | rfl
        · exact indep i t adj
        · exact order i j hi adj
        · exact order t j ht adj.symm
        · exact adj.ne rfl
      have high : D.eval (List.ofFn b) = true := by
        rw [values]
        apply (det _).mpr
        have ne := (edge j).ne.symm
        exact ⟨L j,R j,edge j, by simp [enable,b,pin],by simp [enable,b,pin,ne,a]⟩
      obtain ⟨E,em,lt,ev⟩ := restrictAnd D (L j) (L j) dm a b
        (fun i => by contrapose!; intro ne; simp [b,pin,ne]) (by simp [low,high])
        ⟨fun _ => false,by rw [values,enable_succ L j]; exact emptyRow _⟩
      refine ⟨E,em,by omega,fun x => ?_⟩
      rw [ev,values,enable_succ L j]
  obtain ⟨_,_,bound,_⟩ := stage k (le_refl _)
  omega

end Research.CyclicBounds
