import EncodedBank

namespace PEqualNP.Research3561.CubicObstruction
open PEqualNP.Research3561 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Monotonicity of project circuit evaluation, from the public L-meta-1018 proof.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj


def face (a b c : Bool) : List Bool :=
  [false,false,false,a,false,false,false,false,false,b,c]

def input (m : Nat) : Fin 9 → Bool := fun i => m.testBit i.val
def dominating (a b : Bool) := if !a then 16 else if !b then 10 else 9

theorem full_row : encoded (input 24) = face true true true ∧ edgeF (input 24) = true := by decide
theorem negative_rows : ∀ a b : Bool, edgeF (input (dominating a b)) = false := by decide
theorem domination : ∀ a b c : Bool, (a && b && c) = false →
    ∀ i : Fin 11, (face a b c).getD i false = true →
      (encoded (input (dominating a b))).getD i false = true := by decide

/-- Every monotone lift has a literal AND3 on the subcube supported on raw3, OR04 and OR41. -/
theorem compulsory_cube (C : Circuit) (legal : Monotone2 C)
    (correct : ∀ x : Fin 9 → Bool, C.eval (encoded x) = edgeF x) :
    ∀ a b c : Bool, C.eval (face a b c) = (a && b && c) := by
  intro a b c
  by_cases h : (a && b && c) = true
  · simp only [Bool.and_eq_true] at h
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := h
    rw [← full_row.1,correct,full_row.2]
    rfl
  · have off : (a && b && c) = false := Bool.eq_false_iff.mpr h
    rw [off]
    apply Bool.eq_false_iff.mpr
    intro high
    have hleg : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or := by
      intro g hg; simpa using (legal g hg).1
    have dom : ∀ i, (face a b c).getD i false = true →
        (encoded (input (dominating a b))).getD i false = true := by
      intro i hi
      by_cases valid : i < 11
      · exact domination a b c off ⟨i,valid⟩ hi
      · rw [List.getD_eq_default _ _ (by simp [face]; omega)] at hi
        contradiction
    have mono := wiresFrom_mono C.gates hleg (face a b c) (encoded (input (dominating a b)))
      (by simp [face,encoded]) dom C.output high
    change C.eval (encoded _) = true at mono
    rw [correct,negative_rows] at mono
    contradiction

theorem two_literals_survive : ∀ i j : Fin 11,
    (face true true true).getD i false = true → (face true true true).getD j false = true →
      ∃ a b c : Bool, (a && b && c) = false ∧ (face a b c).getD i false = true ∧
        (face a b c).getD j false = true := by decide

/-- In particular no independent-wire disjunction of binary products represents the lift.
Allowing the two product operands to coincide also covers single-literal terms. -/
theorem no_quadratic (C : Circuit) (legal : Monotone2 C)
    (correct : ∀ x : Fin 9 → Bool, C.eval (encoded x) = edgeF x)
    (terms : List (Fin 11 × Fin 11)) :
    ¬ (∀ w : List Bool, w.length = 11 →
      C.eval w = terms.any (fun ij => w.getD ij.1 false && w.getD ij.2 false)) := by
  intro hrep
  have hf := compulsory_cube C legal correct
  have yes : terms.any (fun ij => (face true true true).getD ij.1 false &&
      (face true true true).getD ij.2 false) = true := by
    rw [← hrep _ rfl,hf]; rfl
  obtain ⟨⟨i,j⟩,hmem,hij⟩ := List.any_eq_true.mp yes
  have hboth : (face true true true).getD i false = true ∧ (face true true true).getD j false = true := by
    simpa only [Bool.and_eq_true] using hij
  obtain ⟨hi,hj⟩ := hboth
  obtain ⟨a,b,c,off,h1,h2⟩ := two_literals_survive i j hi hj
  have impossible := hf a b c
  rw [hrep _ rfl,off] at impossible
  have yes' : terms.any (fun ij => (face a b c).getD ij.1 false && (face a b c).getD ij.2 false) = true :=
    List.any_eq_true.mpr ⟨(i,j),hmem,by simpa only [Bool.and_eq_true] using And.intro h1 h2⟩
  exact Bool.noConfusion (yes'.symm.trans impossible)

def star : Circuit :=
  ⟨[⟨.or,[3,5]⟩,⟨.and,[7,8]⟩,⟨.or,[0,5]⟩,⟨.and,[1,10]⟩,
    ⟨.or,[1,3]⟩,⟨.or,[12,6]⟩,⟨.and,[2,13]⟩,⟨.or,[0,6]⟩,⟨.or,[15,7]⟩,⟨.and,[4,16]⟩,
    ⟨.or,[9,11]⟩,⟨.or,[18,14]⟩,⟨.or,[19,17]⟩],20⟩

theorem simultaneous_reuse : star.size = 13 ∧
    (star.gates.flatMap Gate.inputs).count 0 = 2 ∧ (star.gates.flatMap Gate.inputs).count 1 = 2 ∧
    ∀ z : Fin 8 → Bool, circuitFun 8 star z =
      ((z 0 && z 1) || (z 1 && z 2) || (z 2 && z 3) || (z 0 && z 4) ||
       (z 1 && z 5) || (z 2 && z 6) || (z 3 && z 7) || (z 4 && z 6) ||
       (z 5 && z 7) || (z 7 && z 4)) := by decide +kernel

end PEqualNP.Research3561.CubicObstruction
