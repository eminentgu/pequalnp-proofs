import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
namespace VertexPeel.SideReaders

def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def Agree (B : Finset Nat) (x y : List Bool) :=
  x.length = y.length ∧ ∀ i, i ∉ B → x.getD i false = y.getD i false

private theorem appendAgree {B x y} (h : Agree B x y) (b : Bool) :
    Agree B (x ++ [b]) (y ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  by_cases hx : i < x.length
  · rw [List.getD_append _ _ _ _ hx, List.getD_append _ _ _ _ (h.1 ▸ hx)]
    exact h.2 _ hi
  · have hlen := h.1
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), List.getElem?_append_right (by omega : y.length ≤ i), h.1]

private theorem skipAgree {B x y} (h : Agree B x y) (gs : List Gate)
    (skip : ∀ g ∈ gs, ∀ j ∈ g.inputs, j ∉ B) :
    Agree B (gs.foldl step x) (gs.foldl step y) := by
  induction gs generalizing x y with
  | nil => exact h
  | cons g gs ih =>
    apply ih
    · have e := List.map_congr_left (l := g.inputs) (fun j hj => h.2 j (skip g (by simp) j hj))
      simp only [step, e]
      exact appendAgree h _
    · intro k hk
      exact skip k (by simp [hk])

private theorem rawRead {w : List Bool} {j : Nat} (hj : j < w.length) :
    ∀ gs : List Gate, (gs.foldl step w).getD j false = w.getD j false := by
  intro gs
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (by simp [step]; omega), step, List.getD_append _ _ _ _ hj]

private theorem length_run (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih, step, Nat.add_comm, Nat.add_left_comm]

private theorem getDInit (x : Fin n → Bool) (j : Fin n) :
    (List.ofFn x).getD j.val false = x j := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp),
    Option.getD_some, List.getElem_ofFn]

/-- On the all-true side, every wire earlier than the first read of the other side is true. -/
theorem before_first {w : List Bool} {B : Finset Nat} (gs : List Gate)
    (initial : ∀ j < w.length, j ∉ B → w.getD j false = true)
    (valid : ∀ i g, gs[i]? = some g →
      (g.op = .and ∨ g.op = .or) ∧ g.inputs ≠ [] ∧
      ∀ j ∈ g.inputs, j < w.length + i ∧ j ∉ B) :
    ∀ j < (gs.foldl step w).length, j ∉ B → (gs.foldl step w).getD j false = true := by
  induction gs generalizing w with
  | nil => exact initial
  | cons g gs ih =>
    have ⟨op, nonempty, ports⟩ := valid 0 g (by simp)
    have all : ∀ j ∈ g.inputs, w.getD j false = true := by
      intro j hj
      exact initial j (by simpa using (ports j hj).1) (ports j hj).2
    have out : g.op.eval (g.inputs.map fun j => w.getD j false) = true := by
      rcases op with e | e
      · simp [e, GateOp.eval, List.all_eq_true]
        simpa only [List.getD_eq_getElem?_getD] using all
      · obtain ⟨v,hv⟩ := List.exists_mem_of_ne_nil g.inputs nonempty
        simp [e, GateOp.eval, List.any_eq_true]
        exact ⟨v, hv, all v hv⟩
    apply ih
    · intro j hj hb
      by_cases old : j < w.length
      · rw [step,List.getD_append _ _ _ _ old]; exact initial j old hb
      · have z : j = w.length := by simp [step] at hj; omega
        subst j
        simp [step, List.getD_eq_getElem?_getD]
        simpa only [List.getD_eq_getElem?_getD] using out
    · intro i g' h
      have arg := valid (i+1) g' (by simpa using h)
      simpa [step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using arg

/-- Two input coordinates with a shared exclusive OR reader are indistinguishable
    outside those coordinates on every pair of inputs for which that OR is true. -/
theorem shared_or_collision {n : Nat} {a b : Fin n} {pre post : List Gate} {g : Gate} {o : Nat}
    (hop : g.op = .or) (ha : a.val ∈ g.inputs) (hb : b.val ∈ g.inputs)
    (skip : ∀ q ∈ pre ++ post, ∀ j ∈ q.inputs, j ≠ a.val ∧ j ≠ b.val)
    (hout : o ≠ a.val ∧ o ≠ b.val)
    (x y : Fin n → Bool) (hx : x a = true) (hy : y b = true)
    (agree : ∀ z, z ≠ a → z ≠ b → x z = y z) :
    (⟨pre ++ g :: post,o⟩ : Circuit).eval (List.ofFn x) =
      (⟨pre ++ g :: post,o⟩ : Circuit).eval (List.ofFn y) := by
  let B : Finset Nat := {a.val,b.val}
  have init : Agree B (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro i hi
    by_cases h : i < n
    · change (List.ofFn x).getD (⟨i,h⟩ : Fin n).val false = (List.ofFn y).getD (⟨i,h⟩ : Fin n).val false
      rw [getDInit,getDInit]
      exact agree _ (by rintro rfl; simp [B] at hi) (by rintro rfl; simp [B] at hi)
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using Nat.le_of_not_gt h : (List.ofFn x).length ≤ i), List.getElem?_eq_none (by simpa using Nat.le_of_not_gt h : (List.ofFn y).length ≤ i)]
  have excluded : ∀ q ∈ pre ++ post, ∀ j ∈ q.inputs, j ∉ B := by
    intro q hq j hj
    simpa [B, not_or] using skip q hq j hj
  have hpre := skipAgree init pre (fun q hq => excluded q (by simp [hq]))
  have val (t : Fin n → Bool) (u : Fin n) (hu : u.val ∈ g.inputs) (ht : t u = true) :
      g.op.eval (g.inputs.map fun j => (pre.foldl step (List.ofFn t)).getD j false) = true := by
    simp [hop,GateOp.eval,List.any_eq_true]
    refine ⟨u.val,hu,?_⟩
    change (pre.foldl step (List.ofFn t)).getD u.val false = true
    rw [rawRead (by simp) pre, getDInit, ht]
  have hstep : Agree B (step (pre.foldl step (List.ofFn x)) g) (step (pre.foldl step (List.ofFn y)) g) := by
    simp only [step,val x a ha hx,val y b hb hy]
    exact appendAgree hpre _
  have final := skipAgree hstep post (fun q hq => excluded q (by simp [hq]))
  change ((pre ++ g :: post).foldl step (List.ofFn x)).getD o false = _
  change _ = ((pre ++ g :: post).foldl step (List.ofFn y)).getD o false
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
  exact final.2 o (by simpa [B,not_or] using hout)


/-- When the earliest read of the chosen input side ORs a bit with a wire
    outside that side, the all-true opposite side already satisfies the OR.
    If no other gate reads the bit, turning it on does not change the output. -/
theorem single_or_collision {n : Nat} {a : Fin n} {pre post : List Gate} {g : Gate} {o j : Nat}
    (B : Finset Nat) (hop : g.op = .or) (ha : a.val ∈ g.inputs) (hj : j ∈ g.inputs)
    (outside : j ∉ B) (back : j < n + pre.length)
    (valid : ∀ i q, pre[i]? = some q →
      (q.op = .and ∨ q.op = .or) ∧ q.inputs ≠ [] ∧
      ∀ z ∈ q.inputs, z < n + i ∧ z ∉ B)
    (skip : ∀ q ∈ pre ++ post, a.val ∉ q.inputs)
    (hout : o ≠ a.val)
    (x y : Fin n → Bool) (base : ∀ z : Fin n, z.val ∉ B → x z = true)
    (flip : y a = true) (agree : ∀ z, z ≠ a → x z = y z) :
    (⟨pre ++ g :: post,o⟩ : Circuit).eval (List.ofFn x) =
      (⟨pre ++ g :: post,o⟩ : Circuit).eval (List.ofFn y) := by
  have initial : ∀ v < (List.ofFn x).length, v ∉ B → (List.ofFn x).getD v false = true := by
    intro v hv hvB
    let z : Fin n := ⟨v, by simpa using hv⟩
    exact (getDInit x z).trans (base z hvB)
  have isTrue := before_first pre initial (by simpa using valid) j
    (by simpa [length_run] using back) outside
  have init : Agree {a.val} (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro i hi
    by_cases h : i < n
    · change (List.ofFn x).getD (⟨i,h⟩ : Fin n).val false = (List.ofFn y).getD (⟨i,h⟩ : Fin n).val false
      rw [getDInit,getDInit]
      exact agree _ (by rintro rfl; simp at hi)
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using Nat.le_of_not_gt h : (List.ofFn x).length ≤ i), List.getElem?_eq_none (by simpa using Nat.le_of_not_gt h : (List.ofFn y).length ≤ i)]
  have excluded : ∀ q ∈ pre ++ post, ∀ z ∈ q.inputs, z ∉ ({a.val} : Finset Nat) := by
    intro q hq z hz
    simp only [Finset.mem_singleton]
    rintro rfl
    exact skip q hq hz
  have hpre := skipAgree init pre (fun q hq => excluded q (by simp [hq]))
  have rawY : (pre.foldl step (List.ofFn y)).getD a.val false = true := by
    rw [rawRead (by simp) pre, getDInit, flip]
  have val (t : Fin n → Bool) (u : Nat) (hu : u ∈ g.inputs)
      (ht : (pre.foldl step (List.ofFn t)).getD u false = true) :
      g.op.eval (g.inputs.map fun z => (pre.foldl step (List.ofFn t)).getD z false) = true := by
    simp [hop,GateOp.eval,List.any_eq_true]
    exact ⟨u,hu,ht⟩
  have hstep : Agree {a.val} (step (pre.foldl step (List.ofFn x)) g) (step (pre.foldl step (List.ofFn y)) g) := by
    simp only [step,val x j hj isTrue,val y a ha rawY]
    exact appendAgree hpre _
  have final := skipAgree hstep post (fun q hq => excluded q (by simp [hq]))
  change ((pre ++ g :: post).foldl step (List.ofFn x)).getD o false = _
  change _ = ((pre ++ g :: post).foldl step (List.ofFn y)).getD o false
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
  exact final.2 o (by simpa using hout)


open PEqualNP.MetaComplexity.NestedCover PEqualNP.MetaComplexity

def bits (S : Finset (Fin n)) (u : Fin n) : Bool := decide (u ∈ S)

private lemma b_iff (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) :
    graphFun G ∅ (bits S) = true ↔ ∃ u ∈ S, ∃ v ∈ S, G.Adj u v := by
  classical
  simp [graphFun,bits]
  tauto

lemma pair_iff (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (bits {u,v}) = true ↔ G.Adj u v := by
  rw [b_iff]
  constructor
  · rintro ⟨y,hy,z,hz,h⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy hz
    rcases hy with rfl | rfl <;> rcases hz with rfl | rfl
    · exact False.elim ((G.loopless.irrefl _) h)
    · exact h
    · exact h.symm
    · exact False.elim ((G.loopless.irrefl _) h)
  · intro h
    exact ⟨u,by simp,v,by simp,h⟩

theorem no_raw_output {C : Circuit} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (correct : circuitFun n C = graphFun G ∅) (a : Fin n) : C.output ≠ a.val := by
  intro e
  have h := congrFun correct (bits {a,a})
  change (C.gates.foldl step (List.ofFn (bits {a,a}))).getD C.output false = _ at h
  rw [e,rawRead (by simp),getDInit] at h
  have h' : graphFun G ∅ (bits {a,a}) = true := by simpa [bits] using h.symm
  exact (G.loopless.irrefl _) ((pair_iff G a a).mp h')

/-- Distinct neighborhoods forbid two side vertices sharing an exclusive OR reader. -/
theorem graph_shared_or_impossible {n : Nat} {a b : Fin n} {pre post : List Gate} {g : Gate} {o : Nat}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hop : g.op = .or) (ha : a.val ∈ g.inputs) (hb : b.val ∈ g.inputs)
    (skip : ∀ q ∈ pre ++ post, ∀ j ∈ q.inputs, j ≠ a.val ∧ j ≠ b.val)
    (witness : ∃ u, G.Adj u a ∧ ¬ G.Adj u b)
    (correct : circuitFun n ⟨pre ++ g :: post,o⟩ = graphFun G ∅) : False := by
  obtain ⟨u,hu,hn⟩ := witness
  have eq := shared_or_collision hop ha hb skip
    ⟨no_raw_output G correct a, no_raw_output G correct b⟩
    (bits {u,a}) (bits {u,b}) (by simp [bits]) (by simp [bits]) (by
      intro z hza hzb
      simp [bits,hza,hzb])
  change circuitFun n ⟨pre ++ g :: post,o⟩ _ = circuitFun n ⟨pre ++ g :: post,o⟩ _ at eq
  rw [correct] at eq
  exact hn ((pair_iff G u b).mp (eq.symm.trans ((pair_iff G u a).mpr hu)))

/-- If the complement of B is independent, a vertex with a neighbor in that
    complement cannot make its only appearance in the first B reader in an OR
    with a wire outside B. -/
theorem graph_single_or_impossible {n : Nat} {a : Fin n} {pre post : List Gate} {g : Gate} {o j : Nat}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (B : Finset Nat)
    (independent : ∀ u v : Fin n, u.val ∉ B → v.val ∉ B → ¬ G.Adj u v)
    (neighbor : ∃ u : Fin n, u.val ∉ B ∧ G.Adj u a)
    (hop : g.op = .or) (ha : a.val ∈ g.inputs) (hj : j ∈ g.inputs)
    (outside : j ∉ B) (back : j < n + pre.length)
    (valid : ∀ i q, pre[i]? = some q →
      (q.op = .and ∨ q.op = .or) ∧ q.inputs ≠ [] ∧
      ∀ z ∈ q.inputs, z < n + i ∧ z ∉ B)
    (skip : ∀ q ∈ pre ++ post, a.val ∉ q.inputs)
    (correct : circuitFun n ⟨pre ++ g :: post,o⟩ = graphFun G ∅) : False := by
  classical
  let A : Finset (Fin n) := Finset.univ.filter fun u => u.val ∉ B
  have neg : ¬ graphFun G ∅ (bits A) = true := by
    rw [b_iff]
    rintro ⟨u,hu,v,hv,hadj⟩
    exact independent u v (by simpa [A] using hu) (by simpa [A] using hv) hadj
  obtain ⟨u,hu,hua⟩ := neighbor
  have pos : graphFun G ∅ (bits (insert a A)) = true := (b_iff _ _).mpr
    ⟨u,Finset.mem_insert_of_mem (by simpa [A] using hu),a,Finset.mem_insert_self _ _,hua⟩
  have eq := single_or_collision B hop ha hj outside back valid skip (no_raw_output G correct a)
    (bits A) (bits (insert a A)) (by intro z hz; simp [bits,A,hz]) (by simp [bits])
    (by intro z hz; simp [bits,hz])
  change circuitFun n ⟨pre ++ g :: post,o⟩ _ = circuitFun n ⟨pre ++ g :: post,o⟩ _ at eq
  rw [correct] at eq
  exact neg (eq.trans pos)


/-- In a C4-free graph, a vertex of degree at least two always has a neighbor
    not belonging to the neighborhood of a fixed, distinct vertex. -/
theorem separated_neighbor (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (noSquare : PEqualNP.TopForm.NoFourCycle G) {a b : Fin n}
    (hne : a ≠ b) (high : 2 ≤ G.degree a) : ∃ u, G.Adj u a ∧ ¬ G.Adj u b := by
  classical
  by_contra! off
  have sub : G.neighborFinset a ⊆ Finset.univ.filter (fun u => G.Adj a u ∧ G.Adj b u) := by
    intro u hu
    have h : G.Adj a u := (G.mem_neighborFinset a u).mp hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h,(off u h.symm).symm⟩
  have low := (Finset.card_le_card sub).trans (noSquare a b hne)
  rw [G.card_neighborFinset_eq_degree] at low
  omega

/-- The first gate to read the chosen side cannot be an OR with two distinct
    inputs unless some side input of that gate is read in a different gate. -/
theorem first_or_has_second_reader {n : Nat} {a : Fin n} {pre post : List Gate} {g : Gate} {o j : Nat}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (B : Finset Nat)
    (bounded : ∀ b ∈ B, b < n)
    (independent : ∀ u v : Fin n, u.val ∉ B → v.val ∉ B → ¬ G.Adj u v)
    (neighbor : ∃ u : Fin n, u.val ∉ B ∧ G.Adj u a)
    (noSquare : PEqualNP.TopForm.NoFourCycle G) (high : 2 ≤ G.degree a)
    (hop : g.op = .or) (ha : a.val ∈ g.inputs) (inSide : a.val ∈ B)
    (hj : j ∈ g.inputs) (distinct : j ≠ a.val) (back : j < n + pre.length)
    (valid : ∀ i q, pre[i]? = some q →
      (q.op = .and ∨ q.op = .or) ∧ q.inputs ≠ [] ∧
      ∀ z ∈ q.inputs, z < n + i ∧ z ∉ B)
    (correct : circuitFun n ⟨pre ++ g :: post,o⟩ = graphFun G ∅) :
    ∃ t ∈ B, t ∈ g.inputs ∧ ∃ q ∈ pre ++ post, t ∈ q.inputs := by
  classical
  by_contra! never
  by_cases side : j ∈ B
  · let b : Fin n := ⟨j,bounded j side⟩
    have hb : a ≠ b := by intro h; exact distinct (congrArg Fin.val h).symm
    refine graph_shared_or_impossible G hop ha (show b.val ∈ g.inputs from hj) ?_
      (separated_neighbor G noSquare hb high) correct
    intro q hq z hz
    exact ⟨fun h => never a.val inSide ha q hq (h ▸ hz),
      fun h => never j side hj q hq (by simpa only [h] using hz)⟩
  · exact graph_single_or_impossible G B independent neighbor hop ha hj side back valid
      (fun q hq => never a.val inSide ha q hq) correct

end VertexPeel.SideReaders
