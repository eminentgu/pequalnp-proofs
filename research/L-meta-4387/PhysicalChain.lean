import PEqualNP.Defs.TopForm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity NestedCover PEqualNP.TopForm

namespace Packed4387

abbrev Col := BitVec 58

def row (k : ℕ) (vs : List Col) := vs.map (fun v => v.getLsbD k)

def Step (pool : List Col) (v : Col) : Prop :=
  ∃ a ∈ pool, ∃ b ∈ pool, v = a &&& b ∨ v = a ||| b

def Chain (bank vs : List Col) : Prop :=
  ∀ j : Fin vs.length, Step (bank ++ vs.take j.val) (vs.get j)

def firstGate : Gate := ⟨.or,[0,1]⟩

/-- Column realizations record the complete wire vector at every bit,
    as well as the physical first gate. -/
structure Real (raw pool : List Col) (gs : List Gate) : Prop where
  count : raw.length + gs.length = pool.length
  first : gs.head? = some firstGate
  ao : IsAO2 raw.length ⟨gs,0⟩
  wires : ∀ k : ℕ, (Circuit.mk gs 0).wires (row k raw) = row k pool

private theorem append_ok {n : ℕ} {gs : List Gate} (ok : IsAO2 n ⟨gs,0⟩)
    (g : Gate) (op : g.op = .and ∨ g.op = .or) (len : g.inputs.length = 2)
    (refs : ∀ j ∈ g.inputs, j < n+gs.length) : IsAO2 n ⟨gs++[g],0⟩ := by
  constructor
  · intro h hh
    rcases List.mem_append.mp hh with hh | hh
    · exact ok.1 _ hh
    · have := List.mem_singleton.mp hh; subst h; exact op
  constructor
  · intro j hj a ha
    change j < (gs++[g]).length at hj
    change a ∈ ((gs++[g]).getD j _).inputs at ha
    by_cases old : j < gs.length
    · rw [List.getD_append _ _ _ _ old] at ha
      exact ok.2.1 j old a ha
    · have eq : j = gs.length := by simp at hj; omega
      subst j
      simpa using (refs a (by simpa using ha))
  · intro h hh
    rcases List.mem_append.mp hh with hh | hh
    · exact ok.2.2 _ hh
    · have := List.mem_singleton.mp hh; subst h; exact len

private theorem val_get (k : ℕ) (vs : List Col) (i : Fin vs.length) :
    (row k vs).getD i.val false = (vs.get i).getLsbD k := by
  rw [List.getD_eq_getElem _ _ (by simp [row])]
  simp [row]

private theorem extend {raw pool : List Col} {gs : List Gate} (built : Real raw pool gs)
    {v : Col} (step : Step pool v) : ∃ g, Real raw (pool++[v]) (gs++[g]) := by
  obtain ⟨a,ha,b,hb,which⟩ := step
  obtain ⟨i,ra⟩ := List.mem_iff_get.mp ha
  obtain ⟨j,rb⟩ := List.mem_iff_get.mp hb
  have ci : i.val < raw.length+gs.length := by rw [built.count]; exact i.isLt
  have cj : j.val < raw.length+gs.length := by rw [built.count]; exact j.isLt
  have push (op : GateOp) (binary : op = .and ∨ op = .or)
      (bits : ∀ k, op.eval [a.getLsbD k,b.getLsbD k] = v.getLsbD k) :
      Real raw (pool++[v]) (gs++[⟨op,[i.val,j.val]⟩]) := by
    refine ⟨by simp [built.count,← Nat.add_assoc],?_,?_,?_⟩
    · cases eq : gs with
      | nil => simp [eq] at built; have h := built.first; contradiction
      | cons h t => simpa [eq] using built.first
    · apply append_ok built.ao _ binary rfl
      intro ref href
      simp only [List.mem_cons,List.not_mem_nil,or_false] at href
      rcases href with rfl | rfl <;> assumption
    · intro k
      have app :
          (Circuit.mk (gs++[⟨op,[i.val,j.val]⟩]) 0).wires (row k raw) =
          (Circuit.mk gs 0).wires (row k raw) ++
            [op.eval [((Circuit.mk gs 0).wires (row k raw)).getD i.val false,
              ((Circuit.mk gs 0).wires (row k raw)).getD j.val false]] := by
        simp only [Circuit.wires,List.foldl_append,List.foldl_cons,List.foldl_nil,List.map_cons,List.map_nil]
      rw [app,built.wires k,val_get k pool i,val_get k pool j,ra,rb,bits k]
      simp [row]
  rcases which with rfl | rfl
  · exact ⟨_,push .and (Or.inl rfl) (fun k => by simp [GateOp.eval])⟩
  · exact ⟨_,push .or (Or.inr rfl) (fun k => by simp [GateOp.eval])⟩

/-- Compile a sequence that uses only AND/OR on previously available columns. -/
theorem compile {raw base : List Col} {start : List Gate} (initial : Real raw base start)
    (xs : List Col) (chain : Chain base xs) : ∃ gs, Real raw (base++xs) gs := by
  induction xs using List.reverseRecOn with
  | nil => simpa using Exists.intro start initial
  | append_singleton xs v ih =>
    have prev : Chain base xs := by
      intro j
      have h := chain ⟨j.val, by simp⟩
      simpa only [List.get_eq_getElem,List.getElem_append_left j.isLt,
        List.take_append_of_le_length j.isLt.le] using h
    have step := chain ⟨xs.length,by simp⟩
    simp only [List.get_eq_getElem,List.getElem_append_right (Nat.le_refl _),Nat.sub_self,
      List.getElem_cons_zero,List.take_append_length] at step
    obtain ⟨gs,old⟩ := ih prev
    obtain ⟨g,ext⟩ := extend old step
    exact ⟨_,by simpa only [List.append_assoc] using ext⟩

end Packed4387
