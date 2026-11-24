import EncodedBank
namespace PEqualNP.Research3561
namespace ReadOnceKW
abbrev Row := Fin 414

def KWSolution (S : Finset Sig) : Prop := ∃ label : Row → Row → Sig,
  (∀ p n, label p n ∈ S ∧ bit true p (label p n) = true ∧ bit false n (label p n) = false) ∧
  ∀ p n p' n', label p n = label p' n' → label p n' = label p n

private def choose (d : Bool) (a b : Sig) (p n : Row) : Sig :=
  if d then (if bit true p a then a else b) else (if bit false n a then b else a)

private theorem choose_valid {a b : Sig} {d : Bool} {p n : Row}
    (hp : bit true p (bin d a b) = true) (hn : bit false n (bin d a b) = false) :
    bit true p (choose d a b p n) = true ∧ bit false n (choose d a b p n) = false := by
  rw [bit_bin] at hp hn
  cases d <;> cases hpA : bit true p a <;> cases hnA : bit false n a <;> simp_all [choose]

private def fetched (f : Row → Row → Sig) (g : Sig) (d : Bool) (a b : Sig) (p n : Row) : Sig :=
  if f p n = g then choose d a b p n else f p n

private theorem split_rect {f : Row → Row → Sig} (d : Bool) {g a b : Sig}
    (isRect : ∀ p n p' n', f p n = f p' n' → f p n' = f p n)
    (oldA : ∀ p n, f p n ≠ a) (oldB : ∀ p n, f p n ≠ b)
    (p n p' n' : Row) (heq : fetched f g d a b p n = fetched f g d a b p' n') :
    fetched f g d a b p n' = fetched f g d a b p n := by
  let recover := fun z : Sig => if z=a ∨ z=b then g else z
  have undo (x y : Row) : recover (fetched f g d a b x y) = f x y := by
    by_cases h : f x y = g
    · rw [fetched,ite_eq_left h,h]
      cases d <;> simp only [choose,Bool.false_eq_true,ite_false,ite_true] <;> split <;> simp [recover]
    · simp [fetched,h,recover,oldA,oldB]
  have same : f p n = f p' n' := (undo p n).symm.trans ((congrArg recover heq).trans (undo p' n'))
  have cross := isRect p n p' n' same
  by_cases h : f p n = g
  · have h' : f p' n' = g := same.symm.trans h
    rw [fetched,ite_eq_left (cross.trans h),fetched,ite_eq_left h]
    cases d with
    | true => rfl
    | false => simpa [fetched,h,h',choose] using heq.symm
  · simp [fetched,cross,h]

private theorem kw_step {a b : Sig} {d : Bool} {U : Finset Sig}
    (an : a ∉ U) (bn : b ∉ U) (gnew : bin d a b ∉ insert a (insert b U))
    (sol : KWSolution (insert (bin d a b) U)) : KWSolution (insert a (insert b U)) := by
  obtain ⟨f,legal,rect⟩ := sol
  let g := bin d a b
  have ga : g ≠ a := by intro e; exact gnew (Finset.mem_insert.mpr (Or.inl e))
  have gb : g ≠ b := by intro e; exact gnew (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl e)))
  have oldA (p n : Row) : f p n ≠ a := by
    rcases Finset.mem_insert.mp (legal p n).1 with eq | mem
    · exact eq ▸ ga
    · exact fun eq => an (eq ▸ mem)
  have oldB (p n : Row) : f p n ≠ b := by
    rcases Finset.mem_insert.mp (legal p n).1 with eq | mem
    · exact eq ▸ gb
    · exact fun eq => bn (eq ▸ mem)
  refine ⟨fetched f g d a b,?_,split_rect d rect oldA oldB⟩
  intro p n
  by_cases e : f p n = g
  · rw [fetched,ite_eq_left e]
    have fs := (legal p n).2
    rw [e] at fs
    exact ⟨by cases d <;> simp only [choose,Bool.false_eq_true,ite_false,ite_true] <;> split <;> simp,
      choose_valid fs.1 fs.2⟩
  · rw [fetched,ite_eq_right e]
    exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ((Finset.mem_insert.mp (legal p n).1).resolve_left e)),(legal p n).2⟩

theorem kw_of_live {k t : Nat} {S : Finset Sig} (run : Live k t S) (mono : t = 0) (sat : S.card = k+1) : KWSolution S := by
  induction run with
  | stop => exact ⟨fun _ _ => target,fun p n => ⟨Finset.mem_singleton_self _,by simp [bit,target,testBit_top,p.isLt],by simp [bit,target]⟩,fun _ _ _ _ _ => rfl⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d _ _ ab gf tail ih =>
    have gn : bin d a b ∉ U := fun h => gf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have cap := (live_size tail).2
    rw [Finset.card_insert_of_notMem gn] at cap
    have first := Finset.card_insert_le a (insert b U)
    have second := Finset.card_insert_le b U
    have bn : b ∉ U := by intro hb; rw [Finset.insert_eq_of_mem hb] at sat; have := Finset.card_insert_le a U; omega
    have an : a ∉ U := by intro ha; rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ha)] at sat; omega
    apply kw_step an bn gf (ih mono ?_)
    rw [Finset.card_insert_of_notMem gn]
    omega

/-- A private KW cell forces its unique separating wire as a label. If the rectangular hulls of
two forced labels overlap, no monotone liveness trace saturating the cardinality bound exists. -/
def Private (S : Finset Sig) (p n : Row) (a : Sig) : Prop :=
  ∀ x ∈ S, bit true p x = true → bit false n x = false → x = a

theorem crossed_private_cells {k : Nat} {S : Finset Sig} (sat : S.card = k+1)
    {a b : Sig} (ab : a ≠ b) {p n pa na pb nb : Row}
    (ap : Private S p na a) (an : Private S pa n a) (bp : Private S p nb b) (bn : Private S pb n b) : ¬ Live k 0 S := by
  intro live
  obtain ⟨f,leg,rect⟩ := kw_of_live live rfl sat
  have forced {x p n} (h : Private S p n x) : f p n = x :=
    h _ (leg p n).1 (leg p n).2.1 (leg p n).2.2
  have eA := (rect p na pa n ((forced ap).trans (forced an).symm)).trans (forced ap)
  have eB := (rect p nb pb n ((forced bp).trans (forced bn).symm)).trans (forced bp)
  exact ab (eA.symm.trans eB)
/-- Check a private cell using only two table bits per wire. -/
def privateCell (ws : List Sig) (p n : Row) (a : Sig) : Bool :=
  ws.all (fun x => !(bit true p x) || bit false n x || decide (x=a))

private theorem private_of_cell {w : List Sig} {p n : Row} {a : Sig} (h : privateCell w p n a = true) :
    Private w.toFinset p n a := by
  intro x hx pos neg
  have yes := List.all_eq_true.mp h x (List.mem_toFinset.mp hx)
  simpa [pos,neg] using yes

structure Crossing where
  a : Nat
  b : Nat
  p : Row
  n : Row
  pa : Row
  na : Row
  pb : Row
  nb : Row

def verifyCrossing (ws : List Sig) (c : Crossing) : Bool :=
  let a := ws.getD c.a zero
  let b := ws.getD c.b zero
  decide (a ≠ b) && privateCell ws c.p c.na a && privateCell ws c.pa c.n a &&
    privateCell ws c.p c.nb b && privateCell ws c.pb c.n b

theorem verified_crossing {ws : List Sig} {c : Crossing} {k : Nat}
    (sat : ws.toFinset.card = k+1) (h : verifyCrossing ws c = true) : ¬ Live k 0 ws.toFinset := by
  simp only [verifyCrossing,Bool.and_eq_true,decide_eq_true_eq] at h
  exact crossed_private_cells sat h.1.1.1.1 (private_of_cell h.1.1.1.2) (private_of_cell h.1.1.2)
    (private_of_cell h.1.2) (private_of_cell h.2)

/-- Both free-parameter AND/OR branches pass basic 414-pair separation on this concrete two-gate
prefix. An eight-coordinate certificate rejects all eleven-gate monotone completions in one step. -/
def exampleState : List Sig := signals ++ [bin false raw0 (bin true raw4 raw1),bin true raw0 (bin true raw4 raw1)]

theorem concrete_crossing : ¬ Live 11 0 exampleState.toFinset :=
  verified_crossing (c := ⟨1,2,4,188,5,227,8,253⟩) (by decide +kernel) (by decide +kernel)

end ReadOnceKW
end PEqualNP.Research3561
