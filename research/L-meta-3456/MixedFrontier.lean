import Std

namespace MixedFrontier

/-- An assignment is a pair of supports, one on each side. -/
structure Input (X Y : Type) where
  left : X → Prop
  right : Y → Prop

variable {X Y : Type}
abbrev Signal (X Y : Type) := Input X Y → Prop

def Sub (s t : Input X Y) : Prop :=
  (∀ x, s.left x → t.left x) ∧ ∀ y, s.right y → t.right y

def Mono (f : Signal X Y) : Prop := ∀ s t, Sub s t → f s → f t

def leftOnly (x : X) : Input X Y := ⟨fun v => v = x, fun _ => False⟩
def rightOnly (y : Y) : Input X Y := ⟨fun _ => False, fun v => v = y⟩
def pair (x : X) (y : Y) : Input X Y := ⟨fun v => v = x, fun v => v = y⟩

def join (s t : Input X Y) : Input X Y :=
  ⟨fun x => s.left x ∨ t.left x, fun y => s.right y ∨ t.right y⟩

theorem sub_join_left (s t : Input X Y) : Sub s (join s t) :=
  ⟨fun _ h => Or.inl h, fun _ h => Or.inl h⟩

theorem sub_join_right (s t : Input X Y) : Sub t (join s t) :=
  ⟨fun _ h => Or.inr h, fun _ h => Or.inr h⟩

def Edge (I : X → Y → Prop) (s : Input X Y) : Prop :=
  ∃ x y, I x y ∧ s.left x ∧ s.right y

def RectangleFree (I : X → Y → Prop) : Prop :=
  ∀ x x' y y', x ≠ x' → y ≠ y' → I x y → I x y' → I x' y → I x' y' → False

/-- Whenever both signals fire, the complete output must contain an edge. -/
def Safe (I : X → Y → Prop) (g h : Signal X Y) : Prop :=
  ∀ s, g s → h s → Edge I s

theorem left_neighbour {I : X → Y → Prop} {g h : Signal X Y}
    (gm : Mono g) (hm : Mono h) (safe : Safe I g h)
    {x p : X} {l : Y} (gx : g (leftOnly x)) (pos : h (pair p l)) (bad : ¬ I p l) :
    I x l := by
  let a := leftOnly (Y:=Y) x
  let b := pair p l
  obtain ⟨i,j,edge,hi,hj⟩ := safe (join a b)
    (gm a _ (sub_join_left a b) gx) (hm b _ (sub_join_right a b) pos)
  change i = x ∨ i = p at hi
  change False ∨ j = l at hj
  rcases hi with rfl | rfl <;> rcases hj with no | rfl
  · contradiction
  · exact edge
  · contradiction
  · exact (bad edge).elim

theorem right_neighbour {I : X → Y → Prop} {g h : Signal X Y}
    (gm : Mono g) (hm : Mono h) (safe : Safe I g h)
    {y l : Y} {p : X} (gy : g (rightOnly y)) (pos : h (pair p l)) (bad : ¬ I p l) :
    I p y := by
  let a := rightOnly (X:=X) y
  let b := pair p l
  obtain ⟨i,j,edge,hi,hj⟩ := safe (join a b)
    (gm a _ (sub_join_left a b) gy) (hm b _ (sub_join_right a b) pos)
  change False ∨ i = p at hi
  change j = y ∨ j = l at hj
  rcases hi with no | rfl
  · contradiction
  rcases hj with rfl | rfl
  · exact edge
  · exact (bad edge).elim

/-- The sibling signal accepts at most one nonedge across the bipartition. -/
theorem unique_bad_pair {I : X → Y → Prop} (free : RectangleFree I)
    {g h : Signal X Y} (gm : Mono g) (hm : Mono h) (safe : Safe I g h)
    {x x' : X} {y y' : Y} (xx : x ≠ x') (yy : y ≠ y')
    (gx : g (leftOnly x)) (gx' : g (leftOnly x'))
    (gy : g (rightOnly y)) (gy' : g (rightOnly y'))
    {p q : X} {l m : Y} (pl : h (pair p l)) (qp : h (pair q m))
    (noPL : ¬ I p l) (noQM : ¬ I q m) : p=q ∧ l=m := by
  constructor
  · apply Classical.byContradiction
    intro neq
    exact free p q y y' neq yy
      (right_neighbour gm hm safe gy pl noPL) (right_neighbour gm hm safe gy' pl noPL)
      (right_neighbour gm hm safe gy qp noQM) (right_neighbour gm hm safe gy' qp noQM)
  · apply Classical.byContradiction
    intro neq
    exact free x x' l m xx neq
      (left_neighbour gm hm safe gx pl noPL) (left_neighbour gm hm safe gx qp noQM)
      (left_neighbour gm hm safe gx' pl noPL) (left_neighbour gm hm safe gx' qp noQM)

def OneSide (s : Input X Y) : Prop := (∀ x, ¬ s.left x) ∨ ∀ y, ¬ s.right y

theorem no_one_side {I : X → Y → Prop} {g h : Signal X Y}
    (gm : Mono g) (hm : Mono h) (safe : Safe I g h)
    {x : X} {y : Y} (gx : g (leftOnly x)) (gy : g (rightOnly y))
    (s : Input X Y) (single : OneSide s) : ¬ h s := by
  intro pos
  rcases single with nl | nr
  · let a := rightOnly (X:=X) y
    obtain ⟨p,_,_,hp,_⟩ := safe (join a s)
      (gm a _ (sub_join_left a s) gy) (hm s _ (sub_join_right a s) pos)
    exact hp.elim (fun e => e) (nl p)
  · let a := leftOnly (Y:=Y) x
    obtain ⟨_,l,_,_,hl⟩ := safe (join a s)
      (gm a _ (sub_join_left a s) gx) (hm s _ (sub_join_right a s) pos)
    exact hl.elim (fun e => e) (nr l)

/-- Every positive assignment contains a positive one-side assignment or a positive mixed pair.
    In particular this holds if every minterm of the sibling has size at most two. -/
def BinaryWitness (h : Signal X Y) : Prop :=
  ∀ s, h s → (∃ t, Sub t s ∧ h t ∧ OneSide t) ∨
    ∃ p l, s.left p ∧ s.right l ∧ h (pair p l)

/-- If the sole candidate nonedge is absent, accepted pairs of the sibling are all edges.
    With binary witnesses this gives semantic soundness of the sibling by itself. -/
theorem sibling_safe {I : X → Y → Prop} {g h : Signal X Y} (gm : Mono g) (hm : Mono h)
    (safe : Safe I g h) (binary : BinaryWitness h) {x x' : X} {y y' : Y}
    (gx : g (leftOnly x)) (gx' : g (leftOnly x'))
    (gy : g (rightOnly y)) (gy' : g (rightOnly y'))
    (candidate : ∀ p l, I x l → I x' l → I p y → I p y' → h (pair p l) → I p l) :
    ∀ s, h s → Edge I s := by
  intro s pos
  rcases binary s pos with ⟨t,_,ht,one⟩ | ⟨p,l,hp,hl,ht⟩
  · exact (no_one_side gm hm safe gx gy t one ht).elim
  · refine ⟨p,l,?_,hp,hl⟩
    apply Classical.byContradiction
    intro bad
    exact bad (candidate p l (left_neighbour gm hm safe gx ht bad)
      (left_neighbour gm hm safe gx' ht bad) (right_neighbour gm hm safe gy ht bad)
      (right_neighbour gm hm safe gy' ht bad) ht)

end MixedFrontier
