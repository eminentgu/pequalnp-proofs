import MixedFrontier

namespace MixedFrontier

variable {X Y : Type}

theorem sub_self (s : Input X Y) : Sub s s := ⟨fun _ h => h, fun _ h => h⟩

theorem left_single_sub {s : Input X Y} {x : X} (hx : s.left x) : Sub (leftOnly x) s := by
  constructor
  · rintro v rfl; exact hx
  · intro _ no; exact no.elim

theorem right_single_sub {s : Input X Y} {y : Y} (hy : s.right y) : Sub (rightOnly y) s := by
  constructor
  · intro _ no; exact no.elim
  · rintro v rfl; exact hy

/-- Every independent assignment extends to another independent assignment that activates g. -/
def ExtendsNegatives (I : X → Y → Prop) (g : Signal X Y) : Prop :=
  ∀ s, ¬Edge I s → ∃ t, Sub s t ∧ ¬Edge I t ∧ g t

theorem left_closed_star {I : X → Y → Prop} {g : Signal X Y} (gm : Mono g) (x : X)
    (center : g (leftOnly x)) (neighbors : ∀ y, I x y → g (rightOnly y)) :
    ExtendsNegatives I g := by
  intro s independent
  by_cases h : ∃ y, I x y ∧ s.right y
  · obtain ⟨y,edge,hy⟩ := h
    exact ⟨s,sub_self s,independent,gm _ s (right_single_sub hy) (neighbors y edge)⟩
  · let a := leftOnly (Y:=Y) x
    refine ⟨join a s,sub_join_right a s,?_,gm a _ (sub_join_left a s) center⟩
    rintro ⟨p,l,edge,hp,hl⟩
    change p=x ∨ s.left p at hp
    change False ∨ s.right l at hl
    rcases hl with no | hl
    · exact no
    rcases hp with rfl | hp
    · exact h ⟨l,edge,hl⟩
    · exact independent ⟨p,l,edge,hp,hl⟩

theorem right_closed_star {I : X → Y → Prop} {g : Signal X Y} (gm : Mono g) (y : Y)
    (center : g (rightOnly y)) (neighbors : ∀ x, I x y → g (leftOnly x)) :
    ExtendsNegatives I g := by
  intro s independent
  by_cases h : ∃ x, I x y ∧ s.left x
  · obtain ⟨x,edge,hx⟩ := h
    exact ⟨s,sub_self s,independent,gm _ s (left_single_sub hx) (neighbors x edge)⟩
  · let a := rightOnly (X:=X) y
    refine ⟨join a s,sub_join_right a s,?_,gm a _ (sub_join_left a s) center⟩
    rintro ⟨p,l,edge,hp,hl⟩
    change False ∨ s.left p at hp
    change l=y ∨ s.right l at hl
    rcases hp with no | hp
    · exact no
    rcases hl with rfl | hl
    · exact h ⟨p,edge,hp⟩
    · exact independent ⟨p,l,edge,hp,hl⟩

/-- The increased circuit stays exact if every negative can be extended to where the
    substituted gate was already true. This also applies to gates with multiple consumers. -/
theorem safe_increase {I : X → Y → Prop} {g raised : Signal X Y} (rm : Mono raised)
    (extension : ExtendsNegatives I g) (keepsPositive : ∀ s, Edge I s → raised s)
    (agreesWhenHigh : ∀ s, g s → raised s → Edge I s) :
    ∀ s, raised s ↔ Edge I s := by
  intro s
  constructor
  · intro accepted
    apply Classical.byContradiction
    intro noEdge
    obtain ⟨t,sub,noEdge',high⟩ := extension s noEdge
    exact noEdge' (agreesWhenHigh t high (rm s t sub accepted))
  · exact keepsPositive s

end MixedFrontier
