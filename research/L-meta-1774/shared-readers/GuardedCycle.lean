import Shannon

namespace PEqualNP.Research.GuardedReaders.Cycle

open CircuitLowerBounds EdgeOwnership MetaComplexity MetaComplexity.NestedCover TopForm
attribute [local instance] gateOpDecEq

/-- The cycle 0–1–2–3–4–0, with a pendant at each of 1, 2, 4. -/
abbrev G := edgeGraph 8 [(0,1),(1,2),(2,3),(3,4),(4,0),(4,5),(1,6),(2,7)]

def prefixGates : List Gate := [⟨.or,[0,2]⟩,⟨.or,[1,3]⟩]

private abbrev Ports := Option (Option (Option (Fin 10)))

private def sink : Net Ports :=
  let r₁ : Ports := some (some none)
  let r₂ : Ports := some none
  let r₃ : Ports := none
  let original (i : Fin 10) : Ports := some (some (some i))
  .gate false (original 0) (original 3) <|
  .gate true (some (original 4)) none <|
  .gate false (some (some r₁)) (some (some r₂)) <|
  .gate false (some (some (some r₃))) (some none) <|
  .gate false (some none) none (.output none)

def plan (first second third : Bool) : Readers (Fin 10) :=
  .reader first 1 6 <|
  .reader second (some 2) (some 7) <|
  .reader third (some (some 4)) (some (some 5)) (.finish sink)

def C := attach 8 prefixGates Fin.val ((plan false false false).original 8 9)

def rewritten (p q r : Bool) := attach 8 prefixGates Fin.val ((plan p q r).rerouted 8 9)

theorem original_independent (p q r : Bool) :
    attach 8 prefixGates Fin.val ((plan p q r).original 8 9) = C := by
  cases p <;> cases q <;> cases r <;> rfl

theorem legal : Monotone2 C := by
  apply attach_mono
  simp [prefixGates,Monotone2]

theorem correct : circuitFun 8 C = graphFun G ∅ := by
  funext x
  exact (by decide +kernel : ∀ y : Fin 8 → Bool, circuitFun 8 C y = graphFun G ∅ y) x

theorem girth : (∀ a b c : Fin 8, G.Adj a b → G.Adj b c → ¬ G.Adj c a) ∧ NoFourCycle G :=
  by decide +kernel

theorem ready : ∀ j < C.size, (gateAt C j).op = .and →
    ∃ a b : Fin 8, G.Adj a b ∧ Owns 8 C j a b := by
  intro j hj
  exact (by decide +kernel : ∀ i : Fin 14, (gateAt C i).op = .and →
      ∃ a b : Fin 8, G.Adj a b ∧ Owns 8 C i a b) ⟨j,hj⟩

theorem disjoint : G.Adj 0 1 ∧ G.Adj 2 3 ∧ Owns 8 C 2 (0 : Fin 8) 1 ∧ Owns 8 C 2 (2 : Fin 8) 3 :=
  by decide +kernel

/-- Selecting the left parent at the third reader accepts the nonedge {2,4}; the
right parent instead accepts {1,4}. The other two choices cannot mask the result. -/
def badRow (third : Bool) := pairInput (if third then (2 : Fin 8) else 1) (4 : Fin 8)

theorem every_choice_fails (p q r : Bool) : circuitFun 8 (rewritten p q r) (badRow r) = true ∧
    graphFun G ∅ (badRow r) = false := by revert p q r; decide +kernel

theorem no_parent_only_exchange (p q r : Bool) : circuitFun 8 (rewritten p q r) ≠ graphFun G ∅ := by
  intro h
  have on := congrFun h (badRow r)
  rw [(every_choice_fails p q r).1,(every_choice_fails p q r).2] at on
  contradiction

def ten : Circuit := ⟨[⟨.or,[0,2]⟩,⟨.or,[8,6]⟩,⟨.and,[1,9]⟩,
  ⟨.or,[3,7]⟩,⟨.and,[2,11]⟩,⟨.or,[0,3]⟩,⟨.or,[13,5]⟩,
  ⟨.and,[4,14]⟩,⟨.or,[10,12]⟩,⟨.or,[16,15]⟩],17⟩

theorem shorter : Monotone2 ten ∧ circuitFun 8 ten = graphFun G ∅ ∧ ten.size + 4 = C.size := by
  refine ⟨by simp [ten,Monotone2],?_,rfl⟩
  funext x
  exact (by decide +kernel : ∀ y : Fin 8 → Bool, circuitFun 8 ten y = graphFun G ∅ y) x

theorem notMinimal : ¬ IsMinimalMonoCircuit 8 C := by
  intro least
  have lower := least.2 ten shorter.1 (shorter.2.1.trans correct.symm)
  have size := shorter.2.2
  omega

end PEqualNP.Research.GuardedReaders.Cycle
