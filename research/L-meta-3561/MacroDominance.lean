import PEqualNP.Outside.L_meta_2913
open PEqualNP.Outside.L_meta_2913.Main1672
namespace PEqualNP.Research3561.ProjectedMonotone

/-- Substituting the first wire for the second preserves every positive success
and every negative failure through an arbitrary monotone suffix. -/
def Dominates (a b : Sig) : Prop :=
  (∀ i, b.1.testBit i = true → a.1.testBit i = true) ∧
  (∀ i, a.2.testBit i = true → b.2.testBit i = true)

private theorem liftBool (d x y x' y' : Bool) (hx : x = true → x' = true) (hy : y = true → y' = true) :
    (if d then x || y else x && y) = true → (if d then x' || y' else x' && y') = true := by
  cases d <;> cases x <;> cases y <;> simp_all

theorem binary_dominates {a b c e : Sig} (h : Dominates a c) (g : Dominates b e) (d : Bool) :
    Dominates (bin d a b) (bin d c e) := by
  constructor
  · intro i
    have t := liftBool d _ _ _ _ (h.1 i) (g.1 i)
    cases d <;> simpa [bin,Nat.testBit_or,Nat.testBit_and] using t
  · intro i
    have t := liftBool d _ _ _ _ (h.2 i) (g.2 i)
    cases d <;> simpa [bin,Nat.testBit_or,Nat.testBit_and] using t

private theorem dominates_target {a : Sig} (va : Valid a) (hit : Dominates a target) : a = target := by
  apply Prod.ext
  · apply Nat.eq_of_testBit_eq
    intro i
    change a.1.testBit i = top.testBit i
    by_cases hi : i < 414
    · have pos : top.testBit i = true := by simp [testBit_top,hi]
      exact (hit.1 i pos).trans pos.symm
    · simp [va.1 i (by omega),testBit_top,hi]
  · apply Nat.eq_of_testBit_eq
    intro i
    cases h : a.2.testBit i with
    | false => simp [target]
    | true => have no := hit.2 i h; simp [target] at no

/-- A monotone live suffix can run on any bank that supplies pointwise
dominating projected inputs. Its gate budget can only decrease. -/
theorem transfer (H K : SigHom) {k t : Nat} {S : Finset Sig} (run : Live k t S) (mono : t = 0)
    (T : Finset Sig) (covers : ∀ a ∈ S, ∃ b ∈ T, Dominates (K.fn b) (H.fn a)) :
    Feasible K k T := by
  induction run generalizing T with
  | stop =>
    obtain ⟨b,hb,h⟩ := covers target (Finset.mem_singleton_self _)
    rw [H.htarget] at h
    refine ⟨0,by omega,0,{target},Live.stop,?_⟩
    simpa [Finset.singleton_subset_iff,← dominates_target (K.valid b) h] using Finset.mem_image_of_mem K.fn hb
  | unary => omega
  | @binary k t U a b d _ _ _ _ _ ih =>
    obtain ⟨x,hx,dx⟩ := covers a (Finset.mem_insert_self _ _)
    obtain ⟨y,hy,dy⟩ := covers b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have next : Feasible K k (insert (bin d x y) T) := by
      apply ih mono
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact ⟨bin d x y,Finset.mem_insert_self _ _,by rw [K.hbin,H.hbin]; exact binary_dominates dx dy d⟩
      · obtain ⟨u,hu,du⟩ := covers v (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv))
        exact ⟨u,Finset.mem_insert_of_mem hu,du⟩
    simpa [Finset.insert_eq_of_mem hy,Finset.insert_eq_of_mem hx] using pull_binary next

/-- A constructive gate-by-gate bound for regenerating an entire projected prefix. -/
inductive Prefix : Nat → Finset Sig → Finset Sig → Prop
  | nil (B : Finset Sig) : Prefix 0 B B
  | gate {q : Nat} {B T : Finset Sig} {a b : Sig} (d : Bool)
      (ha : a ∈ B) (hb : b ∈ B) (rest : Prefix q (insert (bin d a b) B) T) : Prefix (q+1) B T

theorem pull_prefix (K : SigHom) {q k : Nat} {B T : Finset Sig} (history : Prefix q B T)
    (h : Feasible K k T) : Feasible K (k+q) B := by
  induction history with
  | nil => simpa using h
  | @gate q B T a b d ha hb _ ih =>
    have step := pull_binary (ih h)
    simpa [Finset.insert_eq_of_mem ha,Finset.insert_eq_of_mem hb,Nat.add_assoc] using step

/-- A 13-gate candidate cannot reach a monotone suffix whose entire projected
live bank can be regenerated one gate more cheaply from the raw inputs. -/
theorem shadow_prefix_bound (H : SigHom) {k q : Nat} {S T : Finset Sig} (bound : k+q ≤ 12)
    (cheaper : Prefix q raw.toFinset T)
    (covers : ∀ a ∈ S, ∃ b ∈ T, Dominates (homProject4.fn b) (H.fn a)) : ¬ Live k 0 S := by
  intro run
  exact root_project4_impossible (feasible_mono (pull_prefix homProject4 cheaper (transfer H homProject4 run rfl T covers)) bound)
end PEqualNP.Research3561.ProjectedMonotone
