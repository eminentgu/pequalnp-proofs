import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Research2836.Monotone

def rows : List Nat := [3,6,12,17,24,33,42,50,66,69,104,116,132,138,160,201,208,261,264,276,288,320,385,402]
def positives : List Nat := [3,6,12,17,24,33,66,132,160,264,288,320]
def bits (r : Nat) : Fin 9 → Bool := fun i => r.testBit i.val
def edge (x : Fin 9 → Bool) :=
  ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any fun e =>
    x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 e)
def bank (k : Fin 9) (x : Fin 9 → Bool) :=
  let p := k = 0 ∨ k = 4
  List.ofFn (if p then Function.update x k false else x) ++
    [if p then x 0 || x 4 else false, if p then x k || x (if k = 0 then 3 else 1) else x 0 || x 4 || x k]
def source (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 4]
def From1922 : Prop := ∀ C : Circuit, Monotone2 C →
  (∀ r ∈ rows, C.eval (source (bits r)) = decide (r ∈ positives)) → 15 ≤ C.size
def Uniform : Prop := ∀ (k : Fin 9) (C : Circuit), FanInTwo C → C.size ≤ 13 →
  (∀ h ∈ C.gates, h.op ≠ GateOp.not) → (∀ x, C.eval (bank k x) = edge x) → False

private def blank (k : Fin 9) : Nat := if k = 0 ∨ k = 4 then k.val else 9
private def redirect (k : Fin 9) (i : Nat) := if i = blank k then 24 else i
private def orGate (k : Fin 9) : Gate := ⟨.or, if k = 0 then [0,3] else if k = 4 then [4,1] else [9,k.val]⟩
private def rename (k : Fin 9) (g : Gate) : Gate := ⟨g.op,g.inputs.map (redirect k)⟩
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
private def restore (k : Fin 9) (C : Circuit) : Circuit :=
  ⟨orGate k :: C.gates.map (rename k), redirect k C.output⟩

private theorem blank_lt (k : Fin 9) : blank k < 11 := by unfold blank; split <;> omega
private theorem at_last (w : List Bool) (v : Bool) : (w ++ [v]).getD w.length false = v := by simp
private theorem at_old (w : List Bool) (v : Bool) (i : Nat) (h : i ≠ w.length) :
    (w ++ [v]).getD i false = w.getD i false := by
  by_cases hi : i < w.length
  · exact List.getD_append _ _ _ _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private theorem simulation (k : Fin 9) (gs : List Gate) (w z : List Bool)
    (len : w.length = z.length) (enough : 11 ≤ w.length) (bound : w.length + gs.length ≤ 24)
    (eq : ∀ i, w.getD i false = z.getD (redirect k i) false) :
    ∀ i, (gs.foldl step w).getD i false = ((gs.map (rename k)).foldl step z).getD (redirect k i) false := by
  induction gs generalizing w z with
  | nil => exact eq
  | cons g gs ih =>
    simp only [List.map_cons,List.foldl_cons]
    have lengthW : (step w g).length = w.length + 1 := by simp [step]
    have lengthZ : (step z (rename k g)).length = z.length + 1 := by simp [step]
    have before : w.length < 24 := by simp only [List.length_cons] at bound; omega
    apply ih _ _ (by omega) (by omega) (by simp only [List.length_cons] at bound; omega)
    intro i
    have pins : g.inputs.map (fun j => w.getD j false) =
        (g.inputs.map (redirect k)).map (fun j => z.getD j false) := by
      rw [List.map_map]; exact List.map_congr_left (fun j _ => eq j)
    by_cases h : i = w.length
    · subst i
      have rid : redirect k w.length = z.length := by
        have lt := blank_lt k
        unfold redirect
        rw [if_neg (show w.length ≠ blank k by omega)]
        exact len
      rw [rid]
      change (w ++ [_]).getD w.length false = (z ++ [_]).getD z.length false
      simp only [at_last]
      simpa only [rename] using congrArg g.op.eval pins
    · have h' : redirect k i ≠ z.length := by unfold redirect; split <;> omega
      simp only [step,rename]
      rw [at_old _ _ _ h,at_old _ _ _ h',eq]

private theorem rows_ok : ∀ r ∈ rows, edge (bits r) = decide (r ∈ positives) := by decide +kernel
private theorem initial : ∀ k : Fin 9, ∀ r ∈ rows, ∀ i : Fin 11,
    (bank k (bits r)).getD i.val false =
      (step (source (bits r)) (orGate k)).getD (redirect k i.val) false := by decide +kernel

theorem transport (raw : From1922) : Uniform := by
  intro k C fan sz noNot correct
  let D := restore k C
  have hmono : Monotone2 D := by
    intro g hg
    change g ∈ orGate k :: C.gates.map (rename k) at hg
    rcases List.mem_cons.mp hg with rfl | h
    · refine ⟨Or.inr rfl,?_⟩
      by_cases a : k = 0 <;> by_cases b : k = 4 <;> simp [orGate,a,b]
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
      obtain ⟨op,num⟩ := fan a ha
      refine ⟨?_,by simpa [rename] using num⟩
      rcases op with a | b | c
      · exact Or.inl a
      · exact Or.inr b
      · exact False.elim (noNot _ ha c)
  have eval (r : Nat) (hr : r ∈ rows) : D.eval (source (bits r)) = decide (r ∈ positives) := by
    let w := bank k (bits r)
    let z := step (source (bits r)) (orGate k)
    have hw : w.length = 11 := by simp [w,bank]
    have hz : z.length = 11 := by simp [z,step,source]
    have rel (i : Nat) : w.getD i false = z.getD (redirect k i) false := by
      by_cases hi : i < 11
      · exact initial k r hr ⟨i,hi⟩
      · have ri : redirect k i = i := by
          have lt := blank_lt k
          simp [redirect,show i ≠ blank k by omega]
        rw [ri,List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
    have sim := simulation k C.gates w z (by omega) (by omega)
      (by change C.gates.length ≤ 13 at sz; omega) rel C.output
    exact sim.symm.trans ((correct (bits r)).trans (rows_ok r hr))
  have lo := raw D hmono eval
  change 15 ≤ (orGate k :: C.gates.map (rename k)).length at lo
  simp only [List.length_cons,List.length_map] at lo
  change C.gates.length ≤ 13 at sz
  omega

end PEqualNP.Research2836.Monotone
