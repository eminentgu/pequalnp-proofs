import Tagged292
import PackedIso
import Mathlib.Data.List.GetD

namespace VertexPeel.Mask4.RawCheck
open Packed
set_option maxRecDepth 100000

/-- A witness stores its target row in the low nine bits followed by fourteen
    hexadecimal digits for each direction of the vertex permutation. -/
def accept (z : Code) (w : ℕ) : Bool :=
  let i := w % 512
  let target := tagged292.getD i 0
  let forward := (w >>> 9) % (2^56)
  let backward := w >>> 65
  decide (i < tagged292.length ∧ (z = target ∨ Valid z target forward backward))

abbrev Closed (l : List Code) :=
  ∀ z ∈ l, ∃ t ∈ tagged292, Nonempty (graph z ≃g graph t)

private theorem sound (z : Code) (w : ℕ) (ok : accept z w = true) :
    ∃ t ∈ tagged292, Nonempty (graph z ≃g graph t) := by
  let i := w%512
  let t := tagged292.getD i 0
  obtain ⟨hi,cert⟩ := (of_decide_eq_true ok : i < tagged292.length ∧
    (z = t ∨ Valid z t ((w >>> 9) % (2^56)) (w >>> 65)))
  have mem : t ∈ tagged292 := by
    rw [show t = tagged292[i] from List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem _
  refine ⟨t,mem,?_⟩
  rcases cert with rfl | maps
  · exact ⟨RelIso.refl _⟩
  · exact ⟨isoOfValid maps⟩

theorem block (codes : List Code) (data : List ℕ) (lengths : codes.length = data.length)
    (ok : (codes.zip data).all (fun x => accept x.1 x.2) = true) : Closed codes := by
  induction codes generalizing data with
  | nil => simp [Closed]
  | cons z zs ih =>
    cases data with
    | nil => simp at lengths
    | cons d ds =>
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at ok
      intro t ht
      rcases List.mem_cons.mp ht with rfl | rest
      · exact sound _ _ ok.1
      · exact ih ds (by simpa using lengths) ok.2 t rest

theorem append {a b : List Code} (ca : Closed a) (cb : Closed b) : Closed (a++b) := by
  intro z hz
  exact (List.mem_append.mp hz).elim (ca z) (cb z)

end VertexPeel.Mask4.RawCheck
