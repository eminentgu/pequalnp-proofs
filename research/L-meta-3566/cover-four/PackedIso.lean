import Mask4

namespace VertexPeel.Mask4.Packed
/-- The i-th base-16 digit gives the image of vertex i (all tables have ≤14 vertices). -/
def label (p v : ℕ) := (p >>> (4*v)) % 16

abbrev Order (z : Code) := 4 + (columns z).length

def Valid (z t : Code) (f g : ℕ) : Prop :=
  (∀ u : Fin (Order z), label f u < Order t ∧ label g (label f u) = u.val) ∧
  (∀ v : Fin (Order t), label g v < Order z ∧ label f (label g v) = v.val) ∧
  ∀ u v : Fin (Order z), adjB t (label f u) (label f v) = adjB z u v

instance (z t : Code) (f g : ℕ) : Decidable (Valid z t f g) := by
  unfold Valid
  infer_instance

def isoOfValid {z t : Code} {f g : ℕ} (h : Valid z t f g) : graph z ≃g graph t where
  toFun u := ⟨label f u,(h.1 u).1⟩
  invFun v := ⟨label g v,(h.2.1 v).1⟩
  left_inv u := Fin.ext (h.1 u).2
  right_inv v := Fin.ext (h.2.1 v).2
  map_rel_iff' := by
    intro u v
    change (adjB t (label f u) (label f v) = true) ↔ adjB z u v = true
    rw [h.2.2 u v]

end VertexPeel.Mask4.Packed
