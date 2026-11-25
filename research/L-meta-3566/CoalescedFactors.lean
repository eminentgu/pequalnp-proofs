import BicliqueFactor

namespace VertexPeel.FactorMatching
variable {A B : Type*}

abbrev Coalesces (G H : Relation A B) (r s : A) : Prop :=
  ∀ p, G r p ∨ G s p → H r p ∧ H s p

abbrev TwoNeighbors (G : Relation A B) (r : A) : Prop :=
  ∃ p q, p≠q ∧ G r p ∧ G r q

private theorem private_col (G : Relation A B) (sq : SquareFree G) {r s : A} (rs : r≠s)
    (deg : TwoNeighbors G r) : ∃ p, G r p ∧ ¬G s p := by
  obtain ⟨p,q,pq,rp,rq⟩ := deg
  by_cases sp : G s p
  · exact ⟨q,rq,fun sq' => sq rs pq rp rq sp sq'⟩
  · exact ⟨p,rp,sp⟩

private theorem at_missing_col (G H K : Relation A B) (e : Exact G H K)
    {r : A} {p : B} (hh : H r p) (off : ¬G r p) {u v : A} (close : Coalesces G K u v)
    (hit : G u p ∨ G v p) : G u p ∧ G v p := by
  have both := close p hit
  exact ⟨(common_col G H K e hh both.1).resolve_left off,(common_col G H K e hh both.2).resolve_left off⟩

private theorem missed_side (G H K : Relation A B) (e : Exact G H K) (sq : SquareFree G)
    {r s u v : A} (rs : r≠s) (uv : u≠v) (dr : TwoNeighbors G r) (ds : TwoNeighbors G s)
    (first : Coalesces G H r s) (second : Coalesces G K u v) :
    ∃ t p, (t=r ∨ t=s) ∧ H t p ∧ ¬G t p ∧ ¬G u p ∧ ¬G v p := by
  obtain ⟨p,rp,sp⟩ := private_col G sq rs dr
  obtain ⟨q,sq',rq⟩ := private_col G sq rs.symm ds
  have pq : p≠q := by rintro rfl; exact sp sq'
  have hp := (first p (Or.inl rp)).2
  have hq := (first q (Or.inr sq')).1
  by_cases hitp : G u p ∨ G v p
  · have t := at_missing_col G H K e hp sp second hitp
    have no : ¬(G u q ∨ G v q) := by
      intro h
      have w := at_missing_col G H K e hq rq second h
      exact sq uv pq t.1 w.1 t.2 w.2
    exact ⟨r,q,Or.inl rfl,hq,rq,fun h => no (Or.inl h),fun h => no (Or.inr h)⟩
  · exact ⟨s,p,Or.inr rfl,hp,sp,fun h => hitp (Or.inl h),fun h => hitp (Or.inr h)⟩

/-- Two strict neighborhood coalescences on the same side are incompatible
    if all four rows have at least two true neighbors each. -/
theorem no_two_row_pairs (G H K : Relation A B) (e : Exact G H K) (sq : SquareFree G)
    {r s u v : A} (rs : r≠s) (uv : u≠v) (dr : TwoNeighbors G r) (ds : TwoNeighbors G s)
    (du : TwoNeighbors G u) (dv : TwoNeighbors G v)
    (first : Coalesces G H r s) (second : Coalesces G K u v) : False := by
  obtain ⟨t,p,side,hp,gp,up,vp⟩ := missed_side G H K e sq rs uv dr ds first second
  have rev : Exact G K H := fun R S => (e R S).trans and_comm
  obtain ⟨z,q,other,kq,gq,rq,sq'⟩ := missed_side G K H rev sq uv rs du dv second first
  rcases cross G H K e hp gp kq gq with pos | pos
  · exact (side.elim (fun h => h ▸ rq) (fun h => h ▸ sq')) pos
  · exact (other.elim (fun h => h ▸ up) (fun h => h ▸ vp)) pos

/-- A row pair in one branch and a column pair in the other are also
    incompatible when their four degrees are at least two. -/
theorem no_row_column_pairs (G H K : Relation A B) (e : Exact G H K) (sq : SquareFree G)
    {r s : A} {u v : B} (rs : r≠s) (uv : u≠v) (dr : TwoNeighbors G r) (ds : TwoNeighbors G s)
    (du : TwoNeighbors (flip G) u) (dv : TwoNeighbors (flip G) v)
    (first : Coalesces G H r s) (second : Coalesces (flip G) (flip K) u v) : False := by
  have sq' : SquareFree (flip G) := by
    intro a b c d ab cd ac ad bc bd
    exact sq cd ab ac bc ad bd
  obtain ⟨p,rp,sp⟩ := private_col G sq rs dr
  obtain ⟨q,sqg,rq⟩ := private_col G sq rs.symm ds
  obtain ⟨x,xu,xv⟩ := private_col (flip G) sq' uv du
  obtain ⟨y,yv,yu⟩ := private_col (flip G) sq' uv.symm dv
  change G x u at xu
  change ¬G x v at xv
  change G y v at yv
  change ¬G y u at yu
  have hp := (first p (Or.inl rp)).2
  have hq := (first q (Or.inr sqg)).1
  have kx := (second x (Or.inl xu)).2
  have ky := (second y (Or.inr yv)).1
  have re : Exact G K H := fun R S => (e R S).trans and_comm
  have ce (z : B) (uw : z=u ∨ z=v) (hit : G r z ∨ G s z) : G r z ∧ G s z := by
    rcases uw with rr | rr <;> subst z
    · exact at_missing_col G K H re ky yu first hit
    · exact at_missing_col G K H re kx xv first hit
  have fe : Exact (flip G) (flip H) (flip K) := transpose G H K e
  have row (t : A) (rw : t=r ∨ t=s) (hit : G t u ∨ G t v) : G t u ∧ G t v := by
    rcases rw with rr|rr <;> subst t
    · exact at_missing_col (flip G) (flip H) (flip K) fe hq rq second hit
    · exact at_missing_col (flip G) (flip H) (flip K) fe hp sp second hit
  have none (t : A) (z : B) (rw : t=r ∨ t=s) (cw : z=u ∨ z=v) : ¬G t z := by
    intro pos
    have ca := ce z cw (rw.elim (fun h => Or.inl (h ▸ pos)) (fun h => Or.inr (h ▸ pos)))
    have rr := row r (Or.inl rfl) (cw.elim (fun h => Or.inl (h ▸ ca.1)) (fun h => Or.inr (h ▸ ca.1)))
    have ss := row s (Or.inr rfl) (cw.elim (fun h => Or.inl (h ▸ ca.2)) (fun h => Or.inr (h ▸ ca.2)))
    exact sq rs uv rr.1 rr.2 ss.1 ss.2
  have xp := (cross G H K e hp sp kx xv).resolve_left (none s v (Or.inr rfl) (Or.inr rfl))
  have xq := (cross G H K e hq rq kx xv).resolve_left (none r v (Or.inl rfl) (Or.inr rfl))
  have yp := (cross G H K e hp sp ky yu).resolve_left (none s u (Or.inr rfl) (Or.inl rfl))
  have yq := (cross G H K e hq rq ky yu).resolve_left (none r u (Or.inl rfl) (Or.inl rfl))
  exact sq (by rintro rfl; exact yu xu) (by rintro rfl; exact sp sqg) xp xq yp yq

end VertexPeel.FactorMatching

#print axioms VertexPeel.FactorMatching.no_two_row_pairs
#print axioms VertexPeel.FactorMatching.no_row_column_pairs
