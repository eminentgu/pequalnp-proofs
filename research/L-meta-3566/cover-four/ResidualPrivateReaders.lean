import ResidualPartner

namespace VertexPeel.CoverFourResidual
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadTwo
open VertexPeel.ZeroFold VertexPeel.SideReaders VertexPeel.SidePeel VertexPeel.PendantCross

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private abbrev F15 := PEqualNP.EdgeOwnership.edgeGraph 9 (table 15).2

private theorem neighbor15 : ∀ b : Fin 9, b.val ∈ subdivisionSide → ∃ u : Fin 9, F15.Adj u b := by decide +kernel

private theorem mono_of_ao {n : ℕ} {C : Circuit} (ao : IsAO2 n C) : Monotone2 C := by
  intro g hg
  obtain h | h := ao.1 g hg <;> simp [h,ao.2.2 g hg]

abbrev CofactorBound15 :=
  ∀ (b : Fin 9), 4 ≤ b.val → ∀ C : Circuit, Monotone2 C →
    (∀ x : Fin 9 → Bool, circuitFun 9 C x = graphFun F15 ∅ (Function.update x b false)) →
    12 ≤ C.size

private theorem falseNoTwo (cofactor : CofactorBound15) {C : Circuit} (ao : IsAO2 9 C)
    (ok : circuitFun 9 C = graphFun F15 ∅) (small : C.size ≤ 13)
    {b : Fin 9} (side : b.val ∈ subdivisionSide) {j k : ℕ}
    (hj : j < C.size) (hk : k < C.size) (ne : j ≠ k)
    (mj : ¬ Mg C {b} j) (mk : ¬ Mg C {b} k) : False := by
  classical
  let F := (Finset.range C.size).filter (Mg C {b})
  have sub : insert j (insert k F) ⊆ Finset.range C.size := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact Finset.mem_range.mpr hj
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact Finset.mem_range.mpr hk
    exact (Finset.mem_filter.mp ht).1
  have count := Finset.card_le_card sub
  simp [F,ne,mj,mk] at count
  obtain ⟨D,dao,ev,sz⟩ := ZeroFold.compile C ao {b}
  have lo : 4 ≤ b.val := (by decide : ∀ t : Fin 9, t.val ∈ subdivisionSide → 4 ≤ t.val) b side
  have bound := cofactor b lo D (mono_of_ao dao) (fun x => by
    rw [ev]
    change circuitFun 9 C (zr {b} x) = _
    rw [ok]
    congr 1
    funext t
    by_cases e : t=b
    · subst t; simp [zr]
    · rw [Function.update_of_ne e]; simp [zr,e])
  omega

private theorem distinctExclusive {C : Circuit} (ao : IsAO2 9 C)
    (ok : circuitFun 9 C = graphFun F15 ∅)
    (unique : ∀ (b : Fin 9), b.val ∈ subdivisionSide → ∀ j (hj : j < C.size),
      b.val ∈ C.gates[j].inputs → ∀ k (hk : k < C.size), b.val ∈ C.gates[k].inputs → j=k)
    {a b : Fin 9} (sa : a.val ∈ subdivisionSide) (sb : b.val ∈ subdivisionSide) (ab : a ≠ b)
    {r : ℕ} (hr : r < C.size) (op : C.gates[r].op = .or)
    (ra : a.val ∈ C.gates[r].inputs) (rb : b.val ∈ C.gates[r].inputs) : False := by
  obtain ⟨u,ua,ub⟩ := (by decide +kernel : ∀ v w : Fin 9, v.val ∈ subdivisionSide →
    w.val ∈ subdivisionSide → v ≠ w → ∃ t, F15.Adj t v ∧ ¬F15.Adj t w) a b sa sb ab
  let x := bits {u,a}
  let y := bits {u,b}
  have diff : wval C x C.output ≠ wval C y C.output := by
    change circuitFun 9 C x ≠ circuitFun 9 C y
    rw [ok]
    intro eq
    exact ub ((pair_iff _ u b).mp (eq.symm.trans ((pair_iff _ u a).mpr ua)))
  obtain ⟨k,hk,_,d,t,ht,read⟩ := crosses_diff C ao {a.val,b.val} x y (by
    intro v hv
    have va : v ≠ a := by rintro rfl; simp at hv
    have vb : v ≠ b := by rintro rfl; simp at hv
    simp [x,y,bits,va,vb]) diff (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or]; exact ⟨no_raw_output F15 ok a,no_raw_output F15 ok b⟩)
  have kr : k=r := by
    rcases Finset.mem_insert.mp ht with h | h
    · exact unique a sa k hk (h ▸ read) r hr ra
    · exact unique b sb k hk ((Finset.mem_singleton.mp h) ▸ read) r hr rb
  subst k
  have onA : wval C x a.val = true := (wval_in C x a).trans (by simp [x,bits])
  have onB : wval C y b.val = true := (wval_in C y b).trans (by simp [y,bits])
  exact d ((on_of_or C ao r hr op a.val ra x onA).trans (on_of_or C ao r hr op b.val rb y onB).symm)

/-- A hypothesized 13-gate circuit has a zero intermediate and a consuming gate
    on every assignment excluding the unsubdivided edge. -/
theorem forcedPair15 (cofactor : CofactorBound15) {C : Circuit} (ao : IsAO2 9 C)
    (ok : circuitFun 9 C = graphFun F15 ∅) (small : C.size ≤ 13) :
    ∃ j k, ∃ hj : j < C.gates.length, ∃ hk : k < C.gates.length, j ≠ k ∧
      (∀ x : Fin 9 → Bool, ¬ (x 0 = true ∧ x 1 = true) → wval C x (9+j) = false) ∧
      9+j ∈ C.gates[k].inputs := by
  classical
  let hit (i : ℕ) := ∃ hi : i < C.size, ∃ b : Fin 9, b.val ∈ subdivisionSide ∧ b.val ∈ C.gates[i].inputs
  have hits : ∃ i, hit i := by
    obtain ⟨i,hi,rb⟩ := raw_reader F15 C ao ok 4 0 (by decide)
    exact ⟨i,hi,4,by decide,rb⟩
  let r := Nat.find hits
  obtain ⟨hr,b,side,br⟩ := Nat.find_spec hits
  change r < C.size at hr
  change b.val ∈ C.gates[r].inputs at br
  have unique (v : Fin 9) (hv : v.val ∈ subdivisionSide) (j : ℕ) (hj : j < C.size)
      (rj : v.val ∈ C.gates[j].inputs) (k : ℕ) (hk : k < C.size) (rk : v.val ∈ C.gates[k].inputs) : j=k := by
    by_contra ne
    have off := fv_in0 C {v} v (by simp)
    exact falseNoTwo cofactor ao ok small hv hj hk ne (kill C ao _ j hj _ rj off) (kill C ao _ k hk _ rk off)
  have zg := fv_in0 C {b} b (by simp)
  have notZero : fv C {b} (9+r) ≠ fun _ => false := by
    intro h
    obtain ⟨u,ub⟩ := neighbor15 b side
    have rem : ∃ v w, F15.Adj v w ∧ v ≠ b ∧ w ≠ b :=
      ⟨0,1,by decide,(by decide : ∀ b : Fin 9, b.val ∈ subdivisionSide → 0 ≠ b) b side,
        (by decide : ∀ b : Fin 9, b.val ∈ subdivisionSide → 1 ≠ b) b side⟩
    obtain ⟨k,hk,ne,mk⟩ := second_of_zero F15 C ao ok b u ub rem r hr h
    exact falseNoTwo cofactor ao ok small side hk hr ne mk (kill C ao _ r hr _ br zg)
  obtain ⟨l,m,ports,hl,hm,ops⟩ := two 9 C ao r hr
  have which : b.val = l ∨ b.val = m := by simpa [ports] using br
  have isOr := ops.resolve_left (by
    intro hand
    apply notZero
    funext x
    rw [fv_and C {b} r l m hr ports hl hm hand]
    rcases which with e | e <;> rw [← e,zg] <;> simp)
  have lm : l ≠ m := by
    rintro rfl
    have bb : b.val = l := which.elim id id
    apply notZero
    funext x
    rw [fv_or C {b} r l l hr ports hl hm isOr,←bb,zg]
    rfl
  obtain ⟨d,dr,back,bd⟩ : ∃ d, d ∈ C.gates[r].inputs ∧ d < 9+r ∧ b.val ≠ d := by
    rcases which with e | e
    · exact ⟨m,by simp [ports],hm,by omega⟩
    · exact ⟨l,by simp [ports],hl,by omega⟩
  have outside : d ∉ subdivisionSide := by
    intro ds
    have bound : d < 9 := (by decide : ∀ s ∈ subdivisionSide, s < 9) d ds
    let v : Fin 9 := ⟨d,bound⟩
    exact distinctExclusive ao ok unique side (show v.val ∈ subdivisionSide from ds)
      (fun e => bd (congrArg Fin.val e)) hr isOr br dr
  have skip (i : ℕ) (hi : i < C.gates.length) (lt : i < r) (t : ℕ) (read : t ∈ C.gates[i].inputs) :
      t ∉ subdivisionSide := by
    intro h
    have bound : t < 9 := (by decide : ∀ s ∈ subdivisionSide, s < 9) t h
    exact (Nat.find_min hits lt) ⟨hi,⟨t,bound⟩,h,read⟩
  have off := firstPartner ao ok r hr isOr b side br (fun i hi bi => unique b side i hi bi r hr br)
    skip d dr back outside
  obtain ⟨j,jr,eq⟩ := internal_of_vanishes back off
  exact ⟨j,r,lt_trans jr (show r < C.gates.length from hr),hr,jr.ne,eq ▸ off,eq ▸ dr⟩

/-- A 12-gate lower bound on the designated rows excludes every AO₂ circuit of size ≤13. -/
theorem lower15_of_rows {ι : Type*} (sample : ι → Fin 9 → Bool)
    (missing : ∀ a, ¬ (sample a 0 = true ∧ sample a 1 = true))
    (cofactor : CofactorBound15)
    (partialBound : ∀ D : Circuit, Monotone2 D →
      (∀ a, circuitFun 9 D (sample a) = graphFun F15 ∅ (sample a)) → 12 ≤ D.size)
    (erase : ∀ (C : Circuit), IsAO2 9 C → ∀ {j k : ℕ} (hj : j < C.gates.length) (hk : k < C.gates.length),
      j ≠ k → (∀ a, wval C (sample a) (9+j) = false) → 9+j ∈ C.gates[k].inputs →
      ∃ D : Circuit, IsAO2 9 D ∧ (∀ a, circuitFun 9 D (sample a) = circuitFun 9 C (sample a)) ∧
        D.size + 2 ≤ C.size)
    (C : Circuit) (ao : IsAO2 9 C) (ok : circuitFun 9 C = graphFun F15 ∅) : 14 ≤ C.size := by
  by_contra! h
  obtain ⟨j,k,hj,hk,ne,off,reads⟩ := forcedPair15 cofactor ao ok (by omega)
  obtain ⟨D,dao,same,save⟩ := erase C ao hj hk ne (fun a => off _ (missing a)) reads
  have lower := partialBound D (mono_of_ao dao) (fun a => (same a).trans (congrFun ok _))
  omega
end VertexPeel.CoverFourResidual
#print axioms VertexPeel.CoverFourResidual.forcedPair15
#print axioms VertexPeel.CoverFourResidual.lower15_of_rows
