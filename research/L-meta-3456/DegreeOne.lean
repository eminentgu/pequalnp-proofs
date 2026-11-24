import StarForest

namespace SingletonFiniteFormula.Formula

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {N : Nat} (I : Fin N → Fin N → Prop)

private abbrev Centers := {p : Fin N // ∃ l, I p l}

private noncomputable def spokes (p : Centers I) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (I p.val)

private theorem mem_spokes {p : Centers I} {l : Fin N} : l ∈ spokes I p ↔ I p.val l := by
  classical
  simp [spokes]

private noncomputable def group (p : Centers I) : Star (Fin (N+N)) :=
  let first := p.property.choose
  ⟨Fin.castAdd N p.val, Fin.natAdd N first,
    ((spokes I p).erase first).toList.map (Fin.natAdd N)⟩

private theorem in_group (p : Centers I) (v : Fin (N+N)) :
    v ∈ (group I p).neighbors ↔ ∃ l : Fin N, I p.val l ∧ Fin.natAdd N l = v := by
  classical
  let first : Fin N := p.property.choose
  have first_valid : I p.val first := p.property.choose_spec
  change v ∈ Fin.natAdd N first :: ((spokes I p).erase first).toList.map (Fin.natAdd N) ↔ _
  simp only [List.mem_cons, List.mem_map, Finset.mem_toList, Finset.mem_erase, mem_spokes]
  constructor
  · rintro (rfl | ⟨l,⟨_,hi⟩,rfl⟩)
    · exact ⟨_,first_valid,rfl⟩
    · exact ⟨_,hi,rfl⟩
  · rintro ⟨l,hi,rfl⟩
    by_cases h : l = first
    · exact Or.inl (h ▸ rfl)
    · exact Or.inr ⟨_,⟨h,hi⟩,rfl⟩

private theorem left_ne_right (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro equality
  have a := congrArg Fin.val equality
  simp at a
  omega

private theorem group_nodup (p : Centers I) : (group I p).variables.Nodup := by
  classical
  apply List.nodup_cons.mpr
  constructor
  · intro h
    obtain ⟨l,_,e⟩ := (in_group I p _).mp h
    exact left_ne_right p.val l e.symm
  · let first := p.property.choose
    change (Fin.natAdd N first :: ((spokes I p).erase first).toList.map (Fin.natAdd N)).Nodup
    apply List.nodup_cons.mpr
    constructor
    · intro h
      obtain ⟨l,hl,e⟩ := List.mem_map.mp h
      have eq : l = first := Fin.ext (by simpa using congrArg Fin.val e)
      exact (Finset.mem_erase.mp (Finset.mem_toList.mp hl)).1 eq
    · apply List.Nodup.map _ (Finset.nodup_toList _)
      intro a b eq
      exact Fin.ext (by simpa using congrArg Fin.val eq)

private theorem groups_disjoint (hdeg : ∀ p q l, I p l → I q l → p = q)
    {p q : Centers I} (h : p ≠ q) :
    (group I p).variables.Disjoint (group I q).variables := by
  intro v hp hq
  change v ∈ Fin.castAdd N p.val :: (group I p).neighbors at hp
  change v ∈ Fin.castAdd N q.val :: (group I q).neighbors at hq
  rw [List.mem_cons, in_group] at hp hq
  rcases hp with rp | ⟨a,ha,ea⟩ <;> rcases hq with rq | ⟨b,hb,eb⟩
  · exact h (Subtype.ext (Fin.ext (by simpa using congrArg Fin.val (rp.symm.trans rq))))
  · exact left_ne_right p.val b (rp.symm.trans eb.symm)
  · exact left_ne_right q.val a (rq.symm.trans ea.symm)
  · have e : a=b := Fin.ext (by simpa using congrArg Fin.val (ea.trans eb.symm))
    exact h (Subtype.ext (hdeg _ _ b (e ▸ ha) hb))

/-- If every right vertex has degree at most one, the graph has a disjoint
    star presentation. Isolated vertices on either side are allowed. -/
theorem isStarForest_of_unique_left (hdeg : ∀ p q l, I p l → I q l → p = q) :
    IsStarForest I := by
  classical
  let centers := (Finset.univ : Finset (Centers I)).toList
  use centers.map (group I)
  constructor
  · simp only [List.flatMap_map]
    apply List.nodup_flatMap.mpr
    exact ⟨fun p _ => group_nodup I p,
      (Finset.nodup_toList _).imp fun hpq => groups_disjoint I hdeg hpq⟩
  · constructor
    · intro t ht v hv
      obtain ⟨p,_,rfl⟩ := List.mem_map.mp ht
      obtain ⟨l,hl,rfl⟩ := (in_group I p v).mp hv
      exact ⟨p.val,l,hl,Or.inl ⟨rfl,rfl⟩⟩
    · intro p l hl
      let c : Centers I := ⟨p,l,hl⟩
      have hc : c ∈ centers := by simp [centers]
      exact ⟨group I c, List.mem_map.mpr ⟨c,hc,rfl⟩, Fin.natAdd N l,
        (in_group I c _).mpr ⟨l,hl,rfl⟩, Or.inl ⟨rfl,rfl⟩⟩

theorem normalize_of_unique_left (C : Circuit) (hdeg : ∀ p q l, I p l → I q l → p = q)
    (mono : Monotone2 C)
    (he : ∀ z : Fin (N+N) → Bool, circuitFun (N+N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    IncidenceNormalizes I C :=
  normalize_of_star_forest I C (isStarForest_of_unique_left I hdeg) mono he

end SingletonFiniteFormula.Formula
