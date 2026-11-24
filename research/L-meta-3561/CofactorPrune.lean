import EncodedBank
import PEqualNP.Outside.L_meta_2913

namespace PEqualNP.Research3561.RawPredecessor
open PEqualNP.Research3561

/-- Put back both prepaid OR operations in the sampled live program, releasing raw4
as soon as its second use has finished. This works at the level of the actual sample bank. -/
theorem prependOrs {k t : Nat} (h : Live k t signals.toFinset) :
    Live (k+2) t raw.toFinset := by
  let a := bin true raw0 raw4
  let b := bin true raw4 raw1
  let u : Finset Sig := [raw0,raw1,raw2,raw3,raw5,raw6,raw7,raw8,a].toFinset
  have f0 : proper raw0 := ⟨raw_valid _ (by simp [raw]), by decide, by decide⟩
  have f1 : proper raw1 := ⟨raw_valid _ (by simp [raw]), by decide, by decide⟩
  have f4 : proper raw4 := ⟨raw_valid _ (by simp [raw]), by decide, by decide⟩
  have e0 : signals.toFinset = insert b u := by decide +kernel
  rw [e0] at h
  have h' := @Live.binary k t u raw4 raw1 true f4 f1 (by decide)
    (by decide +kernel) h
  have e1 : insert raw4 (insert raw1 u) = insert a raw.toFinset := by decide +kernel
  rw [e1] at h'
  have h'' := @Live.binary (k+1) t raw.toFinset raw0 raw4 true f0 f4 (by decide)
    (by decide +kernel) h'
  have e2 : insert raw0 (insert raw4 raw.toFinset) = raw.toFinset := by decide +kernel
  rwa [e2] at h''

/-- Transport the live derivation to the publicly checked predecessor's identical
414 paired-row bank. Only its inductive predicate has a distinct declaration name. -/
theorem transfer {k t : Nat} {s : Finset Sig} (h : Live k t s) :
    PEqualNP.Outside.L_meta_2913.Main1672.Live k t s := by
  induction h with
  | stop => exact .stop
  | unary ha hf _ ih => exact .unary ha hf ih
  | binary ha hb hne hf _ ih => exact .binary ha hb hne hf ih

theorem sampled_budget (k t : Nat) (hk : k ≤ 12) : ¬ Live k t signals.toFinset := by
  intro h
  have u := transfer (prependOrs h)
  have sz := (PEqualNP.Outside.L_meta_2913.Main1672.live_size u).2
  have card : raw.toFinset.card = 9 := by decide +kernel
  rw [card] at sz
  have h14 : k+2 ≤ 14 := by omega
  have ht6 : t ≤ 6 := by omega
  exact PEqualNP.Outside.L_meta_2913.Main1672.rootImpossible t ht6 (k+2) h14 _ _
    PEqualNP.Outside.L_meta_2913.Main1672.rootWires_rep
    (PEqualNP.Outside.L_meta_2913.Main1672.restrict_live u
      (PEqualNP.Outside.L_meta_2913.Main1672.rootTag_ok h14))

theorem circuit_budget (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (correct : ∀ x : Fin 9 → Bool, C.eval (encoded x) = edgeF x) : 13 ≤ C.size := by
  obtain ⟨k,t,hk,hl,_⟩ := extractedBank C legal correct
  by_contra! h
  exact sampled_budget k t (by omega) hl

end PEqualNP.Research3561.RawPredecessor

namespace PEqualNP.Outside.L_meta_2913.Main1672.Prune3561

-- Transport a set of live projected inputs across a larger bank, ignoring constants.
lemma properTransfer {H : SigHom} {q : Nat} {S T : Finset Sig} (h : Feasible H q S)
    (hs : ∀ a ∈ S, H.fn a ∈ T.image H.fn ∨ ¬ proper (H.fn a)) : Feasible H q T := by
  obtain ⟨m, hm, t, U, hl, hu⟩ := h
  refine ⟨m, hm, t, U, hl, ?_⟩
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (hu ha)
  exact (hs b hb).resolve_right (fun hn => hn (live_proper hl _ ha))

def vtx (i : Fin 9) : Sig := raw.getD i.val zero
def leftOr : Sig := bin true raw0 raw4
def rightOr : Sig := bin true raw4 raw1
def more1 : Finset Sig := insert leftOr raw.toFinset
def more2 : Finset Sig := insert rightOr more1

theorem payLeft {H : SigHom} {q} (h : Feasible H q more1) : Feasible H (q+1) raw.toFinset := by
  have h' := @pull_binary H q raw0 raw4 true raw.toFinset h
  have h0 : raw0 ∈ raw.toFinset := by simp [raw]
  have h4 : raw4 ∈ raw.toFinset := by simp [raw]
  simpa only [Finset.insert_eq_of_mem h4,Finset.insert_eq_of_mem h0] using h'

theorem payRight {H : SigHom} {q} (h : Feasible H q more2) : Feasible H (q+1) more1 := by
  have h' := @pull_binary H q raw4 raw1 true more1 h
  have h1 : raw1 ∈ more1 := by simp [more1,raw]
  have h4 : raw4 ∈ more1 := by simp [more1,raw]
  simpa only [Finset.insert_eq_of_mem h1,Finset.insert_eq_of_mem h4] using h'

theorem freeLeft {q} (h : Feasible (homProject 0) q more1) : Feasible (homProject 0) q raw.toFinset := by
  have hn : ¬proper ((homProject 0).fn raw0) := fun hp => hp.2.1 (project_raw_zero 0)
  have h' := @free_binary_left (homProject 0) q raw0 raw4 true raw.toFinset hn h
  have h0 : raw0 ∈ raw.toFinset := by simp [raw]
  have h4 : raw4 ∈ raw.toFinset := by simp [raw]
  simpa only [Finset.insert_eq_of_mem h4,Finset.insert_eq_of_mem h0] using h'

theorem freeRight {q} (h : Feasible (homProject 1) q more2) : Feasible (homProject 1) q more1 := by
  have hn : ¬proper ((homProject 1).fn raw1) := fun hp => hp.2.1 (project_raw_zero 1)
  have h' := @free_binary_right (homProject 1) q raw4 raw1 true more1 hn h
  have h1 : raw1 ∈ more1 := by simp [more1,raw]
  have h4 : raw4 ∈ more1 := by simp [more1,raw]
  simpa only [Finset.insert_eq_of_mem h1,Finset.insert_eq_of_mem h4] using h'

/-- On 0 and 1 one prepaid OR collapses. On 6 and 7 both prepaid ORs
can be charged against the stronger degree-two restriction lower bound. -/
theorem forbidden (i : Fin 9) (hi : i=0 ∨ i=1 ∨ i=6 ∨ i=7)
    {q} (hq : q ≤ 10) (h : Feasible (homProject i) q more2) : False := by
  rcases hi with rfl|rfl|rfl|rfl
  · exact root_project_deg3 0 (by decide) (feasible_mono (freeLeft (payRight h)) (by omega))
  · exact root_project_deg3 1 (by decide) (feasible_mono (payLeft (freeRight h)) (by omega))
  · exact root_project_deg2 6 (by decide) (feasible_mono (payLeft (payRight h)) (by omega))
  · exact root_project_deg2 7 (by decide) (feasible_mono (payLeft (payRight h)) (by omega))

theorem signals_sub_more : PEqualNP.Research3561.signals.toFinset ⊆ more2 := by decide +kernel

theorem two_zero_tail (i : Fin 9) (hi : i=0 ∨ i=1 ∨ i=6 ∨ i=7)
    (b : Sig) {k t : Nat} {S : Finset Sig} (hk : k ≤ 12)
    (h : PEqualNP.Research3561.Live k t S)
    (hs : S ⊆ insert (bin false (vtx i) b) PEqualNP.Research3561.signals.toFinset)
    (hx : vtx i ∈ S) (hy : bin false (vtx i) b ∈ S) (hxy : vtx i ≠ bin false (vtx i) b) : False := by
  let H := homProject i
  have hz : H.fn (vtx i) = zero := project_raw_zero i
  have hg : H.fn (bin false (vtx i) b) = zero := by
    rw [H.hbin,hz,bin_comm]; exact (bin_laws (H.valid b)).2.2.1
  have hn : ¬ proper zero := fun p => p.2.1 rfl
  obtain ⟨q,hq,hf⟩ := feasible_two_consts (PEqualNP.Research3561.RawPredecessor.transfer h)
    H _ _ hx hy hxy (by rw [hz];exact hn) (by rw [hg];exact hn)
  apply forbidden i hi (by omega : q ≤ 10)
  apply properTransfer hf
  intro a ha
  rcases Finset.mem_insert.mp (hs ha) with rfl|hb
  · exact Or.inr (hg ▸ hn)
  · exact Or.inl (Finset.mem_image_of_mem _ (signals_sub_more hb))

/-- All nine projected raw deletion lower bounds with the true number of prepaid OR gates. -/
def encodedFloor (i : Fin 9) : Nat :=
  if i=4 then 13 else if i=0 ∨ i=1 ∨ i=6 ∨ i=7 then 11 else 10

theorem projected_floor (i : Fin 9) {q : Nat} (hq : q < encodedFloor i)
    (h : Feasible (homProject i) q PEqualNP.Research3561.signals.toFinset) : False := by
  have all : Feasible (homProject i) q more2 := by
    apply properTransfer h
    intro x hx; exact Or.inl (Finset.mem_image_of_mem _ (signals_sub_more hx))
  by_cases h4 : i=4
  · subst i
    have ha : ¬proper ((homProject 4).fn raw4) := fun hp => hp.2.1 (project_raw_zero 4)
    have h1 : raw1 ∈ more1 := by simp [more1,raw]
    have h4 : raw4 ∈ more1 := by simp [more1,raw]
    have p := @free_binary_left (homProject 4) q raw4 raw1 true more1 ha all
    have p' : Feasible (homProject 4) q more1 := by
      simpa only [Finset.insert_eq_of_mem h1,Finset.insert_eq_of_mem h4] using p
    have p := @free_binary_right (homProject 4) q raw0 raw4 true raw.toFinset ha p'
    have u : raw0 ∈ raw.toFinset := by simp [raw]
    have v : raw4 ∈ raw.toFinset := by simp [raw]
    have z : Feasible (homProject 4) q raw.toFinset := by
      simpa only [Finset.insert_eq_of_mem u,Finset.insert_eq_of_mem v] using p
    apply root_project_deg2 4 (by decide) (feasible_mono z ?_)
    simp [encodedFloor] at hq; omega
  · by_cases special : i=0 ∨ i=1 ∨ i=6 ∨ i=7
    · apply forbidden i special _ all
      simp [encodedFloor,h4,special] at hq; omega
    · apply root_project_deg3 i (by omega) (feasible_mono (payLeft (payRight all)) ?_)
      simp [encodedFloor,h4,special] at hq; omega

/-- Four additional unary branches: if a NOT of one of the indicated raws is
formed and its positive operand is retained, the resulting two projected constants
force the same cofactor contradiction. -/
theorem first_neg_keep (i : Fin 9) (hi : i=0 ∨ i=1 ∨ i=6 ∨ i=7)
    {k t : Nat} {S : Finset Sig} (hk : k ≤ 12) (h : PEqualNP.Research3561.Live k t S)
    (hs : S ⊆ insert (neg (vtx i)) PEqualNP.Research3561.signals.toFinset)
    (ha : vtx i ∈ S) (hb : neg (vtx i) ∈ S) : False := by
  let H := homProject i
  have z := project_raw_zero i
  have hz : H.fn (vtx i) = zero := z
  have valid : Valid (vtx i) := by
    rcases hi with rfl|rfl|rfl|rfl <;> apply raw_valid <;> simp [vtx,raw]
  have h1 : H.fn (neg (vtx i)) = one := by rw [H.hneg valid,hz,neg_laws.1]
  have distinct : vtx i ≠ neg (vtx i) := by
    intro eq
    have hh := congrArg H.fn eq
    rw [hz,h1] at hh; exact (by decide : zero ≠ one) hh
  have not0 : ¬proper (H.fn (vtx i)) := fun hp => hp.2.1 hz
  have not1 : ¬proper (H.fn (neg (vtx i))) := fun hp => hp.2.2 h1
  obtain ⟨q,hq,hf⟩ := feasible_two_consts (PEqualNP.Research3561.RawPredecessor.transfer h)
    H _ _ ha hb distinct not0 not1
  apply forbidden i hi (by omega : q ≤ 10)
  apply properTransfer hf
  intro w hw; rcases Finset.mem_insert.mp (hs hw) with rfl|hm
  · exact Or.inr not1
  · exact Or.inl (Finset.mem_image_of_mem _ (signals_sub_more hm))

end PEqualNP.Outside.L_meta_2913.Main1672.Prune3561


namespace PEqualNP.Research3561.RawPredecessor

def witnessRows : List (List Nat) := [[414,27,27,27,27,27,27,27,414,414],[34,414,102,34,34,34,34,34,414,414],[414,414,414,414,414,414,414,414,414,414],[414,414,414,414,414,414,414,414,414,414],[414,414,414,414,414,414,414,414,414,414],[414,414,414,414,414,414,414,414,414,414],[5,196,5,5,5,414,5,5,5,196],[8,8,38,8,8,8,414,8,8,8],[414,414,414,414,414,414,414,414,414,414]]
def point (i : Fin 9) (j : Fin 10) : Nat := (witnessRows.getD i.val []).getD j.val 414
def operand (j : Fin 10) : Sig := signals.getD j.val zero
def valAt (i : Fin 9) : Sig := raw.getD i.val zero
def otherWires (i : Fin 9) (j : Fin 10) : List Sig :=
  signals.erase (valAt i) ++ [bin false (valAt i) (operand j)]

theorem table_ok : ∀ (i : Fin 9) (j : Fin 10), point i j < 414 →
    (i = 0 ∨ i = 1 ∨ i = 6 ∨ i = 7) ∧
    valAt i ≠ bin false (valAt i) (operand j) ∧
    (unionSep true (otherWires i j)).testBit (point i j) = false := by decide +kernel

/-- A finite list of early AND choices eliminated on exactly the 414 sampled row pairs,
including all 22 raw pairs incident to positions 0,1,6,7, plus four with a prepaid OR. -/
theorem first_and (i : Fin 9) (j : Fin 10) (hp : point i j < 414)
    {k t : Nat} {S : Finset Sig} (hk : k ≤ 12) (h : Live k t S)
    (hs : S ⊆ insert (bin false (valAt i) (operand j)) signals.toFinset)
    (hg : bin false (valAt i) (operand j) ∈ S) : False := by
  obtain ⟨hi,hne,ht⟩ := table_ok i j hp
  apply PEqualNP.Outside.L_meta_2913.Main1672.Prune3561.two_zero_tail i hi (operand j) hk h hs _ hg hne
  change valAt i ∈ S
  by_contra hmiss
  obtain ⟨a,ha,hsep⟩ := live_sep h (point i j) hp
  have ne : a ≠ valAt i := fun e => hmiss (e ▸ ha)
  have hm : a ∈ otherWires i j := by
    rcases Finset.mem_insert.mp (hs ha) with rfl|hold
    · simp [otherWires]
    · exact List.mem_append_left _ ((List.mem_erase_of_ne ne).mpr (List.mem_toFinset.mp hold))
  have tt := (mem_unionSep true (otherWires i j) (point i j)).2
    ⟨a,hm,sep_weaken _ (live_proper h a ha).1 _ hp hsep⟩
  exact Bool.noConfusion (tt.symm.trans ht)

end PEqualNP.Research3561.RawPredecessor
