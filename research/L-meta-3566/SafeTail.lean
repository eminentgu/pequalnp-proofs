import InternalSoundAnd
import PEqualNP.Outside.L_meta_1491

namespace VertexPeel.SafeTail
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.ReadTwo
open PEqualNP.Outside.L_meta_2668 (bypass bypass_length bypass_output aliasWire
  bypass_mem bypass_readsBack bypass_eval_eq bypass_val_lt bypass_rel opMono_reverse)
open PEqualNP.Outside.L_meta_1491.S98 (appOr appOr_W_lt appOr_eval appOr_AO AO_of_IsAO2 IsAO2_of_AO)
open VertexPeel.ZeroFold (two gateAt_eq wval_or wval_past)

variable {n : ℕ}

/-- A sound wire accepts only positive graph inputs. -/
def SoundAt (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w : ℕ) : Prop :=
  ∀ x, wval C x w = true → graphFun G ∅ x = true

/-- Every consumer of a sound wire is itself a sound OR gate. -/
def CleanReaders (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : Prop :=
  ∀ j < C.gates.length, ∀ w ∈ (gateAt C j).inputs,
    SoundAt G C w → (gateAt C j).op = .or ∧ SoundAt G C (n+j)

open Classical in
noncomputable def unsafeGates (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :=
  (Finset.range C.size).filter (fun j => ¬ SoundAt G C (n+j))

private lemma empty_legal (n : ℕ) : IsAO2 n ⟨[],n⟩ := by
  refine ⟨fun g mem => (List.not_mem_nil mem).elim,fun j h => (Nat.not_lt_zero j h).elim,
    fun g mem => (List.not_mem_nil mem).elim⟩

private lemma valid_output (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (least : IsLeastAO G C) {j : ℕ} (hj : j < C.gates.length) : C.output < n+C.size := by
  by_contra! invalid
  let E : Circuit := ⟨[],n⟩
  have ev : circuitFun n E = graphFun G ∅ := by
    rw [← least.2.1]
    funext x
    exact (wval_past E x n (by simp [E])).trans (wval_past C x C.output invalid).symm
  have bound := least.2.2 E (empty_legal n) ev
  change C.gates.length ≤ 0 at bound
  omega

private lemma bypassLegal (C : Circuit) (hC : IsAO2 n C) {j w : ℕ}
    (hw : w<n+j) : IsAO2 n (bypass n C j w) := by
  refine ⟨?_,bypass_readsBack hw hC.2.1,?_⟩
  · intro g hg
    obtain ⟨h,mem,op,_⟩ := bypass_mem g hg
    rw [op]; exact hC.1 h mem
  · intro g hg
    obtain ⟨h,mem,_,len⟩ := bypass_mem g hg
    rw [len]; exact hC.2.2 h mem

/-- When an unsafe OR has a sound operand b, reconnect its consumers to a
and attach b at the output. The new least circuit has fewer unsafe gates. -/
theorem exchange_or (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (least : IsLeastAO G C) {j a b : ℕ} (hj : j<C.gates.length) (ha : a<n+j) (hb : b<n+j)
    (ev : ∀ x : Fin n → Bool, wval C x (n+j) = (wval C x a || wval C x b))
    (safe : SoundAt G C b) (bad : ¬SoundAt G C (n+j)) :
    ∃ D : Circuit, IsLeastAO G D ∧ D.size = C.size ∧ (unsafeGates G D).card < (unsafeGates G C).card := by
  classical
  let B := bypass n C j a
  let D := appOr n B B.output b
  have hc := least.1
  have lenB : B.gates.length = C.gates.length-1 := bypass_length _ _ _ _
  have orig := valid_output G C least hj
  change C.output < n+C.gates.length at orig
  have bB : b<n+B.gates.length := by omega
  have oB : B.output < n+B.gates.length := by
    change aliasWire (n+j) a C.output < _
    unfold aliasWire
    split_ifs <;> omega
  have ao : ∀ k < C.gates.length, (gateAt C k).op = .and ∨ (gateAt C k).op = .or := by
    intro k hk
    rw [gateAt_eq _ _ hk]; exact hc.1 _ (List.getElem_mem hk)
  have dlegal : IsAO2 n D := IsAO2_of_AO n D (appOr_AO n B _ _ (AO_of_IsAO2 n B (bypassLegal C hc ha)) oB bB)
  have count : D.size = C.size := by simp [D,appOr,Circuit.size,lenB]; omega
  have dout : D.output = n+B.gates.length := rfl
  have correct : circuitFun n D = graphFun G ∅ := by
    funext x
    have sameB : wval B x b = wval C x b := bypass_val_lt (by simp) hj b hb
    have extend : circuitFun n D x = (circuitFun n B x || wval B x b) :=
      appOr_eval n B B.output b x oB bB
    rw [extend,sameB]
    cases bx : wval C x b with
    | true => simpa [bx] using (safe x bx).symm
    | false =>
      simp only [Bool.or_false]
      have merge : wval C x (n+j) = wval C x a := by rw [ev,bx,Bool.or_false]
      exact (bypass_eval_eq (show (List.ofFn x).length = n by simp) ao hj (.inl ha) merge).trans
        (congrFun least.2.1 x)
  have dleast : IsLeastAO G D := ⟨dlegal,correct,fun E legal ok => count.symm ▸ least.2.2 E legal ok⟩
  let idx (i : ℕ) := if i<j then i else i+1
  have avoids (i : ℕ) : idx i ≠ j := by dsimp [idx]; split_ifs <;> omega
  have inj : Function.Injective idx := by
    intro i k eq; dsimp [idx] at eq; split_ifs at eq <;> omega
  have sub : (unsafeGates G D).image idx ⊆ (unsafeGates G C).erase j := by
    intro i him
    obtain ⟨k,badK,rfl⟩ := Finset.mem_image.mp him
    obtain ⟨kr,unsafeK⟩ := Finset.mem_filter.mp badK
    have last : k ≠ B.gates.length := by
      rintro rfl
      exact unsafeK (fun x yes => (congrFun correct x) ▸ (show circuitFun n D x = true from yes))
    have kD := Finset.mem_range.mp kr
    have sizeD : D.size = B.gates.length+1 := by simp [D,appOr,Circuit.size]
    have kB : k < B.gates.length := by omega
    have old : idx k < C.gates.length := by dsimp [idx]; split_ifs <;> omega
    refine Finset.mem_erase.mpr ⟨avoids _,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr old,?_⟩⟩
    intro sound
    apply unsafeK
    intro x on
    have pre : wval D x (n+k) = wval B x (n+k) :=
      appOr_W_lt n B B.output b x _ (by omega)
    have route : aliasWire (n+j) a (n+idx k) = n+k := by
      dsimp [aliasWire,idx]; split_ifs <;> omega
    have weaken : wval C x a = true → wval C x (n+j) = true := by
      intro yes; rw [ev,yes]; rfl
    have relation := bypass_rel (fun _ h => h) opMono_reverse
      (show (List.ofFn x).length=n by simp) ao hj (.inl ha) (fun _ => weaken)
      (n+idx k) (by have := avoids k; omega)
    change wval B x (aliasWire (n+j) a (n+idx k)) = true → wval C x (n+idx k) = true at relation
    rw [route] at relation
    exact sound x (relation (pre ▸ on))
  have cardinal := Finset.card_le_card sub
  have inBad : j ∈ unsafeGates G C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,bad⟩
  rw [Finset.card_image_of_injective _ inj,Finset.card_erase_of_mem inBad] at cardinal
  have positive : 0 < (unsafeGates G C).card := Finset.card_pos.mpr
    ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,bad⟩⟩
  exact ⟨D,dleast,count,by omega⟩

private lemma no_and (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (least : IsLeastAO G C) {j a b w : ℕ} (hj : j<C.gates.length) (inputs : C.gates[j].inputs = [a,b])
    (ha : a<n+j) (hb : b<n+j) (op : C.gates[j].op=.and) (operand : w=a ∨ w=b) (sound : SoundAt G C w) : False := by
  have good : WrongSupports.SoundOff G C w ∅ := fun X _ on =>
    (WrongSupports.point_edge G X).mp (sound _ on)
  obtain ⟨D,leg,ev,save⟩ := WrongSupports.bypass_sound_child G C least.1 least.2.1 hj inputs ha hb op operand ∅ good
  have dc : circuitFun n D = graphFun G ∅ := by
    funext x
    have identity : ZeroFold.zr ∅ x = x := by funext v; simp [ZeroFold.zr]
    simpa only [identity] using ev x
  have le := least.2.2 D leg dc
  omega

/-- Among least circuits choose one minimizing the number of gates that accept
an independent input. Its sound wires feed only sound OR gates. -/
theorem exists_clean_readers (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (least : IsLeastAO G C) : ∃ D, IsLeastAO G D ∧ CleanReaders G D ∧ D.size = C.size := by
  classical
  let Can (k : ℕ) : Prop := ∃ D, IsLeastAO G D ∧ (unsafeGates G D).card=k
  have possible : ∃ k, Can k := ⟨_,C,least,rfl⟩
  obtain ⟨D,minimum,dc⟩ := Nat.find_spec possible
  have opt (E : Circuit) (e : IsLeastAO G E) : (unsafeGates G D).card ≤ (unsafeGates G E).card := by
    rw [dc]; exact Nat.find_min' possible (show Can (unsafeGates G E).card from ⟨E,e,rfl⟩)
  refine ⟨D,minimum,?_,Nat.le_antisymm (minimum.2.2 C least.1 least.2.1) (least.2.2 D minimum.1 minimum.2.1)⟩
  intro j hj w operand good
  obtain ⟨a,b,inputs,ha,hb,op⟩ := two n D minimum.1 j hj
  have port : w=a ∨ w=b := by simpa [gateAt_eq D j hj,inputs] using operand
  rcases op with hand|hor
  · exact (no_and G D minimum hj inputs ha hb hand port good).elim
  · refine ⟨by rwa [gateAt_eq D j hj],?_⟩
    by_contra bad
    have orig (x : Fin n → Bool) := wval_or D x j a b hj inputs ha hb hor
    have swap (p q) (hp : p<n+j) (hq : q<n+j) (safe : SoundAt G D q)
        (on : ∀ x : Fin n → Bool, wval D x (n+j)=(wval D x p || wval D x q)) : False := by
      obtain ⟨E,emin,_,better⟩ := exchange_or G D minimum hj hp hq on safe bad
      exact (not_lt_of_ge (opt E emin)) better
    rcases port with rfl|rfl
    · exact swap b w hb ha good (fun x => (orig x).trans (Bool.or_comm _ _))
    · exact swap a w ha hb good orig

/-- Every strict descendant gate of a sound gate is a sound OR. -/
theorem sound_above (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (clean : CleanReaders G C) (i : ℕ) (safe : SoundAt G C (n+i))
    (k : ℕ) (hk : k<C.gates.length) (cone : PEqualNP.EdgeOwnership.InCone n C i k) :
    (gateAt C k).op=.or ∧ SoundAt G C (n+k) := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    obtain ⟨w,read,lo,hi,branch⟩ := (PEqualNP.Outside.L_meta_1491.S98.inCone_iff n C i k hk).mp cone
    apply clean k hk w read
    rcases branch with eq|inside
    · have ix : n+i=w := by omega
      exact ix ▸ safe
    · have earlier : w-n<k := by omega
      have sw := (ih (w-n) earlier (earlier.trans hk) inside).2
      have ix : n+(w-n)=w := by omega
      exact ix ▸ sw

theorem clean_topForm (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (clean : CleanReaders G C) : TopForm G C := by
  intro i _ k hk _ safe hand inside
  have clash := (sound_above G C clean i safe k hk inside).1
  rw [hand] at clash
  contradiction

/-- The project's TopForm predicate holds for a circuit of the same least size,
with no assumptions about edges, bipartitions, cycles or fanout. -/
theorem exists_least_topForm (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (least : IsLeastAO G C) : ∃ D, IsLeastAO G D ∧ TopForm G D ∧ D.size=C.size := by
  obtain ⟨D,opt,clean,eq⟩ := exists_clean_readers G C least
  exact ⟨D,opt,clean_topForm G D clean,eq⟩

#print axioms exists_least_topForm
#print axioms exchange_or
#print axioms exists_clean_readers
end VertexPeel.SafeTail
