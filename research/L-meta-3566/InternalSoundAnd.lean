import WrongSupportCircuit
import PEqualNP.Outside.L_meta_2668

namespace VertexPeel.WrongSupports
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.ReadTwo VertexPeel.ZeroFold
open PEqualNP.Outside.L615Aux.Wires (point)
open PEqualNP.Outside.L_meta_2668 (bypass bypass_length bypass_mem bypass_readsBack
  bypass_eval_rel bypass_eval_eq opMono_imp gateAt_bypass)

variable {n : ℕ}

abbrev SoundOff (G : SimpleGraph (Fin n)) (C : Circuit) (w : ℕ) (T : Finset (Fin n)) :=
  ∀ X, Disjoint X T → Active C w X → HasEdge G X

private lemma bypass_ao (C : Circuit) (hC : IsAO2 n C) (j w : ℕ)
    (hw : w<n+j) : IsAO2 n (bypass n C j w) := by
  refine ⟨?_,bypass_readsBack hw hC.2.1,?_⟩
  · intro g hg
    obtain ⟨h,mem,op,_⟩ := bypass_mem g hg
    rw [op]; exact hC.1 h mem
  · intro g hg
    obtain ⟨h,mem,_,len⟩ := bypass_mem g hg
    rw [len]; exact hC.2.2 h mem

private lemma compile_readers (C : Circuit) (hC : IsAO2 n C) (T : Finset (Fin n)) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = fv C T C.output ∧
      D.size + (forcedReaders C C.size T).card ≤ C.size := by
  classical
  obtain ⟨D,well,eq,size⟩ := compile C hC T
  refine ⟨D,well,eq,?_⟩
  let A := (Finset.range C.size).filter (Mg C T)
  let R := forcedReaders C C.size T
  have dis : Disjoint A R := by
    apply Finset.disjoint_left.mpr
    intro k ka kr
    obtain ⟨_,mg⟩ := Finset.mem_filter.mp ka
    obtain ⟨_,v,vt,read⟩ := Finset.mem_filter.mp kr
    rw [gateAt_eq _ _ mg.1] at read
    exact kill C hC T k mg.1 v.val read (fv_in0 C T v vt) mg
  have sub : A∪R ⊆ Finset.range C.size := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  calc
    D.size + R.card ≤ A.card + R.card := Nat.add_le_add_right size _
    _ = (A∪R).card := (Finset.card_union_of_disjoint dis).symm
    _ ≤ C.size := by simpa using Finset.card_le_card sub

/-- Each old reader of a raw coordinate survives the bypass, except for the
removed gate itself. Its new position is decremented precisely after j. -/
private lemma transport_readers (C : Circuit) (T : Finset (Fin n)) {j : ℕ}
    (hj : j<C.gates.length) (w : ℕ) :
    ((forcedReaders C C.size T).erase j).card ≤
      (forcedReaders (bypass n C j w) (bypass n C j w).size T).card := by
  classical
  let A := (forcedReaders C C.size T).erase j
  let pos (k : ℕ) := if k < j then k else k-1
  have avoid {k} (hk : k ∈ A) : k ≠ j := (Finset.mem_erase.mp hk).1
  have inj : Set.InjOn pos (↑A : Set ℕ) := by
    intro a ha b hb e
    have na := avoid ha
    have nb := avoid hb
    dsimp [pos] at e
    split_ifs at e <;> omega
  rw [← Finset.card_image_of_injOn inj]
  apply Finset.card_le_card
  intro k hk
  obtain ⟨h,mem,rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨hr,v,vt,read⟩ := Finset.mem_filter.mp (Finset.mem_erase.mp mem).2
  have room : h < C.gates.length := Finset.mem_range.mp hr
  have newlen : (bypass n C j w).size = C.gates.length-1 := bypass_length _ _ _ _
  have hne := avoid mem
  by_cases before : h < j
  · have bound : h < C.gates.length-1 := by omega
    simp only [pos,ite_eq_left before]
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (newlen ▸ bound),v,vt,?_⟩
    simpa [gateAt_bypass bound,before] using read
  · have bound : h-1 < C.gates.length-1 := by omega
    have beyond : ¬ h-1 < j := by omega
    have index : h-1+1=h := by omega
    simp only [pos,ite_eq_right before]
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (newlen ▸ bound),v,vt,?_⟩
    rw [gateAt_bypass bound,ite_eq_right beyond,index]
    apply List.mem_map.mpr
    exact ⟨v.val,read,PEqualNP.Outside.L_meta_2668.aliasWire_lt_self (by omega)⟩

/-- In an arbitrary circuit for G, bypass an internal AND by either operand
which is sound for G on the restricted domain. Fanout is unrestricted. -/
theorem bypass_sound_child (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsAO2 n C) (computes : circuitFun n C = graphFun G ∅)
    {j a b w : ℕ} (hj : j < C.gates.length) (inputs : C.gates[j].inputs = [a,b])
    (ha : a<n+j) (hb : b<n+j) (op : C.gates[j].op = .and)
    (operand : w = a ∨ w = b) (T : Finset (Fin n)) (sound : SoundOff G C w T) :
    ∃ D : Circuit, IsAO2 n D ∧ (∀ x, circuitFun n D x = graphFun G ∅ (zr T x)) ∧
      D.size + ((forcedReaders C C.size T).erase j).card + 1 ≤ C.size := by
  classical
  let B := bypass n C j w
  have hw : w<n+j := by rcases operand with rfl|rfl <;> assumption
  have hB : IsAO2 n B := bypass_ao C hC j w hw
  have len : B.size = C.size-1 := bypass_length _ _ _ _
  have ao : ∀ k < C.gates.length, (gateAt C k).op = .and ∨ (gateAt C k).op = .or := by
    intro k hk
    rw [gateAt_eq _ _ hk]; exact hC.1 _ (List.getElem_mem hk)
  obtain ⟨D,well,evaluated,size⟩ := compile_readers B hB T
  refine ⟨D,well,?_,?_⟩
  · intro x
    let y := zr T x
    let X := Finset.univ.filter (fun i => y i = true)
    have px : point X = y := by funext i; simp [point,X]
    have off : Disjoint X T := by
      apply Finset.disjoint_left.mpr
      intro v h ht
      have on := (Finset.mem_filter.mp h).2
      simp [y,zr,ht] at on
    have dom : wval C y (n+j) = true → wval C y w = true := by
      rw [wval_and C _ j a b hj inputs ha hb op,Bool.and_eq_true]
      rcases operand with rfl|rfl
      · exact And.left
      · exact And.right
    rw [evaluated]
    change B.eval (List.ofFn y) = graphFun G ∅ y
    by_cases pos : graphFun G ∅ y = true
    · rw [pos]
      have original : C.eval (List.ofFn y) = true := by change circuitFun n C y = true; rw [computes,pos]
      exact bypass_eval_rel (fun _ h => h) opMono_imp (show (List.ofFn y).length = n by simp) ao hj (.inl hw) dom original
    · have noChild : wval C y w = false := by
        apply Bool.eq_false_iff.mpr
        intro yes
        rw [← px] at yes
        exact pos (px ▸ (point_edge G X).mpr (sound X off yes))
      have noBoth : wval C y (n+j) = false :=
        Bool.eq_false_iff.mpr (fun yes => Bool.false_ne_true (noChild.symm.trans (dom yes)))
      have eq : wval C y (n+j) = wval C y w := noBoth.trans noChild.symm
      rw [bypass_eval_eq (show (List.ofFn y).length = n by simp) ao hj (.inl hw) eq]
      exact congrFun computes y
  · have cap := transport_readers C T hj w
    change ((forcedReaders C C.size T).erase j).card ≤ (forcedReaders B B.size T).card at cap
    change j < C.size at hj
    omega

/-- A nonconstant edge function always has a sound AND gate. Start at its
output, following an accepting OR operand until the first AND. -/
theorem exists_sound_and (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hc : IsAO2 n C) (computes : circuitFun n C = graphFun G ∅)
    (nonempty : ∃ u v, G.Adj u v) :
    ∃ j, ∃ hj : j < C.gates.length, C.gates[j].op = .and ∧ SoundOff G C (n+j) ∅ := by
  obtain ⟨u,v,edge⟩ := nonempty
  let X : Finset (Fin n) := {u,v}
  have someEdge : HasEdge G X := ⟨u,by simp [X],v,by simp [X],edge⟩
  have descend (w : ℕ) (on : Active C w X) (sound : SoundOff G C w ∅) :
      ∃ j, ∃ hj : j < C.gates.length, C.gates[j].op = .and ∧ SoundOff G C (n+j) ∅ := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases raw : w<n
      · let i : Fin n := ⟨w,raw⟩
        have hit : Active C w {i} := by change wval C (point {i}) i = true; simp [wval_in,point]
        obtain ⟨a,ha,b,hb,ab⟩ := sound {i} (by simp) hit
        rw [Finset.mem_singleton.mp ha,Finset.mem_singleton.mp hb] at ab
        exact (G.loopless.irrefl _ ab).elim
      by_cases past : n+C.gates.length ≤ w
      · rw [Active,wval_past C _ w past] at on; contradiction
      let j := w-n
      have eq : w = n+j := by dsimp [j]; omega
      have hj : j < C.gates.length := by omega
      obtain ⟨a,b,inputs,ha,hb,op⟩ := two n C hc j hj
      rcases op with hand|hor
      · exact ⟨j,hj,hand,eq ▸ sound⟩
      · have ev (Y : Finset (Fin n)) : Active C w Y ↔ Active C a Y ∨ Active C b Y := by
          rw [eq]; simp [Active,wval_or C _ j a b hj inputs ha hb hor]
        rcases (ev X).mp on with left|right
        · exact ih a (by omega) left (fun Y clear act => sound Y clear ((ev Y).mpr (.inl act)))
        · exact ih b (by omega) right (fun Y clear act => sound Y clear ((ev Y).mpr (.inr act)))
  have eq (Y : Finset (Fin n)) : Active C C.output Y ↔ HasEdge G Y := by
    change circuitFun n C (point Y) = true ↔ _
    rw [computes,point_edge]
  exact descend _ ((eq X).mpr someEdge) (fun Y _ => (eq Y).mp)

private lemma sound_and_pair (G : SimpleGraph (Fin n)) (C : Circuit)
    {j a b : ℕ} (hj : j<C.gates.length) (inputs : C.gates[j].inputs = [a,b])
    (ha : a<n+j) (hb : b<n+j) (op : C.gates[j].op = .and)
    (sound : SoundOff G C (n+j) ∅) :
    ∀ X, Active C a X → Active C b X → HasEdge G X := by
  intro X left right
  apply sound X (by simp)
  rw [Active,wval_and C _ j a b hj inputs ha hb op,Bool.and_eq_true]
  exact ⟨left,right⟩

private lemma bounded_child_sound (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (sq : NoFourCycle G)
    (C : Circuit) (hc : IsAO2 n C)
    {j a b : ℕ} (hj : j<C.gates.length) (inputs : C.gates[j].inputs = [a,b])
    (ha : a<n+j) (hb : b<n+j) (op : C.gates[j].op = .and) (sound : SoundOff G C (n+j) ∅)
    (p q : ℕ) (wa : WitnessWidth (Active (n:=n) C a) p) (wb : WitnessWidth (Active (n:=n) C b) q) :
    (∃ T : Finset (Fin n), T.card ≤ q*p ∧ SoundOff G C a T) ∨
      (∃ T : Finset (Fin n), T.card ≤ ((q+1)*p).choose 2 ∧ SoundOff G C b T) := by
  have upgrade (k w) (width : WitnessWidth (Active (n:=n) C w) k) (T : Finset (Fin n))
      (limited : ∀ X, Disjoint X T → X.card ≤ k → Active C w X → HasEdge G X) :
      SoundOff G C w T := by
    intro X hx on
    obtain ⟨W,sub,card,onW⟩ := width X on
    obtain ⟨u,hu,v,hv,e⟩ := limited W (Finset.disjoint_left.mpr (fun {_} hi ht =>
      Finset.disjoint_left.mp hx (sub hi) ht)) card onW
    exact ⟨u,sub hu,v,sub hv,e⟩
  have dich := sound_child G sq _ _ (active_mono C hc a) (active_mono C hc b)
    (sound_and_pair G C hj inputs ha hb op sound) p q
  exact dich.imp (fun ⟨T,ht,c⟩ => ⟨T,ht,upgrade p a wa T c⟩)
    (fun ⟨T,ht,c⟩ => ⟨T,ht,upgrade q b wb T c⟩)

/-- An arbitrary circuit for a nonempty C4-free graph contains a sound AND j
that can be bypassed on a bounded vertex restriction.  Every other physical
gate reading a forced variable can be saved in addition to this gate. -/
theorem compress_arbitrary_circuit (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (sq : NoFourCycle G)
    (nonempty : ∃ u v, G.Adj u v) (C : Circuit) (hc : IsAO2 n C)
    (computes : circuitFun n C = graphFun G ∅) :
    ∃ j, ∃ hj : j<C.gates.length, ∃ (a b d e : ℕ) (T : Finset (Fin n)) (D : Circuit),
      C.gates[j].op = .and ∧ C.gates[j].inputs = [a,b] ∧
      AndDepth n C a d ∧ AndDepth n C b e ∧
      ((T.card ≤ 2^e * 2^d ∧ SoundOff G C a T) ∨
        (T.card ≤ ((2^e+1)*2^d).choose 2 ∧ SoundOff G C b T)) ∧
      IsAO2 n D ∧ (∀ x, circuitFun n D x = graphFun G ∅ (zr T x)) ∧
      D.size + ((forcedReaders C C.size T).erase j).card + 1 ≤ C.size := by
  obtain ⟨j,hj,op,sound⟩ := exists_sound_and G C hc computes nonempty
  obtain ⟨a,b,inputs,ha,hb,_⟩ := two n C hc j hj
  have room : n+j ≤ n+C.size := Nat.add_le_add_left hj.le n
  obtain ⟨d,da⟩ := exists_andDepth C hc a (ha.trans_le room)
  obtain ⟨e,db⟩ := exists_andDepth C hc b (hb.trans_le room)
  have cut := bounded_child_sound G sq C hc hj inputs ha hb op sound _ _
    (width_of_andDepth C hc da) (width_of_andDepth C hc db)
  rcases cut with ⟨T,size,good⟩|⟨T,size,good⟩
  · obtain ⟨D,well,correct,gain⟩ := bypass_sound_child G C hc computes hj inputs ha hb op (.inl rfl) T good
    exact ⟨j,hj,a,b,d,e,T,D,op,inputs,da,db,.inl ⟨size,good⟩,well,correct,gain⟩
  · obtain ⟨D,well,correct,gain⟩ := bypass_sound_child G C hc computes hj inputs ha hb op (.inr rfl) T good
    exact ⟨j,hj,a,b,d,e,T,D,op,inputs,da,db,.inr ⟨size,good⟩,well,correct,gain⟩

/-- The singleton neighborhood certificate can be applied to an internal
sound AND, and charges all physical readers elsewhere in the whole circuit. -/
theorem internal_singleton_cut (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hc : IsAO2 n C) (computes : circuitFun n C = graphFun G ∅)
    {j a b : ℕ} (hj : j<C.gates.length) (inputs : C.gates[j].inputs = [a,b])
    (ha : a<n+j) (hb : b<n+j) (op : C.gates[j].op = .and) (sound : SoundOff G C (n+j) ∅)
    (X : Finset (Fin n)) (indep : ¬ HasEdge G X) (left : Active C a X) (z : Fin n)
    (boundary : ∀ u ∈ X, ∀ v, G.Adj u v → v=z ∨ Active C a {v}) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun (G.deleteIncidenceSet z) ∅ ∧
      D.size + ((forcedReaders C C.size {z}).erase j).card + 1 ≤ C.size := by
  have both := sound_and_pair G C hj inputs ha hb op sound
  have other : SoundOff G C b {z} := by
    intro Y clear right
    by_contra err
    obtain ⟨u,hu,v,hv,uv⟩ := cross_of_sound_and G _ _ (active_mono C hc a) (active_mono C hc b)
      both left right indep err
    rcases boundary u hu v uv with same|active
    · exact Finset.disjoint_left.mp clear hv (Finset.mem_singleton.mpr same)
    · exact err (both Y (active_mono C hc a (Finset.singleton_subset_iff.mpr hv) active) right)
  obtain ⟨D,well,eval,size⟩ := bypass_sound_child G C hc computes hj inputs ha hb op (.inr rfl) {z} other
  refine ⟨D,well,?_,size⟩
  funext x
  rw [eval]; simp [graphFun,zr,SimpleGraph.deleteIncidenceSet_adj]; grind

#print axioms compress_arbitrary_circuit
#print axioms internal_singleton_cut
#print axioms bypass_sound_child
#print axioms exists_sound_and
end VertexPeel.WrongSupports
