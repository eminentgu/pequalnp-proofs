import WrongSupports
import ZeroFold

namespace VertexPeel.WrongSupports
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.ReadTwo VertexPeel.ZeroFold
open PEqualNP.Outside.L615Aux.Wires (point point_mono acts_mono)

variable {n : ℕ}
abbrev Active (C : Circuit) (w : ℕ) (X : Finset (Fin n)) := wval C (point X) w = true

lemma active_mono (C : Circuit) (hC : IsAO2 n C) (w : ℕ) :
    ∀ ⦃X Y : Finset (Fin n)⦄, X ⊆ Y → Active C w X → Active C w Y := by
  intro X Y sub
  have mono : Monotone2 C := fun g mem => ⟨by
    rcases hC.1 g mem with h|h <;> simp [h],(hC.2.2 g mem).le⟩
  exact acts_mono mono (point_mono sub) w

/-- An upper bound on the number of AND gates on any input-to-wire path.
OR gates combine the two input bounds by maximum and AND gates add one. -/
inductive AndDepth (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop
  | input (i : Fin n) : AndDepth n C i 0
  | orGate {j a b d e : ℕ} (hj : j < C.gates.length) (inputs : C.gates[j].inputs = [a,b])
      (ha : a < n+j) (hb : b < n+j) (op : C.gates[j].op = .or)
      (left : AndDepth n C a d) (right : AndDepth n C b e) : AndDepth n C (n+j) (max d e)
  | andGate {j a b d e : ℕ} (hj : j < C.gates.length) (inputs : C.gates[j].inputs = [a,b])
      (ha : a < n+j) (hb : b < n+j) (op : C.gates[j].op = .and)
      (left : AndDepth n C a d) (right : AndDepth n C b e) : AndDepth n C (n+j) (max d e+1)

theorem exists_andDepth (C : Circuit) (hC : IsAO2 n C) (w : ℕ) (hw : w < n+C.size) :
    ∃ d, AndDepth n C w d := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w < n
    · exact ⟨0,.input ⟨w,raw⟩⟩
    · let j := w-n
      have eq : w = n+j := by dsimp [j]; omega
      have hj : j < C.gates.length := by change w < n+C.gates.length at hw; omega
      obtain ⟨a,b,inputs,ha,hb,op⟩ := two n C hC j hj
      obtain ⟨d,left⟩ := ih a (by omega) (by omega)
      obtain ⟨e,right⟩ := ih b (by omega) (by omega)
      rw [eq]
      rcases op with hand|hor
      · exact ⟨_,.andGate hj inputs ha hb hand left right⟩
      · exact ⟨_,.orGate hj inputs ha hb hor left right⟩

/-- A true wire has a positive certificate of size at most 2 to its AND depth,
allowing unrestricted fanout and arbitrarily many OR gates on the paths. -/
theorem width_of_andDepth (C : Circuit) (hC : IsAO2 n C) {w d : ℕ} (depth : AndDepth n C w d) :
    WitnessWidth (Active (n:=n) C w) (2^d) := by
  induction depth with
  | input i =>
    intro X on
    rw [Active,wval_in] at on
    have mem : i ∈ X := by simpa [point] using on
    refine ⟨{i},Finset.singleton_subset_iff.mpr mem,by simp,?_⟩
    simp [Active,wval_in,point]
  | @orGate j a b d e hj inputs ha hb op _ _ ihl ihr =>
    have ev (X : Finset (Fin n)) : Active C (n+j) X ↔ Active C a X ∨ Active C b X := by
      simp [Active,wval_or C _ j a b hj inputs ha hb op]
    intro X on
    rcases (ev X).mp on with l|r
    · obtain ⟨W,sub,size,hW⟩ := ihl X l
      exact ⟨W,sub,size.trans (Nat.pow_le_pow_right (by decide) (le_max_left _ _)),(ev W).mpr (.inl hW)⟩
    · obtain ⟨W,sub,size,hW⟩ := ihr X r
      exact ⟨W,sub,size.trans (Nat.pow_le_pow_right (by decide) (le_max_right _ _)),(ev W).mpr (.inr hW)⟩
  | @andGate j a b d e hj inputs ha hb op _ _ ihl ihr =>
    have ev (X : Finset (Fin n)) : Active C (n+j) X ↔ Active C a X ∧ Active C b X := by
      simp [Active,wval_and C _ j a b hj inputs ha hb op]
    intro X on
    obtain ⟨l,r⟩ := (ev X).mp on
    obtain ⟨U,sU,cU,hU⟩ := ihl X l
    obtain ⟨V,sV,cV,hV⟩ := ihr X r
    refine ⟨U∪V,Finset.union_subset sU sV,?_,(ev _).mpr
      ⟨active_mono C hC a Finset.subset_union_left hU,active_mono C hC b Finset.subset_union_right hV⟩⟩
    have hd : 2^d ≤ 2^(max d e) := Nat.pow_le_pow_right (by decide) (le_max_left _ _)
    have he : 2^e ≤ 2^(max d e) := Nat.pow_le_pow_right (by decide) (le_max_right _ _)
    have hc := Finset.card_union_le U V
    rw [pow_succ]; omega

lemma point_edge (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (X : Finset (Fin n)) :
    graphFun G ∅ (point X) = true ↔ HasEdge G X := by
  simp [graphFun,point]
  unfold HasEdge
  constructor
  · rintro ⟨u,v,uv,hu,hv⟩
    exact ⟨u,hu,v,hv,uv⟩
  · rintro ⟨u,hu,v,hv,uv⟩
    exact ⟨u,v,uv,hu,hv⟩

private def takeCircuit (C : Circuit) (j w : ℕ) : Circuit := ⟨C.gates.take j,w⟩

private lemma prefix_ao (C : Circuit) (hC : IsAO2 n C) (j w : ℕ) : IsAO2 n (takeCircuit C j w) := by
  refine ⟨fun g hg => hC.1 g (List.mem_of_mem_take hg),?_,fun g hg => hC.2.2 g (List.mem_of_mem_take hg)⟩
  intro k hk i hi
  have full : k < C.gates.length := by simp [takeCircuit] at hk; omega
  have same : gateAt (takeCircuit C j w) k = gateAt C k := by
    rw [gateAt_eq _ _ hk,gateAt_eq _ _ full]; exact List.getElem_take
  exact hC.2.1 k full i (same ▸ hi)

private lemma eval_prefix (C : Circuit) (j w : ℕ) (hj : j ≤ C.gates.length) (hw : w < n+j)
    (x : Fin n → Bool) : circuitFun n (takeCircuit C j w) x = wval C x w := by
  change (PEqualNP.Outside.L615Aux.Wires.wiresFrom (C.gates.take j) (List.ofFn x)).getD w false =
    (PEqualNP.Outside.L615Aux.Wires.wiresFrom C.gates (List.ofFn x)).getD w false
  have dec := List.take_append_drop j C.gates
  conv_rhs => rw [← dec,PEqualNP.Outside.L615Aux.Wires.wiresFrom_append]
  symm
  apply PEqualNP.Outside.L615Aux.Wires.prefix_val
  simpa [PEqualNP.Outside.L615Aux.Wires.wiresFrom_length,List.length_take,Nat.min_eq_left hj] using hw

/-- The physical gate positions before j which read a zeroed input. -/
noncomputable def forcedReaders (C : Circuit) (j : ℕ) (T : Finset (Fin n)) := by
  classical exact (Finset.range j).filter (fun k => ∃ v ∈ T, v.val ∈ (gateAt C k).inputs)

private theorem compile_exact_child (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (T : Finset (Fin n)) (w : ℕ) (hw : w<n+j) (agrees : ExactOff G (Active C w) T) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + (forcedReaders C j T).card ≤ j ∧ (∀ x, circuitFun n D x = graphFun G ∅ (zr T x)) := by
  classical
  let P := takeCircuit C j w
  obtain ⟨D,well,deq,size⟩ := compile P (prefix_ao C hC j w) T
  refine ⟨D,well,?_,?_⟩
  · let A := (Finset.range P.size).filter (Mg P T)
    let B := forcedReaders C j T
    have len : P.size = j := by simp [P,takeCircuit,Circuit.size,Nat.min_eq_left hj.le]
    have dis : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      intro k ka kb
      obtain ⟨_,mg⟩ := Finset.mem_filter.mp ka
      obtain ⟨kr,v,vt,read⟩ := Finset.mem_filter.mp kb
      have kp : k < P.gates.length := mg.1
      have kc : k < C.gates.length := (Finset.mem_range.mp kr).trans hj
      have same : P.gates[k] = C.gates[k] := List.getElem_take
      rw [gateAt_eq _ _ kc,← same] at read
      exact kill P (prefix_ao C hC j w) T k kp v.val read (fv_in0 P T v vt) mg
    have sub : A ∪ B ⊆ Finset.range j := by
      apply Finset.union_subset
      · rw [← len]; exact Finset.filter_subset _ _
      · exact Finset.filter_subset _ _
    calc
      D.size + B.card ≤ A.card+B.card := Nat.add_le_add_right size _
      _ = (A∪B).card := (Finset.card_union_of_disjoint dis).symm
      _ ≤ j := by simpa using Finset.card_le_card sub
  · intro x
    let X := Finset.univ.filter (fun i => zr T x i = true)
    have eqX : point X = zr T x := by
      funext i
      simp [point,X]
    have clear : Disjoint X T := Finset.disjoint_left.mpr fun {v} hv ht => by
      have on := (Finset.mem_filter.mp hv).2
      simp [zr,ht] at on
    have sound := agrees X clear
    rw [deq]
    change circuitFun n (takeCircuit C j w) (zr T x) = _
    rw [eval_prefix C j w hj.le hw,← eqX]
    apply Bool.eq_iff_iff.mpr
    exact sound.trans (point_edge G X).symm

private lemma exact_at_and_root (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (computes : circuitFun n C = graphFun G ∅)
    {j a b : ℕ} (hj : j < C.gates.length) (out : C.output = n+j)
    (inputs : C.gates[j].inputs = [a,b]) (ha : a<n+j) (hb : b<n+j)
    (op : C.gates[j].op = .and) (X : Finset (Fin n)) : (Active C a X ∧ Active C b X) ↔ HasEdge G X := by
  rw [← point_edge,← computes]
  change _ ↔ wval C (point X) C.output = true
  rw [out,wval_and C _ j a b hj inputs ha hb op]; simp [Active]

/-- C computes G with an AND at its output j.  After forcing T false we produce an
actual smaller IsAO2 circuit for the restriction, with at most j gates, additionally saving every preceding physical gate reading a zeroed input. -/
theorem compress_output_and (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (sq : NoFourCycle G)
    (C : Circuit) (hC : IsAO2 n C) (computes : circuitFun n C = graphFun G ∅)
    {j a b : ℕ} (hj : j < C.gates.length) (out : C.output = n+j)
    (inputs : C.gates[j].inputs = [a,b]) (ha : a<n+j) (hb : b<n+j) (op : C.gates[j].op = .and)
    {d e : ℕ} (left : AndDepth n C a d) (right : AndDepth n C b e) :
    ∃ (T : Finset (Fin n)) (D : Circuit),
      (T.card ≤ (2^e)*(2^d) ∨ T.card ≤ ((2^e+1)*(2^d)).choose 2) ∧
      IsAO2 n D ∧ D.size + (forcedReaders C j T).card ≤ j ∧ (∀ x, circuitFun n D x = graphFun G ∅ (zr T x)) := by
  classical
  have result := exact_child_after_deletion G sq _ _ (active_mono C hC a) (active_mono C hC b)
    (exact_at_and_root G C computes hj out inputs ha hb op) _ _ (width_of_andDepth C hC left) (width_of_andDepth C hC right)
  rcases result with ⟨T,ht,hT⟩|⟨T,ht,hT⟩
  · obtain ⟨D,ok⟩ := compile_exact_child G C hC hj T a ha hT
    exact ⟨T,D,.inl ht,ok⟩
  · obtain ⟨D,ok⟩ := compile_exact_child G C hC hj T b hb hT
    exact ⟨T,D,.inr ht,ok⟩

/-- If a child accepts an independent X, every error of the other child
meets the neighborhood of X outside the singleton sets accepted by the first. -/
theorem exact_off_boundary (G : SimpleGraph (Fin n)) (f g : Finset (Fin n) → Prop)
    (mf : ∀ ⦃X Y⦄, X ⊆ Y → f X → f Y) (mg : ∀ ⦃X Y⦄, X ⊆ Y → g X → g Y)
    (both : ∀ X, (f X ∧ g X) ↔ HasEdge G X)
    (X T : Finset (Fin n)) (indep : ¬ HasEdge G X) (accept : f X)
    (boundary : ∀ a ∈ X, ∀ b, G.Adj a b → b ∈ T ∨ f {b}) : ExactOff G g T := by
  intro Y dis
  refine ⟨?_,fun e => ((both Y).mpr e).2⟩
  intro gy
  by_contra err
  obtain ⟨a,ax,b,by',adj⟩ := cross_of_sound_and G f g mf mg
    (fun W h k => (both W).mp ⟨h,k⟩) accept gy indep err
  rcases boundary a ax b adj with bt|fb
  · exact Finset.disjoint_left.mp dis by' bt
  · exact err ((both Y).mp ⟨mf (Finset.singleton_subset_iff.mpr by') fb,gy⟩)

/-- A singleton boundary removes the output AND and all its earlier readers of z
with no restriction on the child's AND depth or on the graph. -/
theorem singleton_boundary_saving (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsAO2 n C) (computes : circuitFun n C = graphFun G ∅)
    {j l r : ℕ} (hj : j < C.gates.length) (out : C.output = n+j)
    (inputs : C.gates[j].inputs = [l,r]) (hl : l<n+j) (hr : r<n+j) (op : C.gates[j].op = .and)
    (X : Finset (Fin n)) (indep : ¬ HasEdge G X) (accept : Active C l X) (z : Fin n)
    (boundary : ∀ a ∈ X, ∀ b, G.Adj a b → b = z ∨ Active C l {b}) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun (G.deleteIncidenceSet z) ∅ ∧
      D.size + (forcedReaders C j {z}).card + 1 ≤ C.size := by
  have cut := exact_off_boundary G _ _ (active_mono C hC l) (active_mono C hC r)
    (exact_at_and_root G C computes hj out inputs hl hr op) X {z} indep accept
    (fun a h b e => (boundary a h b e).imp (fun eq => Finset.mem_singleton.mpr eq) id)
  obtain ⟨D,legal,bound,eval⟩ := compile_exact_child G C hC hj {z} r hr cut
  refine ⟨D, legal,?_, by change j < C.size at hj; omega⟩
  funext x
  rw [eval]
  simp [graphFun,zr,SimpleGraph.deleteIncidenceSet_adj]
  grind

open PEqualNP.MetaComplexity.CoverPromise in
/-- A sufficient condition on a *single* least circuit that gives the posted
single-vertex deletion conclusion for every circuit, including the cover bonus. -/
theorem peel_of_singleton_boundary (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (least : IsLeastAO G C)
    {j l r : ℕ} (hj : j < C.gates.length) (out : C.output = n+j)
    (inputs : C.gates[j].inputs = [l,r]) (hl : l<n+j) (hr : r<n+j) (op : C.gates[j].op = .and)
    (X : Finset (Fin n)) (indep : ¬ HasEdge G X) (accept : Active C l X)
    (z : Fin n) (positive : 0 < G.degree z)
    (boundary : ∀ a ∈ X, ∀ b, G.Adj a b → b = z ∨ Active C l {b})
    (enough : G.degree z ≤ (forcedReaders C j {z}).card + 1)
    (bonus : (∃ S : Finset (Fin n), IsVertexCover (G.deleteIncidenceSet z) S ∧
      ∀ T : Finset (Fin n), IsVertexCover G T → S.card < T.card) →
      G.degree z ≤ (forcedReaders C j {z}).card) :
    ∃ v : Fin n, 0 < G.degree v ∧
      ∀ E : Circuit, IsAO2 n E → circuitFun n E = graphFun G ∅ →
        ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun (G.deleteIncidenceSet v) ∅ ∧
          D.size + G.degree v ≤ E.size ∧
          ((∃ S : Finset (Fin n), IsVertexCover (G.deleteIncidenceSet v) S ∧
              ∀ T : Finset (Fin n), IsVertexCover G T → S.card < T.card) →
            D.size + G.degree v + 1 ≤ E.size) := by
  obtain ⟨D,legal,eval,saved⟩ := singleton_boundary_saving G C least.1 least.2.1
    hj out inputs hl hr op X indep accept z boundary
  refine ⟨z,positive,?_⟩
  intro E well computes
  have minimal := least.2.2 E well computes
  exact ⟨D,legal,eval,by omega,fun h => by have := bonus h; omega⟩

#print axioms singleton_boundary_saving
#print axioms peel_of_singleton_boundary
#print axioms width_of_andDepth
#print axioms compress_output_and
end VertexPeel.WrongSupports
