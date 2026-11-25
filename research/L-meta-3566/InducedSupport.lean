import SupportPacking

namespace VertexPeel.BatchExchange

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.MetaComplexity.CoverPromise PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2668 (val val_ge val_input val_gate gateAt_eq)
open VertexPeel.CoverCircuit (getD_ofFn)

private def masked {n} (W : Finset (Fin n)) (x : Fin n → Bool) (i : Fin n) :=
  if i ∈ W then x i else false

private def rename {n} (W : Finset (Fin n)) (s i : Nat) :=
  if h : i<n then if (⟨i,h⟩ : Fin n) ∈ W then i else n+s else i

private def relabel {n} (W : Finset (Fin n)) (s : Nat) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (rename W s)⟩

private def restrictInputs {n} (W : Finset (Fin n)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relabel W C.size),rename W C.size C.output⟩

private theorem restrict_spec {n} (W : Finset (Fin n)) (C : Circuit) (mono : Monotone2 C) :
    Monotone2 (restrictInputs W C) ∧ (restrictInputs W C).size=C.size ∧
    ∀ x, circuitFun n (restrictInputs W C) x = circuitFun n C (masked W x) := by
  let D := restrictInputs W C
  have len : D.gates.length = C.gates.length := by simp [D,restrictInputs]
  refine ⟨?_,len,?_⟩
  · intro g hg
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
    simpa [relabel] using mono q hq
  · intro x
    have wires (i : Nat) :
        val D (List.ofFn x) (rename W C.size i) = val C (List.ofFn (masked W x)) i := by
      induction i using Nat.strong_induction_on with
      | _ i ih =>
        by_cases input : i<n
        · by_cases keep : (⟨i,input⟩ : Fin n) ∈ W
          · rw [show rename W C.size i = i by simp [rename,input,keep],
                val_input (n:=n) (by simp) input,val_input (n:=n) (by simp) input]
            simp [masked,keep,input]
          · rw [show rename W C.size i = n+C.size by simp [rename,input,keep],
              val_ge (n:=n) (by simp) (by rw [len]; rfl),val_input (n:=n) (by simp) input]
            simp [masked,keep,input]
        · rw [show rename W C.size i = i by simp [rename,input]]
          by_cases past : n+C.gates.length ≤ i
          · rw [val_ge (n:=n) (by simp) (len.symm ▸ past),val_ge (n:=n) (by simp) past]
          · obtain ⟨j,rfl⟩ : ∃ j, i = n+j := ⟨i-n,by omega⟩
            have hj : j<C.gates.length := by omega
            have hjD : j<D.gates.length := len.symm ▸ hj
            rw [val_gate (n:=n) (by simp) hjD,val_gate (n:=n) (by simp) hj]
            have gate : gateAt D j = relabel W C.size (gateAt C j) := by
              rw [gateAt_eq hjD,gateAt_eq hj]
              exact List.getElem_map ..
            rw [gate]
            simp only [relabel,List.map_map]
            congr 1
            apply List.map_congr_left
            intro k _
            simp only [Function.comp_apply]
            by_cases before : k<n+j
            · rw [ite_eq_left before]
              by_cases killed : n+C.size ≤ rename W C.size k
              · rw [ite_eq_right (by change n+C.gates.length ≤ _ at killed; omega),← ih k before,
                  val_ge (n:=n) (by simp) (len.symm ▸ killed)]
              · have same : rename W C.size k = k := by
                  by_cases h : k<n
                  · by_cases m : (⟨k,h⟩ : Fin n) ∈ W
                    · simp [rename,h,m]
                    · simp [rename,h,m] at killed
                  · simp [rename,h]
                rw [ite_eq_left (same.symm ▸ before)]
                exact ih k before
            · have same : rename W C.size k = k := by
                have h : ¬ k<n := by omega
                simp [rename,h]
              rw [ite_eq_right before,same,ite_eq_right before]
    exact wires C.output


/-- Induction on a subset of vertices, leaving the ambient input indices unchanged. -/
def induced {n} (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj a b := G.Adj a b ∧ a ∈ W ∧ b ∈ W
  symm.symm _ _ h := ⟨h.1.symm,h.2.2,h.2.1⟩
  loopless.irrefl _ h := h.1.ne rfl

instance {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : Finset (Fin n)) :
    DecidableRel (induced G W).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

theorem induced_eq_delV {n} (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) :
    induced G W = Loc.delV G Wᶜ := by
  ext a b
  simp [Loc.delV_adj,induced]

/-- Gates that are true on at least one edge of H in the original circuit. -/
def active {n} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (C : Circuit) :
    Finset (Fin C.size) := Finset.univ.filter fun j => (support H C j).Nonempty

/-- The gates active on H suffice as a size budget for an exact circuit for H.
This holds for every monotone circuit for G, even one larger than the minimum. -/
theorem induced_circuit {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : Finset (Fin n))
    (C : Circuit) (mono : Monotone2 C) (correct : circuitFun n C = graphFun G ∅) :
    ∃ B : Circuit, Monotone2 B ∧ circuitFun n B = graphFun (induced G W) ∅ ∧
      B.size = (active (induced G W) C).card := by
  classical
  let H := induced G W
  let A := active H C
  let S := Aᶜ
  let U := S.image Fin.val
  let ks := U.sort (· ≥ ·)
  have order : ks.Pairwise (· > ·) := U.sortedGT_sort.pairwise
  have member (j) : j ∈ ks ↔ ∃ i ∈ S, Fin.val i = j := by simp only [ks,Finset.mem_sort,U,Finset.mem_image]
  have inside (j) (hj : j ∈ ks) : j<C.size := by
    obtain ⟨i,_,rfl⟩ := (member j).mp hj
    exact i.isLt
  have ksize : ks.length=S.card := by simp [ks,U,Finset.card_image_of_injective _ Fin.val_injective]
  let D := cut n C ks
  obtain ⟨dm,size,below⟩ := cut_spec C mono ks (sorted_valid order inside)
  change D.size + ks.length = C.size at size
  change Monotone2 D at dm
  obtain ⟨bm,bs,eval⟩ := restrict_spec W D dm
  refine ⟨restrictInputs W D,bm,?_,?_⟩
  · funext x
    rw [eval]
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro on
      have orig := below (masked W x) on
      rw [correct] at orig
      obtain ⟨a,b,ab,ha,hb⟩ : ∃ a b, G.Adj a b ∧ masked W x a = true ∧ masked W x b = true := by
        simpa [graphFun] using orig
      have inW (i) (hi : masked W x i=true) : i ∈ W ∧ x i=true := by
        by_cases h : i ∈ W <;> simp_all [masked]
      exact (by simpa [graphFun] using (show ∃ a b, (induced G W).Adj a b ∧ x a=true ∧ x b=true from
        ⟨a,b,⟨ab,(inW _ ha).1,(inW _ hb).1⟩,(inW _ ha).2,(inW _ hb).2⟩))
    · intro on
      obtain ⟨a,b,ab,ha,hb⟩ : ∃ a b, H.Adj a b ∧ x a=true ∧ x b=true := by
        simpa [graphFun,H] using on
      have off (i) (hi : i ∈ ks) : gateVal n C i (pairInput a b)=false := by
        obtain ⟨j,hj,rfl⟩ := (member i).mp hi
        apply Bool.eq_false_iff.mpr
        intro yes
        apply Finset.mem_compl.mp hj
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _,s(a,b), Finset.mem_filter.mpr ⟨by simpa using ab, row_mk a b ▸ yes⟩⟩
      have pair : circuitFun n D (pairInput a b) = true := by
        rw [show circuitFun n D (pairInput a b)=_ from cut_off C mono ks order inside (pairInput a b) off, correct]
        simpa [graphFun] using (show ∃ i j, G.Adj i j ∧ pairInput a b i = true ∧ pairInput a b j = true from
          ⟨a,b,ab.1,by simp [pairInput],by simp [pairInput]⟩)
      apply PEqualNP.Outside.L_meta_2573.eval_mono D dm (pairInput a b) (masked W x) _ pair
      intro i hi
      simp only [pairInput,decide_eq_true_eq] at hi
      rcases hi with rfl|rfl
      · simp [masked,ab.2.1,ha]
      · simp [masked,ab.2.2,hb]
  · rw [bs]
    change D.size = A.card
    rw [ksize] at size
    have total : S.card+A.card = C.size := by simp [S]
    omega

/-- Every lower bound already proved for an induced subgraph also bounds the
number of old gates that fire on its edge rows. -/
theorem induced_lower {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : Finset (Fin n))
    (C : Circuit) (mono : Monotone2 C) (correct : circuitFun n C = graphFun G ∅) (k : Nat)
    (lower : ∀ (B : Circuit), Monotone2 B → circuitFun n B = graphFun (induced G W) ∅ →
      k ≤ B.size) : k ≤ (active (induced G W) C).card := by
  obtain ⟨B,bm,bc,bs⟩ := induced_circuit G W C mono correct
  exact bs ▸ lower B bm bc

/-- If G violates the target and H already satisfies it, the gates that disappear
on H strictly underpay the decrease in edges plus cover size. This tests any
simultaneous vertex deletion and uses the original, unmodified gate rows. -/
theorem strict_deficit {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : Finset (Fin n))
    (C : Circuit) (mono : Monotone2 C) (correct : circuitFun n C = graphFun G ∅)
    (gap : C.size+1 < G.edgeFinset.card + Loc.tau G)
    (lower : ∀ B : Circuit, Monotone2 B → circuitFun n B = graphFun (induced G W) ∅ →
      (induced G W).edgeFinset.card + Loc.tau (induced G W) ≤ B.size+1) :
    ((active (induced G W) C)ᶜ).card + (induced G W).edgeFinset.card + Loc.tau (induced G W)
      < G.edgeFinset.card + Loc.tau G := by
  obtain ⟨B,bm,bc,bs⟩ := induced_circuit G W C mono correct
  have bound := lower B bm bc
  rw [bs] at bound
  have total : ((active (induced G W) C)ᶜ).card + (active (induced G W) C).card = C.size := by simp
  omega

#print axioms strict_deficit
#print axioms induced_circuit
#print axioms induced_lower
end VertexPeel.BatchExchange
