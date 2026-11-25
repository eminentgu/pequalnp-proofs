import ZeroFold
import SideReaders
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

namespace VertexPeel.SidePeel

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.Core PEqualNP.MetaComplexity.CoverPromise
open PEqualNP.ReadK PEqualNP.ReadTwo PEqualNP.EdgeOwnership
open ZeroFold SideReaders

/-- If a set of wires contains all changed raw inputs but misses the changed
    output, some gate reads that set and produces a wire outside it. -/
theorem crosses {n : ℕ} (C : Circuit) (ao : IsAO2 n C) (X : Finset ℕ) (x y : Fin n → Bool)
    (agree : ∀ a : Fin n, a.val ∉ X → x a = y a)
    (diff : wval C x C.output ≠ wval C y C.output) (outside : C.output ∉ X) :
    ∃ j, ∃ hj : j < C.gates.length, n+j ∉ X ∧ ∃ t ∈ X, t ∈ C.gates[j].inputs := by
  classical
  by_contra! never
  have ok : ∀ w : ℕ, w ∉ X → wval C x w = wval C y w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hx
      by_cases raw : w < n
      · exact (wval_in C x ⟨w,raw⟩).trans ((agree ⟨w,raw⟩ hx).trans (wval_in C y ⟨w,raw⟩).symm)
      by_cases past : n + C.gates.length ≤ w
      · rw [wval_past C x w past,wval_past C y w past]
      obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
      have hj : j < C.gates.length := by omega
      obtain ⟨a,b,hab,ha,hb,_⟩ := two n C ao j hj
      have ex (t : ℕ) (ht : t ∈ C.gates[j].inputs) : t ∉ X := fun e => never j hj hx t e ht
      rw [wval_gate C x j a b hj hab ha hb,wval_gate C y j a b hj hab ha hb,
        ih a ha (ex a (by simp [hab])),ih b hb (ex b (by simp [hab]))]
  exact diff (ok _ outside)

theorem sensitive {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (correct : circuitFun n C = graphFun G ∅) {a u : Fin n} (hua : G.Adj u a) :
    ∃ x y : Fin n → Bool, (∀ t : Fin n, t ≠ a → x t = y t) ∧ wval C x C.output ≠ wval C y C.output := by
  refine ⟨bits {u,a},bits {u,u},by intro t ht; simp [bits,ht],?_⟩
  change circuitFun n C _ ≠ circuitFun n C _
  rw [correct]
  intro eq
  exact (G.loopless.irrefl _) ((pair_iff G u u).mp (eq.symm.trans ((pair_iff G u a).mpr hua)))

theorem residual_nonzero {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (correct : circuitFun n C = graphFun G ∅) {a : Fin n}
    (edge : ∃ u v, G.Adj u v ∧ u ≠ a ∧ v ≠ a) : fv C {a} C.output ≠ fun _ => false := by
  obtain ⟨u,v,h,hu,hv⟩ := edge
  have unchanged : zr {a} (bits {u,v}) = bits {u,v} := by
    funext t
    by_cases et : t = a
    · subst t
      simp [zr,bits,hu.symm,hv.symm]
    · simp [zr,et]
  intro z
  have zz := congrFun z (bits {u,v})
  change circuitFun n C (zr {a} (bits {u,v})) = false at zz
  rw [unchanged,correct,(pair_iff G u v).mpr h] at zz
  cases zz

/-- In a circuit computing an edge function, zeroing a raw input that makes a
    reader constantly false also disables a different gate, provided an edge
    survives the restriction. -/
theorem second_of_zero {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (correct : circuitFun n C = graphFun G ∅)
    (a u : Fin n) (edge : G.Adj u a) (remaining : ∃ v w, G.Adj v w ∧ v ≠ a ∧ w ≠ a)
    (j : ℕ) (hj : j < C.gates.length) (zero : fv C {a} (n+j) = fun _ => false) :
    ∃ k, k < C.gates.length ∧ k ≠ j ∧ ¬ Mg C {a} k := by
  classical
  have distinct : C.output ≠ n+j := fun eq => residual_nonzero G C correct remaining (eq ▸ zero)
  obtain ⟨x,y,eq,diff⟩ := sensitive G C correct edge
  obtain ⟨k,hk,out,t,ht,read⟩ := crosses C ao {a.val,n+j} x y (by
    intro b hb
    apply eq
    rintro rfl
    simp at hb) diff (by simp [no_raw_output G correct a,distinct])
  have hkj : k ≠ j := by rintro rfl; simp at out
  refine ⟨k,hk,hkj,kill C ao _ k hk t read ?_⟩
  rcases Finset.mem_insert.mp ht with e | e
  · rw [e]; exact fv_in0 C _ a (by simp)
  · rw [Finset.mem_singleton.mp e]; exact zero

open Classical in
private theorem card_two {k j : ℕ} (C : Circuit) (Z : Finset (Fin n))
    (hk : k < C.size) (hj : j < C.size) (ne : k ≠ j) (badk : ¬Mg C Z k) (badj : ¬Mg C Z j) :
    ((Finset.range C.size).filter (Mg C Z)).card + 2 ≤ C.size := by
  classical
  let F := (Finset.range C.size).filter (Mg C Z)
  have sub : insert k (insert j F) ⊆ Finset.range C.size := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Finset.mem_range.mpr hk
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Finset.mem_range.mpr hj
    exact (Finset.mem_filter.mp hi).1
  have h := Finset.card_le_card sub
  simp [F,ne,badk,badj] at h
  omega

theorem restrict_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (correct : circuitFun n C = graphFun G ∅) (a : Fin n) :
    fv C {a} C.output = fun y : Fin n → Bool =>
      @decide (∃ u v : Fin n, (G.deleteIncidenceSet a).Adj u v ∧ y u = true ∧ y v = true)
        (Classical.propDecidable _) := by
  classical
  funext x
  change circuitFun n C (zr {a} x) = _
  rw [correct]
  simp [graphFun,zr,SimpleGraph.deleteIncidenceSet_adj]
  grind

/-- Every AO₂ circuit for this class admits the restriction of one of the
    specified inputs for which at least two gates can be omitted. -/
theorem two_nonmerging {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B : Finset ℕ) (bounded : ∀ b ∈ B, b < n) (nonempty : B.Nonempty)
    (independent : ∀ u v : Fin n, u.val ∉ B → v.val ∉ B → ¬ G.Adj u v)
    (neighbor : ∀ a : Fin n, a.val ∈ B → ∃ u : Fin n, u.val ∉ B ∧ G.Adj u a)
    (remaining : ∀ a : Fin n, a.val ∈ B → ∃ u v, G.Adj u v ∧ u ≠ a ∧ v ≠ a)
    (noSquare : NoFourCycle G) (high : ∀ a : Fin n, a.val ∈ B → 2 ≤ G.degree a)
    (C : Circuit) (ao : IsAO2 n C) (correct : circuitFun n C = graphFun G ∅) :
    ∃ a : Fin n, a.val ∈ B ∧ ∃ j < C.size, ∃ k < C.size, k ≠ j ∧ ¬ Mg C {a} j ∧ ¬ Mg C {a} k := by
  classical
  let hit (j : ℕ) := ∃ hj : j < C.gates.length, ∃ t ∈ B, t ∈ C.gates[j].inputs
  have someHit : ∃ j, hit j := by
    obtain ⟨v,hv⟩ := nonempty
    let a : Fin n := ⟨v,bounded _ hv⟩
    obtain ⟨u,_,edge⟩ := neighbor a hv
    obtain ⟨x,y,eq,diff⟩ := sensitive G C correct edge
    obtain ⟨j,hj,_,t,ht,read⟩ := crosses C ao {a.val} x y
      (fun b hb => eq b (by rintro rfl; simp at hb)) diff (by simpa using no_raw_output G correct a)
    exact ⟨j,hj,t,(Finset.mem_singleton.mp ht) ▸ hv,read⟩
  let r := Nat.find someHit
  obtain ⟨hr,t,ht,read⟩ := Nat.find_spec someHit
  change r < C.gates.length at hr
  change t ∈ C.gates[r].inputs at read
  let a : Fin n := ⟨t,bounded t ht⟩
  have az : fv C {a} a.val = fun _ => false := fv_in0 C _ a (by simp)
  have bad : ¬Mg C {a} r := kill C ao _ r hr t read az
  by_cases gz : fv C {a} (n+r) = fun _ => false
  · obtain ⟨u,_,edge⟩ := neighbor a ht
    obtain ⟨k,hk,ne,hd⟩ := second_of_zero G C ao correct a u edge (remaining a ht) r hr gz
    exact ⟨a,ht,r,hr,k,hk,ne,bad,hd⟩
  obtain ⟨l,m,ports,hl,hm,op⟩ := two n C ao r hr
  have use : t = l ∨ t = m := by simpa [ports] using read
  have isOr : C.gates[r].op = .or := op.resolve_left (by
    intro e
    apply gz
    funext x
    rw [fv_and C {a} r l m hr ports hl hm e]
    rcases use with h | h
    · rw [← h]; change (fv C {a} a.val x && _) = _; rw [az]; rfl
    · rw [← h]; change (_ && fv C {a} a.val x) = _; rw [az,Bool.and_false])
  have lm : l ≠ m := by
    rintro h
    have lt : l = t := by rcases use with h1 | h1 <;> omega
    apply gz
    funext x
    rw [fv_or C {a} r l m hr ports hl hm isOr,← h,lt]
    change (fv C {a} a.val x || _) = _
    rw [az]; rfl
  obtain ⟨d,hd,hdr,dt⟩ : ∃ d, d ∈ C.gates[r].inputs ∧ d < n+r ∧ d ≠ t := by
    rcases use with e | e
    · exact ⟨m,by simp [ports],hm,by omega⟩
    · exact ⟨l,by simp [ports],hl,by omega⟩
  let pre := C.gates.take r
  let post := C.gates.drop (r+1)
  have prelen : pre.length = r := List.length_take_of_le (Nat.le_of_lt hr)
  have decomp : pre ++ C.gates[r] :: post = C.gates := by
    simp [pre,post,List.getElem_cons_drop]
  have noEarlier (i : ℕ) (hi : i < r) {q : Gate} (hq : pre[i]? = some q) :
      ∀ s ∈ q.inputs, s ∉ B := by
    have hi' : i < C.gates.length := by omega
    have same : q = C.gates[i] := by simpa [pre,List.getElem?_take,hi,hi'] using hq.symm
    intro s hs sb
    exact (Nat.find_min someHit hi) ⟨hi',s,sb,same ▸ hs⟩
  have valid : ∀ i q, pre[i]? = some q → (q.op = .and ∨ q.op = .or) ∧ q.inputs ≠ [] ∧
      ∀ z ∈ q.inputs, z < n+i ∧ z ∉ B := by
    intro i q hq
    obtain ⟨hi',eq⟩ := List.getElem?_eq_some_iff.mp hq
    have hi : i < r := prelen ▸ hi'
    have hC : i < C.gates.length := by omega
    have same : q = C.gates[i] := by simpa [pre,List.getElem?_take,hi,hC] using hq.symm
    obtain ⟨l',m',ee,hl',hm',oo⟩ := two n C ao i hC
    refine ⟨same ▸ oo,by simp [same,ee],?_⟩
    intro z hz
    have lm' : z = l' ∨ z = m' := by simpa [same,ee] using hz
    exact ⟨by rcases lm' with rfl | rfl <;> assumption,noEarlier i hi hq z hz⟩
  have corr : circuitFun n ⟨pre ++ C.gates[r] :: post,C.output⟩ = graphFun G ∅ := by
    simpa [decomp] using correct
  obtain ⟨s,sb,sr,q,hq,sq⟩ := first_or_has_second_reader (a := a) G B bounded independent
    (neighbor a ht) noSquare (high a ht) isOr read ht hd dt (by simpa [prelen] using hdr) valid corr
  have qp : q ∈ post := (List.mem_append.mp hq).resolve_left (by
    intro hpre
    obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hpre
    have ip : i < r := prelen ▸ hi
    exact noEarlier i ip (List.getElem?_eq_some_iff.mpr ⟨hi,eq⟩) s sq sb)
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp qp
  have hik : r+1+i < C.gates.length := by simp [post] at hi; omega
  have e' : C.gates[r+1+i] = q := by simpa [post,List.getElem_drop] using eq
  let b : Fin n := ⟨s,bounded s sb⟩
  have bz : fv C {b} s = fun _ => false := fv_in0 C _ b (by simp)
  exact ⟨b,sb,r,hr,r+1+i,hik,by omega, kill C ao _ r hr s sr bz,
    kill C ao _ _ hik s (e' ▸ sq) bz⟩

abbrev Drops {n : ℕ} (G : SimpleGraph (Fin n)) (a : Fin n) : Prop :=
  ∃ S : Finset (Fin n), IsVertexCover (G.deleteIncidenceSet a) S ∧
    ∀ T : Finset (Fin n), IsVertexCover G T → S.card < T.card

theorem remaining_of_stable {n : ℕ} (G : SimpleGraph (Fin n)) (a : Fin n)
    (edge : ∃ u v, G.Adj u v) (stable : ¬ Drops G a) :
    ∃ u v, G.Adj u v ∧ u ≠ a ∧ v ≠ a := by
  classical
  by_contra! none
  apply stable
  refine ⟨∅,?_,?_⟩
  · intro u v h
    obtain ⟨uv,ua,va⟩ := SimpleGraph.deleteIncidenceSet_adj.mp h
    exact (va (none u v uv ua)).elim
  · intro T cover
    obtain ⟨u,v,e⟩ := edge
    rcases cover u v e with h | h
    · exact Finset.card_pos.mpr ⟨_,h⟩
    · exact Finset.card_pos.mpr ⟨_,h⟩

/-- The exact card conclusion for a chosen side of noncritical degree-two
    vertices, uniformly for all AO₂ circuits with a single vertex witness. -/
theorem peel {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B : Finset ℕ) (bounded : ∀ b ∈ B, b < n) (nonempty : B.Nonempty)
    (independent : ∀ u v : Fin n, u.val ∉ B → v.val ∉ B → ¬ G.Adj u v)
    (neighbor : ∀ a : Fin n, a.val ∈ B → ∃ u : Fin n, u.val ∉ B ∧ G.Adj u a)
    (noSquare : NoFourCycle G) (deg : ∀ a : Fin n, a.val ∈ B → G.degree a = 2)
    (stable : ∀ a : Fin n, a.val ∈ B → ¬Drops G a) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C → circuitFun n C = graphFun G ∅ →
      ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = (fun y : Fin n → Bool =>
        @decide (∃ u v : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj u v ∧ y u = true ∧ y v = true)
          (Classical.propDecidable _)) ∧ D.size + G.degree z ≤ C.size ∧
          (Drops G z → D.size + G.degree z + 1 ≤ C.size) := by
  classical
  obtain ⟨t,ht⟩ := nonempty
  let a : Fin n := ⟨t,bounded t ht⟩
  have hasEdge : ∃ u v, G.Adj u v := by
    obtain ⟨u,_,e⟩ := neighbor a ht
    exact ⟨u,a,e⟩
  let realizable (k : ℕ) := ∃ C : Circuit, IsAO2 n C ∧ circuitFun n C = graphFun G ∅ ∧ C.size = k
  by_cases h : ∃ k, realizable k
  · obtain ⟨C,ao,eq,size⟩ := Nat.find_spec h
    obtain ⟨z,hz,j,hj,k,hk,ne,badj,badk⟩ := two_nonmerging G B bounded ⟨t,ht⟩ independent neighbor
      (fun b hb => remaining_of_stable G b hasEdge (stable b hb)) noSquare
      (fun b hb => (deg b hb).ge) C ao eq
    obtain ⟨D,dao,dc,ds⟩ := compile C ao {z}
    have budget := card_two C {z} hk hj ne badk badj
    refine ⟨z,by simp [deg z hz],?_⟩
    intro E eao ecomp
    have le : Nat.find h ≤ E.size := Nat.find_min' h ⟨E,eao,ecomp,rfl⟩
    refine ⟨D,dao,dc.trans (restrict_correct G C eq z),?_,fun drop => (stable z hz drop).elim⟩
    rw [deg z hz]
    omega
  · refine ⟨a,by simp [deg a ht],?_⟩
    intro C ao correct
    exact (h ⟨C.size,C,ao,correct,rfl⟩).elim

end VertexPeel.SidePeel
