import MixedFold
import PendantCross

namespace VertexPeel.ThreeGatePeel
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
    PEqualNP.TopForm PEqualNP.ReadTwo
open MixedFold SideReaders SidePeel PendantCross

def assign (a b : Fin n) (p : Bool) : Restr n :=
  fun x i => if i=b then false else if i=a then p else x i

theorem raw_a (C : Circuit) {a b : Fin n} (ab : a ≠ b) (p : Bool) :
    val C (assign a b p) a.val = fun _ => p := by
  funext x
  change wval C _ a.val = _
  rw [ZeroFold.wval_in]
  simp [assign,ab]

theorem raw_b (C : Circuit) (a b : Fin n) (p : Bool) :
    val C (assign a b p) b.val = fun _ => false := by
  funext x
  change wval C _ b.val = _
  rw [ZeroFold.wval_in]
  simp [assign]

theorem raw_inputs (C : Circuit) (a b : Fin n) (p : Bool) (i : Fin n) :
    Const (val C (assign a b p) i.val) ∨ val C (assign a b p) i.val = fun x => x i := by
  by_cases ib : i=b
  · subst i; exact Or.inl ⟨_,raw_b C a b p⟩
  by_cases ia : i=a
  · subst i; exact Or.inl ⟨_,raw_a C ib p⟩
  right; funext x
  change wval C _ i.val = _
  rw [ZeroFold.wval_in]; simp [assign,ib,ia]

theorem eval_cut (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (cor : circuitFun n C = graphFun G ∅) {a b : Fin n} (only : ∀ t, G.Adj a t → t=b) (p : Bool) :
    val C (assign a b p) C.output = graphFun (G.deleteIncidenceSet b) ∅ := by
  classical
  funext x
  change circuitFun n C (assign a b p x) = _
  rw [cor]
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or]
  apply decide_eq_decide.mpr
  simp only [SimpleGraph.deleteIncidenceSet_adj]
  constructor
  · rintro ⟨u,v,uv,hu,hv⟩
    have ub : u≠b := by rintro rfl; simp [assign] at hu
    have vb : v≠b := by rintro rfl; simp [assign] at hv
    have ua : u≠a := by rintro rfl; exact vb (only v uv)
    have va : v≠a := by rintro rfl; exact ub (only u uv.symm)
    exact ⟨u,v,⟨uv,ub,vb⟩,by simpa [assign,ub,ua] using hu,by simpa [assign,vb,va] using hv⟩
  · rintro ⟨u,v,⟨uv,ub,vb⟩,hu,hv⟩
    have ua : u≠a := by rintro rfl; exact vb (only v uv)
    have va : v≠a := by rintro rfl; exact ub (only u uv.symm)
    exact ⟨u,v,uv,by simpa [assign,ub,ua] using hu,by simpa [assign,vb,va] using hv⟩

theorem residual_nonconstant (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (cor : circuitFun n C = graphFun G ∅) {a b : Fin n} (only : ∀ t, G.Adj a t → t=b)
    (remaining : ∃ u v, G.Adj u v ∧ u≠b ∧ v≠b) (p : Bool) :
    ¬Const (val C (assign a b p) C.output) := by
  rw [eval_cut G C cor only p]
  obtain ⟨u,v,uv,ub,vb⟩ := remaining
  rintro ⟨q,hq⟩
  let H := G.deleteIncidenceSet b
  have pos := (pair_iff H u v).mpr (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨uv,ub,vb⟩)
  have neg : ¬graphFun H ∅ (bits {u,u}) = true := fun e => (H.loopless.irrefl _) ((pair_iff H u u).mp e)
  change graphFun H ∅ = _ at hq
  rw [hq] at pos neg
  exact neg pos

abbrev Three (C : Circuit) (r : Restr n) : Prop :=
  ∃ i < C.size, ∃ j < C.size, ∃ k < C.size, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
    ¬New C r i ∧ ¬New C r j ∧ ¬New C r k

theorem find_third (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (ao : IsAO2 n C)
    (cor : circuitFun n C = graphFun G ∅) (a b : Fin n) (ab : G.Adj a b) (r : Restr n)
    (ca : Const (val C r a.val)) (cb : Const (val C r b.val)) (out : ¬Const (val C r C.output))
    {i j : ℕ} (ne : i ≠ j) (hi : i < C.gates.length) (hj : j < C.gates.length)
    (ci : Const (val C r (n+i))) (sj : Reads C j a.val ∨ Reads C j b.val) : Three C r := by
  classical
  have ni : ¬New C r i := fun h => h.2.2 ci
  have nj : ¬New C r j := by
    rcases sj with s | s
    · exact kill C ao r hj s.choose_spec ca
    · exact kill C ao r hj s.choose_spec cb
  have oi : C.output ≠ n+i := fun e => out (e ▸ ci)
  have both_off (cj : Const (val C r (n+j))) : Three C r := by
    let X : Finset ℕ := {a.val,b.val,n+i,n+j}
    have oj : C.output ≠ n+j := fun e => out (e ▸ cj)
    obtain ⟨x,y,e,diff⟩ := sensitive G C cor ab.symm
    obtain ⟨k,hk,outside,t,ht,port⟩ := crosses C ao X x y
      (fun v hv => e v (by rintro rfl; exact hv (by simp [X]))) diff
      (by simp [X,no_raw_output G cor a,no_raw_output G cor b,oi,oj])
    have ik : i ≠ k := by rintro rfl; simp [X] at outside
    have jk : j ≠ k := by rintro rfl; simp [X] at outside
    have ct : Const (val C r t) := by
      simp only [X,Finset.mem_insert,Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl <;> assumption
    exact ⟨i,hi,j,hj,k,hk,ne,ik,jk,ni,nj,kill C ao r hk port ct⟩
  by_cases cj : Const (val C r (n+j))
  · exact both_off cj
  have missing : ∃ t : Fin n, (t=a ∨ t=b) ∧ t.val ∉ C.gates[j].inputs := by
    by_cases ma : a.val ∈ C.gates[j].inputs
    · refine ⟨b,Or.inr rfl,fun mb => ?_⟩
      exact cj (both C ao r hj (fun e => ab.ne (Fin.ext e)) ma mb ca cb)
    · exact ⟨a,Or.inl rfl,ma⟩
  obtain ⟨s,side,miss⟩ := missing
  have sc : Const (val C r s.val) := by rcases side with rfl | rfl <;> assumption
  have essential : ∃ x y : Fin n → Bool, (∀ t, t ≠ s → x t = y t) ∧ wval C x C.output ≠ wval C y C.output := by
    rcases side with rfl | rfl
    · exact sensitive G C cor ab.symm
    · exact sensitive G C cor ab
  obtain ⟨x,y,e,diff⟩ := essential
  obtain ⟨k,hk,outside,t,ht,port⟩ := crosses C ao {s.val,n+i} x y
    (fun v hv => e v (by rintro rfl; simp at hv)) diff (by simp [no_raw_output G cor s,oi])
  have ik : i ≠ k := by rintro rfl; simp at outside
  have st : t=s.val ∨ t=n+i := by simpa using ht
  by_cases jk : j = k
  · subst k
    have porti : n+i ∈ C.gates[j].inputs := by
      rcases st with e | e
      · exact (miss (e ▸ port)).elim
      · exact e ▸ port
    have cj' : Const (val C r (n+j)) := by
      rcases sj with sa | sb
      · exact both C ao r hj (by have := a.isLt; omega) sa.choose_spec porti ca ci
      · exact both C ao r hj (by have := b.isLt; omega) sb.choose_spec porti cb ci
    exact both_off cj'
  · have ct : Const (val C r t) := by rcases st with rfl | rfl <;> assumption
    exact ⟨i,hi,j,hj,k,hk,ne,ik,jk,ni,nj,kill C ao r hk port ct⟩

/-- On a pendant edge a--b, if b has another neighbor and another edge survives
    cutting b, one can choose a's value while b is zero so that at least three
    gates of the circuit are semantically redundant under that restriction. -/
theorem exists_three (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (ao : IsAO2 n C) (cor : circuitFun n C = graphFun G ∅)
    {a b c : Fin n} (ab : G.Adj a b) (bc : G.Adj b c) (ca : c≠a)
    (only : ∀ t, G.Adj a t → t=b) (remaining : ∃ u v, G.Adj u v ∧ u≠b ∧ v≠b) :
    ∃ p : Bool, Three C (assign a b p) := by
  classical
  obtain ⟨i,ia⟩ := raw_reader G C ao cor a b ab
  by_cases ib : Reads C i b.val
  · obtain ⟨j,ji,sj⟩ := other_reader G C ao cor ab (fun ac => bc.ne (only _ ac).symm) bc ca ia ib
    have hj : j < C.gates.length := by rcases sj with h | h <;> exact h.choose
    let r := assign a b false
    have va : Const (val C r a.val) := ⟨_,raw_a C ab.ne false⟩
    have vb : Const (val C r b.val) := ⟨_,raw_b C _ _ _⟩
    have ci := both C ao r ia.choose (fun e => ab.ne (Fin.ext e)) ia.choose_spec ib.choose_spec va vb
    exact ⟨false,find_third G C ao cor a b ab r va vb (residual_nonconstant G C cor only remaining _)
      ji.symm ia.choose hj ci sj⟩
  · obtain ⟨j,jb⟩ := raw_reader G C ao cor b a ab.symm
    have ij : i ≠ j := fun eq => ib (eq ▸ jb)
    let p := decide ((C.gates[i]'ia.choose).op = .or)
    let r := assign a b p
    have va : val C r a.val = fun _ => p := raw_a C ab.ne _
    have vb : Const (val C r b.val) := ⟨_,raw_b C _ _ _⟩
    have ci := canal C ao r ia.choose ia.choose_spec va
    exact ⟨p,find_third G C ao cor a b ab r ⟨_,va⟩ vb (residual_nonconstant G C cor only remaining _)
      ij ia.choose jb.choose ci (Or.inr jb)⟩

/-- Cutting the joint b of a pendant path saves at least three gates, even when
    b has higher degree. This construction works for every realization. -/
theorem cut_joint (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (ao : IsAO2 n C) (cor : circuitFun n C = graphFun G ∅)
    {a b c : Fin n} (ab : G.Adj a b) (bc : G.Adj b c) (ca : c≠a)
    (only : ∀ t, G.Adj a t → t=b) (remaining : ∃ u v, G.Adj u v ∧ u≠b ∧ v≠b) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun (G.deleteIncidenceSet b) ∅ ∧
      D.size + 3 ≤ C.size := by
  classical
  obtain ⟨p,i,hi,j,hj,k,hk,ij,ik,jk,bi,bj,bk⟩ := exists_three G C ao cor ab bc ca only remaining
  let r := assign a b p
  obtain ⟨D,dao,dc,budget⟩ := compile C ao r (raw_inputs C a b p) (residual_nonconstant G C cor only remaining p)
  let F := (Finset.range C.size).filter (New C r)
  have sub : insert i (insert j (insert k F)) ⊆ Finset.range C.size := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | h
    · exact Finset.mem_range.mpr hi
    rcases Finset.mem_insert.mp h with rfl | h
    · exact Finset.mem_range.mpr hj
    rcases Finset.mem_insert.mp h with rfl | h
    · exact Finset.mem_range.mpr hk
    exact (Finset.mem_filter.mp h).1
  have bound := Finset.card_le_card sub
  change ¬ New C r i at bi
  change ¬ New C r j at bj
  change ¬ New C r k at bk
  simp [F,ij,ik,jk,bi,bj,bk] at bound
  exact ⟨D,dao,dc.trans (eval_cut G C cor only p),by omega⟩

end VertexPeel.ThreeGatePeel
