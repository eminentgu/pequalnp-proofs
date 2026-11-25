import NeighborPorts

namespace VertexPeel.NeighborPorts
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.Core
open VertexPeel.ZeroFold VertexPeel.RowGraph VertexPeel.RowCharge VertexPeel.AndSeparation

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

/-- An independent input cannot dominate all of x's canonical ports if adjoining x completes an edge. -/
theorem separating_port (ao : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅)
    (x t : Fin n) (I : Fin n → Bool) (xt : G.Adj x t) (it : I t=true)
    (ind : graphFun G ∅ I=false) :
    ∃ j ∈ lit C x, wval C I (port C x j)=false := by
  classical
  have eval (z : Fin n → Bool) : wval C z C.output = graphFun G ∅ z := congrFun ok z
  have off : wval C (single x) C.output=false := by rw [eval]; simp [graphFun,single]
  have on : wval C (pairInput x t) C.output=true := by
    rw [eval]; simp [graphFun]; exact ⟨x,t,xt,by simp [pairInput],by simp [pairInput]⟩
  obtain ⟨j,_,opp⟩ := opposing_ancestor C ao (single x) I (pairInput x t) (by
    intro i hi
    rcases (show i=x ∨ i=t by simpa [pairInput] using hi) with rfl|rfl
    · exact Or.inl (by simp [single])
    · exact Or.inr it) _ off ((eval I).trans ind) on
  obtain ⟨yes,zero⟩ := orientation C x I j opp
  exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr opp.1.1,opp.1,yes⟩,zero⟩

/-- Fewer than degree(x) alternative vertices cannot block all neighbors of x. -/
private theorem unblocked (sq : NoFourCycle G) (U : Finset (Fin n)) (x : Fin n)
    (absent : x ∉ U) (small : U.card < G.degree x) :
    ∃ t, G.Adj x t ∧ ∀ y ∈ U, ¬G.Adj y t := by
  classical
  by_contra! no
  have pick (t : Fin n) : ∃ y : Fin n, G.Adj x t → y ∈ U ∧ G.Adj y t := by
    by_cases xt : G.Adj x t
    · obtain ⟨y,inU,yt⟩ := no t xt
      exact ⟨y,fun _ => ⟨inU,yt⟩⟩
    · exact ⟨x,fun h => (xt h).elim⟩
  choose Y hy using pick
  have inject : Set.InjOn Y (G.neighborFinset x : Set (Fin n)) := by
    intro a ha b hb same
    have xa := (G.mem_neighborFinset _ _).mp ha
    have xb := (G.mem_neighborFinset _ _).mp hb
    obtain ⟨aU,ya⟩ := hy a xa
    have yb : G.Adj (Y a) b := same ▸ (hy b xb).2
    have ne : x ≠ Y a := fun e => absent (e ▸ aU)
    exact Finset.card_le_one.mp (sq x (Y a) ne) a (Finset.mem_filter.mpr ⟨Finset.mem_univ _,xa,ya⟩)
      b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,xb,yb⟩)
  have b := Finset.card_le_card_of_injOn (s:=G.neighborFinset x) Y (fun t ht => (hy t ((G.mem_neighborFinset _ _).mp ht)).1) inject
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at b
  omega

/-- If too few physical ANDs see x, every choice of one different singleton
activator per canonical port contains a graph edge. The graph need not be bipartite. -/
theorem transversal_edge (ao : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅)
    (sq : NoFourCycle G) (x : Fin n) (few : (lit C x).card < G.degree x)
    (Y : ℕ → Fin n) (other : ∀ j ∈ lit C x, Y j ≠ x)
    (hit : ∀ j ∈ lit C x, wval C (single (Y j)) (port C x j)=true) :
    ∃ i ∈ lit C x, ∃ j ∈ lit C x, G.Adj (Y i) (Y j) := by
  classical
  let U := (lit C x).image Y
  have absent : x ∉ U := by
    rintro hx
    obtain ⟨j,hj,eq⟩ := Finset.mem_image.mp hx
    exact other j hj eq
  have small : U.card < G.degree x := lt_of_le_of_lt Finset.card_image_le few
  obtain ⟨t,xt,avoid⟩ := unblocked G sq U x absent small
  by_contra! no
  let I (v : Fin n) := decide (v=t ∨ v ∈ U)
  have off : graphFun G ∅ I=false := by
    have ind : ¬∃ a b, G.Adj a b ∧ I a=true ∧ I b=true := by
      rintro ⟨a,b,ab,ha,hb⟩
      rcases (show a=t ∨ a∈U by simpa [I] using ha) with ea|aU
      · rcases (show b=t ∨ b∈U by simpa [I] using hb) with eb|bU
        · exact ab.ne (ea.trans eb.symm)
        · exact avoid b bU (ea ▸ ab.symm)
      · rcases (show b=t ∨ b∈U by simpa [I] using hb) with eb|bU
        · exact avoid a aU (eb ▸ ab)
        · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp aU
          obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp bU
          exact no i hi j hj ab
    simp [graphFun,ind]
  obtain ⟨j,hj,zero⟩ := separating_port G C ao ok x t I xt (by simp [I]) off
  have incl : ∀ v, single (Y j) v=true → I v=true := by
    intro v hv
    have eq : v=Y j := by simpa [single] using hv
    exact decide_eq_true (Or.inr (eq ▸ Finset.mem_image_of_mem Y hj))
  exact Bool.noConfusion (zero.symm.trans (wire_mono C ao incl _ (hit j hj)))

#print axioms separating_port
#print axioms transversal_edge
end VertexPeel.NeighborPorts
