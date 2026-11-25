import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

namespace VertexPeel.ShortCycle

open SimpleGraph PEqualNP.TopForm

abbrev TriangleFree {n : ℕ} (G : SimpleGraph (Fin n)) :=
  ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a

/-- Such an extra edge would be a loop, or would close a triangle or a four-cycle. -/
private def blocked {m : ℕ} (H : SimpleGraph (Fin m)) (a b : Fin m) : Prop :=
  a = b ∨ (∃ c, H.Adj a c ∧ H.Adj c b) ∨
    ∃ c d, a ≠ d ∧ c ≠ b ∧ H.Adj a c ∧ H.Adj c d ∧ H.Adj d b

private instance {m : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (a b : Fin m) :
    Decidable (blocked H a b) := by unfold blocked; infer_instance

private theorem uniqueNeighbor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (square : NoFourCycle G) {a b c d : Fin n} (ab : a ≠ b)
    (ac : G.Adj a c) (bc : G.Adj b c) (ad : G.Adj a d) (bd : G.Adj b d) : c = d := by
  apply Finset.card_le_one.mp (square a b ab)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ac,bc⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ad,bd⟩

private theorem noExtra {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (tri : TriangleFree G) (square : NoFourCycle G) (H : SimpleGraph (Fin m))
    (f : Fin m ↪ Fin n) (edges : ∀ a b, H.Adj a b → G.Adj (f a) (f b))
    (a b : Fin m) (block : blocked H a b) : ¬ G.Adj (f a) (f b) := by
  rcases block with rfl | ⟨c,ac,cb⟩ | ⟨c,d,ad,cb,ac,cd,db⟩
  · exact G.loopless.irrefl _
  · exact fun ab => tri _ _ _ (edges _ _ ac) (edges _ _ cb) ab.symm
  · intro ab
    exact cb (f.injective (uniqueNeighbor G square (fun h => ad (f.injective h))
      (edges _ _ ac) (edges _ _ cd).symm ab (edges _ _ db)))

private def induced {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (tri : TriangleFree G) (square : NoFourCycle G) (H : SimpleGraph (Fin m))
    (f : Fin m ↪ Fin n) (edges : ∀ a b, H.Adj a b → G.Adj (f a) (f b))
    (no : ∀ a b, ¬ H.Adj a b → blocked H a b ∨ ¬ G.Adj (f a) (f b)) : H ↪g G where
  toEmbedding := f
  map_rel_iff' := by
    intro a b
    refine ⟨fun image => ?_,edges a b⟩
    by_contra missing
    exact (no a b missing).elim (fun h => noExtra G tri square H f edges a b h image)
      (fun h => h image)

abbrev Pattern {n : ℕ} (G : SimpleGraph (Fin n)) :=
  Nonempty (cycleGraph 5 ↪g G) ∨ Nonempty (cycleGraph 6 ↪g G) ∨ Nonempty (pathGraph 6 ↪g G)

private def endpoints {m : ℕ} (a b u v : Fin m) : Prop :=
  (a = u ∧ b = v) ∨ (a = v ∧ b = u)

private instance {m : ℕ} (a b u v : Fin m) : Decidable (endpoints a b u v) := by
  unfold endpoints; infer_instance

private theorem pentagon {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (tri : TriangleFree G) (square : NoFourCycle G) (f : Fin 5 ↪ Fin n)
    (edges : ∀ a b, (cycleGraph 5).Adj a b → G.Adj (f a) (f b)) : Pattern G := by
  have table : ∀ a b, ¬(cycleGraph 5).Adj a b → blocked (cycleGraph 5) a b := by decide +kernel
  exact Or.inl ⟨induced G tri square _ f edges (fun a b h => Or.inl (table a b h))⟩

private theorem pathSix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (tri : TriangleFree G) (square : NoFourCycle G) (f : Fin 6 ↪ Fin n)
    (edges : ∀ a b, (pathGraph 6).Adj a b → G.Adj (f a) (f b)) : Pattern G := by
  let front : Fin 5 ↪ Fin 6 := Fin.castLEEmb (by decide)
  let back : Fin 5 ↪ Fin 6 := Fin.succEmb _
  have five (e : Fin 5 ↪ Fin 6)
      (chain : ∀ a b, (cycleGraph 5).Adj a b → (pathGraph 6).Adj (e a) (e b) ∨ endpoints a b 0 4)
      (closing : G.Adj (f (e 0)) (f (e 4))) : Pattern G := by
    apply pentagon G tri square (e.trans f)
    intro a b h
    rcases chain a b h with path | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact edges _ _ path
    · exact closing
    · exact closing.symm
  by_cases h04 : G.Adj (f 0) (f 4)
  · exact five front (by decide +kernel) h04
  by_cases h15 : G.Adj (f 1) (f 5)
  · exact five back (by decide +kernel) h15
  by_cases h05 : G.Adj (f 0) (f 5)
  · have table : ∀ a b, (cycleGraph 6).Adj a b → (pathGraph 6).Adj a b ∨ endpoints a b 0 5 :=
      by decide +kernel
    have forward (a b) (h : (cycleGraph 6).Adj a b) : G.Adj (f a) (f b) := by
      rcases table a b h with path | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact edges _ _ path
      · exact h05
      · exact h05.symm
    have allBlocked : ∀ a b, ¬(cycleGraph 6).Adj a b → blocked (cycleGraph 6) a b := by decide +kernel
    exact Or.inr (Or.inl ⟨induced G tri square _ f forward (fun a b h => Or.inl (allBlocked a b h))⟩)
  · have table : ∀ a b, ¬(pathGraph 6).Adj a b → blocked (pathGraph 6) a b ∨ endpoints a b 0 4 ∨
        endpoints a b 1 5 ∨ endpoints a b 0 5 := by decide +kernel
    apply Or.inr; apply Or.inr
    refine ⟨induced G tri square _ f edges ?_⟩
    intro a b h
    have avoid (i j : Fin 6) (missing : ¬ G.Adj (f i) (f j)) (eq : endpoints a b i j) :
        ¬ G.Adj (f a) (f b) := by
      rcases eq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact missing
      · exact fun adj => missing adj.symm
    rcases table a b h with done | e | e | e
    · exact Or.inl done
    · exact Or.inr (avoid _ _ h04 e)
    · exact Or.inr (avoid _ _ h15 e)
    · exact Or.inr (avoid _ _ h05 e)

theorem of_cycle {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (tri : TriangleFree G) (square : NoFourCycle G) (cyclic : ¬ G.IsAcyclic) : Pattern G := by
  classical
  unfold SimpleGraph.IsAcyclic at cyclic
  push Not at cyclic
  obtain ⟨v,p,cycle⟩ := cyclic
  have three := cycle.three_le_length
  have copy (k : ℕ) (hk : 2 < k) (length : p.length = k) : cycleGraph k ⊑ G :=
    (cycleGraph_isContained_iff hk).2 ⟨v,p,cycle,length⟩
  by_cases len3 : p.length = 3
  · obtain ⟨c⟩ := copy 3 (by decide) len3
    exact False.elim (tri (c 0) (c 1) (c 2) (c.toHom.map_adj (by decide))
      (c.toHom.map_adj (by decide)) (c.toHom.map_adj (by decide)))
  by_cases len4 : p.length = 4
  · obtain ⟨c⟩ := copy 4 (by decide) len4
    have eq := uniqueNeighbor G square (a := c 0) (b := c 2) (c := c 1) (d := c 3)
      (fun eq => (by decide : (0 : Fin 4) ≠ 2) (c.injective eq))
      (c.toHom.map_adj (by decide)) (c.toHom.map_adj (by decide))
      (c.toHom.map_adj (by decide)) (c.toHom.map_adj (by decide))
    exact False.elim ((by decide : (1 : Fin 4) ≠ 3) (c.injective eq))
  by_cases len5 : p.length = 5
  · obtain ⟨c⟩ := copy 5 (by decide) len5
    exact pentagon G tri square ⟨c,c.injective⟩ (fun _ _ adj => c.toHom.map_adj adj)
  have length : 6 ≤ p.length := by omega
  let f : Fin 6 ↪ Fin n := ⟨fun i => p.getVert i.val,fun i j eq => Fin.ext
    (cycle.getVert_injOn' (by change i.val ≤ p.length - 1; omega)
      (by change j.val ≤ p.length - 1; omega) eq)⟩
  apply pathSix G tri square f
  intro a b edge
  change G.Adj (p.getVert a.val) (p.getVert b.val)
  rcases pathGraph_adj.mp edge with step | step
  · rw [← step]
    exact p.adj_getVert_succ (by omega)
  · rw [← step]
    exact (p.adj_getVert_succ (by omega)).symm

#print axioms of_cycle
end VertexPeel.ShortCycle
