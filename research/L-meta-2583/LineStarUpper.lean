import IncidenceReadPairs
import PEqualNP.Defs

/-! A binary formula compiler and exact joint read vectors for the regular
line-star incidence circuit. Its gates are AND/OR gates with exactly two
backward-pointing operands. The formula compiler is specialized from the
L-meta-3456 research development. -/

namespace PEqualNP.Research2583.StarFormula

inductive Op where
  | meet | join
  deriving DecidableEq

def Op.apply : Op → Bool → Bool → Bool
  | .meet, a, b => a && b
  | .join, a, b => a || b

inductive Formula (α : Type) where
  | atom (x : α)
  | node (op : Op) (left right : Formula α)

namespace Formula

variable {α : Type}

def eval (z : α → Bool) : Formula α → Bool
  | .atom x => z x
  | .node op l r => op.apply (eval z l) (eval z r)

def leaves : Formula α → Nat
  | .atom _ => 1
  | .node _ l r => leaves l + leaves r

def gates : Formula α → Nat
  | .atom _ => 0
  | .node _ l r => gates l + gates r + 1

theorem leaves_eq (f : Formula α) : f.leaves = f.gates + 1 := by
  induction f with
  | atom => rfl
  | node op l r hl hr => simp [leaves, gates, hl, hr]; omega

end Formula
end PEqualNP.Research2583.StarFormula

namespace PEqualNP.Research2583.StarFormula.Formula
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

variable {n : Nat}

def opcode : Op → GateOp
  | .meet => .and
  | .join => .or


def ptr : Formula (Fin n) → Nat → Nat
  | .atom i, _ => i.val
  | .node _ a b, base => base + a.gates + b.gates

def code : Formula (Fin n) → Nat → List Gate
  | .atom _, _ => []
  | .node op a b, base =>
    a.code base ++ b.code (base + a.gates) ++
       [⟨opcode op, [a.ptr base, b.ptr (base + a.gates)]⟩]

def trace : Formula (Fin n) → List (Formula (Fin n))
  | .atom _ => []
  | .node op a b => a.trace ++ b.trace ++ [Formula.node op a b]

theorem code_length (f : Formula (Fin n)) (base : Nat) :
    (f.code base).length = f.gates := by
  induction f generalizing base with
  | atom => rfl
  | node op a b ia ib => simp [code, gates, ia, ib, Nat.add_assoc]

theorem trace_length (f : Formula (Fin n)) : f.trace.length = f.gates := by
  induction f with
  | atom => rfl
  | node op a b ia ib => simp [trace, gates, ia, ib, Nat.add_assoc]


theorem ptr_lt (f : Formula (Fin n)) (base : Nat) (h : n ≤ base) :
    f.ptr base < base + f.gates := by
  cases f with
  | atom i => simpa [ptr, gates] using lt_of_lt_of_le i.isLt h
  | node op a b => simp [ptr, gates]; omega

theorem getD_left {α} (a b : List α) (i : Nat) (d : α) (h : i < a.length) :
    (a ++ b).getD i d = a.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]


def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem step_pair (op : Op) (w : List Bool) (a b : Nat) :
    step w ⟨opcode op,[a,b]⟩ = w ++ [op.apply (w.getD a false) (w.getD b false)] := by
  cases op <;> simp [step, opcode, Op.apply, GateOp.eval]

theorem code_eval (f : Formula (Fin n)) (z : Fin n → Bool) (w : List Bool)
    (hn : n ≤ w.length) (hw : ∀ i : Fin n, w.getD i false = z i) :
    (f.code w.length).foldl step w = w ++ f.trace.map (eval z) ∧
    (w ++ f.trace.map (eval z)).getD (f.ptr w.length) false = f.eval z := by
  induction f generalizing w with
  | atom i => exact ⟨by simp [code, trace], by simpa [trace, ptr, eval] using hw i⟩
  | node op a b ia ib =>
    let u := w ++ a.trace.map (eval z)
    let v := u ++ b.trace.map (eval z)
    have hu : u.length = w.length + a.gates := by simp [u, trace_length]
    have hv : v.length = w.length + a.gates + b.gates := by simp [v, hu, trace_length]
    obtain ⟨cal, oa⟩ := ia w hn hw
    have huraw (i : Fin n) : u.getD i false = z i :=
      (getD_left _ _ _ _ (lt_of_lt_of_le i.isLt hn)).trans (hw i)
    have hnu : n ≤ u.length := by omega
    obtain ⟨cbr, ob⟩ := ib u hnu huraw
    rw [hu] at cbr ob
    change (v.getD (b.ptr (w.length + a.gates)) false) = _ at ob
    have old : v.getD (a.ptr w.length) false = a.eval z := by
      apply (getD_left u _ _ _ ?_).trans oa
      rw [hu]
      exact ptr_lt a _ hn
    constructor
    · simp only [code, List.foldl_append, List.foldl_cons, List.foldl_nil, cal]
      change step ((b.code (w.length + a.gates)).foldl step u) _ = _
      rw [cbr]
      change step v _ = _
      rw [step_pair, old, ob]
      simp [trace, v, u, eval, List.append_assoc]
    · change (w ++ (a.trace ++ b.trace ++ [Formula.node op a b]).map (eval z)).getD
          (w.length + a.gates + b.gates) false = _
      have lists : w ++ (a.trace ++ b.trace ++ [Formula.node op a b]).map (eval z) =
          v ++ [(Formula.node op a b).eval z] := by simp [v, u, List.append_assoc]
      rw [lists, ← hv]
      simp [List.getD_eq_getElem?_getD]

end PEqualNP.Research2583.StarFormula.Formula

namespace PEqualNP.Research2583.StarFormula.Formula
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

variable {n : Nat}

def Back (base : Nat) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < base + j

theorem back_append {base : Nat} {a b : List Gate} (ha : Back base a)
    (hb : Back (base + a.length) b) : Back base (a ++ b) := by
  intro j hj i hi
  by_cases h : j < a.length
  · rw [List.getElem_append_left h] at hi
    exact ha j h i hi
  · have hj' : j - a.length < b.length := by simp at hj; omega
    rw [List.getElem_append_right (by omega : a.length ≤ j)] at hi
    have := hb (j - a.length) hj' i hi
    omega

theorem code_back (f : Formula (Fin n)) (base : Nat) (hn : n ≤ base) : Back base (f.code base) := by
  induction f generalizing base with
  | atom => intro j hj; simp [code] at hj
  | node op a b ia ib =>
    apply back_append
    · apply back_append (ia _ hn)
      rw [code_length]
      exact ib _ (by omega)
    · intro j hj i hi
      simp only [List.length_cons,List.length_nil] at hj
      have h0 : j = 0 := by omega
      subst j
      simp only [List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
      simp only [List.length_append, code_length, Nat.add_zero]
      rcases hi with rfl | rfl
      · have := ptr_lt a base hn
        omega
      · have := ptr_lt b (base + a.gates) (by omega)
        omega

theorem code_mono (f : Formula (Fin n)) (base : Nat) (g : Gate) (hg : g ∈ f.code base) :
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction f generalizing base with
  | atom => simp [code] at hg
  | node op a b ia ib =>
    simp only [code, List.mem_append, List.mem_singleton] at hg
    rcases hg with (h|h)|rfl
    · exact ia _ h
    · exact ib _ h
    · cases op <;> simp [opcode]

def circuit (f : Formula (Fin n)) : Circuit := ⟨f.code n, f.ptr n⟩

theorem ofFn_lookup (z : Fin n → Bool) (i : Fin n) : (List.ofFn z).getD i false = z i := by
  simp [List.getD_eq_getElem?_getD]

theorem circuit_wires (f : Formula (Fin n)) (z : Fin n → Bool) :
    f.circuit.wires (List.ofFn z) = List.ofFn z ++ f.trace.map (eval z) := by
  have h := (code_eval f z (List.ofFn z) (by simp) (ofFn_lookup z)).1
  simp only [List.length_ofFn] at h
  exact h

theorem circuit_value (f : Formula (Fin n)) (z : Fin n → Bool) :
    circuitFun n f.circuit z = f.eval z := by
  have h := (code_eval f z (List.ofFn z) (by simp) (ofFn_lookup z)).2
  simp only [List.length_ofFn] at h
  change (f.circuit.wires (List.ofFn z)).getD (f.ptr n) false = _
  rwa [circuit_wires]


end PEqualNP.Research2583.StarFormula.Formula

namespace PEqualNP.Research2583.StarFormula.Formula

variable {α : Type}

def varList : Formula α → List α
  | .atom x => [x]
  | .node _ l r => l.varList ++ r.varList

theorem varList_length (f : Formula α) : f.varList.length = f.leaves := by
  induction f with
  | atom x => rfl
  | node op l r hl hr => simp [varList, leaves, hl, hr]

end PEqualNP.Research2583.StarFormula.Formula

namespace PEqualNP.Research2583.StarFormula.Formula

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

variable {α β : Type}

def joinMany (f : β → Formula α) : β → List β → Formula α
  | a, [] => f a
  | a, b :: bs => .node .join (f a) (joinMany f b bs)

theorem vars_joinMany (f : β → Formula α) (a : β) (bs : List β) :
    (joinMany f a bs).varList = (a :: bs).flatMap (fun b => (f b).varList) := by
  induction bs generalizing a with
  | nil => simp [joinMany]
  | cons b bs ih => simp [joinMany, varList, ih]

theorem eval_joinMany (f : β → Formula α) (z : α → Bool) (a : β) (bs : List β) :
    (joinMany f a bs).eval z = true ↔ ∃ b ∈ a :: bs, (f b).eval z = true := by
  induction bs generalizing a with
  | nil => simp [joinMany]
  | cons b bs ih =>
    simp only [joinMany, eval, Op.apply, Bool.or_eq_true, ih]
    simp

structure Star (α : Type) where
  center : α
  first : α
  more : List α

def Star.neighbors (s : Star α) := s.first :: s.more

def Star.formula (s : Star α) : Formula α :=
  .node .meet (.atom s.center) (joinMany Formula.atom s.first s.more)

def Star.variables (s : Star α) := s.center :: s.neighbors

theorem Star.vars_formula (s : Star α) : s.formula.varList = s.variables := by
  simp [Star.formula, Star.variables, Star.neighbors, varList, vars_joinMany]

theorem Star.eval_formula (s : Star α) (z : α → Bool) :
    s.formula.eval z = true ↔ z s.center = true ∧ ∃ k ∈ s.neighbors, z k = true := by
  simp [Star.formula, Star.neighbors, eval, Op.apply, eval_joinMany]

def forest (s : Star α) (ss : List (Star α)) := joinMany Star.formula s ss

theorem forest_vars (s : Star α) (ss : List (Star α)) :
    (forest s ss).varList = (s :: ss).flatMap Star.variables := by
  simp [forest, vars_joinMany, Star.vars_formula]

theorem forest_eval (s : Star α) (ss : List (Star α)) (z : α → Bool) :
    (forest s ss).eval z = true ↔
      ∃ t ∈ s :: ss, z t.center = true ∧ ∃ k ∈ t.neighbors, z k = true := by
  simp only [forest, eval_joinMany, Star.eval_formula]

def Endpoints {N : Nat} (u v : Fin (N+N)) (p l : Fin N) : Prop :=
  (u = Fin.castAdd N p ∧ v = Fin.natAdd N l) ∨ (v = Fin.castAdd N p ∧ u = Fin.natAdd N l)

/-- Each listed spoke is a graph edge and each edge is one of the listed spokes.
    A center may be on either side of the bipartition. -/
structure Presents {N : Nat} (ss : List (Star (Fin (N+N)))) (I : Fin N → Fin N → Prop) : Prop where
  sound : ∀ t ∈ ss, ∀ k ∈ t.neighbors, ∃ p l, I p l ∧ Endpoints t.center k p l
  complete : ∀ p l, I p l → ∃ t ∈ ss, ∃ k ∈ t.neighbors, Endpoints t.center k p l

theorem forest_incidence {N : Nat} {s : Star (Fin (N+N))} {ss : List (Star (Fin (N+N)))}
    {I : Fin N → Fin N → Prop} (pres : Presents (s::ss) I) (z : Fin (N+N) → Bool) :
    (forest s ss).eval z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
  rw [forest_eval]
  constructor
  · rintro ⟨t, ht, hu, k, hk, hv⟩
    obtain ⟨p,l,hi,pair⟩ := pres.sound t ht k hk
    refine ⟨p,l,hi,?_⟩
    rcases pair with ⟨hp,hl⟩ | ⟨hp,hl⟩
    · exact ⟨hp ▸ hu,hl ▸ hv⟩
    · exact ⟨hp ▸ hv,hl ▸ hu⟩
  · rintro ⟨p,l,hi,hp,hl⟩
    obtain ⟨t,ht,k,hk,pair⟩ := pres.complete p l hi
    rcases pair with ⟨ep,el⟩ | ⟨ep,el⟩
    · exact ⟨t,ht,ep.symm ▸ hp,k,hk,el.symm ▸ hl⟩
    · exact ⟨t,ht,el.symm ▸ hl,k,hk,ep.symm ▸ hp⟩

end PEqualNP.Research2583.StarFormula.Formula

namespace PEqualNP.Research2583.LineStars
open PEqualNP.Research2583.StarFormula PEqualNP.Research2583.StarFormula.Formula
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

abbrev Vectors := List (List Nat)

def mergeVectors (S : List Nat) (op : Op) (a b : Vectors) : Vectors :=
  match op with
  | .join => [a,b].foldl (fun acc B => B.foldl insertNew acc) []
  | .meet => [a,b].foldl (andStep 1) [S.map fun _ => 0]

def vectors {n : Nat} (S : List Nat) (z : Fin n → Vectors) : Formula (Fin n) → Vectors
  | .atom i => z i
  | .node op a b => mergeVectors S op (vectors S z a) (vectors S z b)

def vectorStep (S : List Nat) (R : List Vectors) (g : Gate) :=
  let ins := g.inputs.map fun i => R.getD i []
  R ++ [match g.op with
    | .or => ins.foldl (fun acc A => A.foldl insertNew acc) []
    | .and => ins.foldl (andStep 1) [S.map fun _ => 0]
    | _ => []]

lemma vectorStep_pair (S : List Nat) (op : Op) (w : List Vectors) (a b : Nat) :
    vectorStep S w ⟨opcode op,[a,b]⟩ = w ++ [mergeVectors S op (w.getD a []) (w.getD b [])] := by
  cases op <;> rfl

theorem code_vectors {n : Nat} (S : List Nat) (f : Formula (Fin n)) (z : Fin n → Vectors) (w : List Vectors)
    (hn : n ≤ w.length) (hw : ∀ i : Fin n, w.getD i [] = z i) :
    (f.code w.length).foldl (vectorStep S) w = w ++ f.trace.map (vectors S z) ∧
    (w ++ f.trace.map (vectors S z)).getD (f.ptr w.length) [] = vectors S z f := by
  induction f generalizing w with
  | atom i => exact ⟨by simp [Formula.code, trace], by simpa [trace, ptr, vectors] using hw i⟩
  | node op a b ia ib =>
    let u := w ++ a.trace.map (vectors S z)
    let v := u ++ b.trace.map (vectors S z)
    have hu : u.length = w.length + a.gates := by simp [u, trace_length]
    have hv : v.length = w.length + a.gates + b.gates := by simp [v, hu, trace_length]
    obtain ⟨cal, oa⟩ := ia w hn hw
    have huraw (i : Fin n) : u.getD i [] = z i :=
      (getD_left _ _ _ _ (lt_of_lt_of_le i.isLt hn)).trans (hw i)
    have hnu : n ≤ u.length := by omega
    obtain ⟨cbr, ob⟩ := ib u hnu huraw
    rw [hu] at cbr ob
    change (v.getD (b.ptr (w.length + a.gates)) []) = _ at ob
    have old : v.getD (a.ptr w.length) [] = vectors S z a := by
      apply (getD_left u _ _ _ ?_).trans oa
      rw [hu]
      exact ptr_lt a _ hn
    constructor
    · simp only [Formula.code, List.foldl_append, List.foldl_cons, List.foldl_nil, cal]
      change vectorStep S ((b.code (w.length + a.gates)).foldl (vectorStep S) u) _ = _
      rw [cbr]
      change vectorStep S v _ = _
      rw [vectorStep_pair, old, ob]
      simp [trace, v, u, vectors, List.append_assoc]
    · change (w ++ (a.trace ++ b.trace ++ [Formula.node op a b]).map (vectors S z)).getD
          (w.length + a.gates + b.gates) [] = _
      have lists : w ++ (a.trace ++ b.trace ++ [Formula.node op a b]).map (vectors S z) =
          v ++ [vectors S z (Formula.node op a b)] := by simp [v, u, List.append_assoc]
      rw [lists, ← hv]
      simp [List.getD_eq_getElem?_getD]

lemma compiler_reads {n} (S : List Nat) (f : Formula (Fin n)) :
    (readVectors f.circuit n S 1).getD f.circuit.output [] =
      vectors S (fun i : Fin n => leafVectors S 1 i.val) f := by
  let w := (List.range n).map (leafVectors S 1)
  have len : w.length = n := by simp [w]
  have atRaw (i : Fin n) : w.getD i.val [] = leafVectors S 1 i.val := by
    simp [w, List.getD_eq_getElem?_getD, i.isLt]
  obtain ⟨h, out⟩ := code_vectors S f _ w len.ge atRaw
  rw [len] at h out
  change ((f.code n).foldl (vectorStep S) w).getD (f.ptr n) [] = _
  rw [h]; exact out

lemma mem_insert_rows {v w : List Nat} {A : Vectors} : v ∈ insertNew A w ↔ v ∈ A ∨ v = w := by
  by_cases h : w ∈ A
  · simp [insertNew,h]; exact fun e => e ▸ h
  · simp [insertNew,h]

lemma mem_union (v : List Nat) (A B : Vectors) : v ∈ B.foldl insertNew A ↔ v ∈ A ∨ v ∈ B := by
  induction B generalizing A with
  | nil => simp
  | cons w B ih => simp only [List.foldl_cons,ih,mem_insert_rows,List.mem_cons]; tauto

lemma mem_and {a b : List Nat} {A B : Vectors} (ha : a ∈ A) (hb : b ∈ B) :
    capAdd 1 a b ∈ andStep 1 A B := by
  apply (mem_union _ _ _).2
  right
  exact List.mem_flatMap.mpr ⟨a,ha,List.mem_map.mpr ⟨b,hb,rfl⟩⟩

lemma mem_join {S} (v : List Nat) (A B : Vectors) : v ∈ mergeVectors S .join A B ↔ v ∈ A ∨ v ∈ B := by
  simp [mergeVectors,mem_union]

lemma mem_joinMany {n} {α : Type} (S : List Nat) (z : Fin n → Vectors) (f : α → Formula (Fin n))
    (a : α) (bs : List α) (v : List Nat) :
    v ∈ vectors S z (joinMany f a bs) ↔ ∃ b ∈ a :: bs, v ∈ vectors S z (f b) := by
  induction bs generalizing a with
  | nil => simp [joinMany]
  | cons b bs ih => simp [joinMany,vectors,mem_join,ih]

lemma joint_witness {n} {s : Formula.Star (Fin n)} {ss : List (Formula.Star (Fin n))} (t : Formula.Star (Fin n))
    (ht : t ∈ s :: ss) (p l : Fin n) (diff : p ≠ l) (center : t.center = l) (near : p ∈ t.neighbors) :
    readsAtMost (forest s ss).circuit n [p.val,l.val] 1 = true := by
  let S := [p.val,l.val]
  let z := fun i : Fin n => leafVectors S 1 i.val
  have neq : p.val ≠ l.val := fun h => diff (Fin.ext h)
  have hp : [1,0] ∈ z p := by simp [z,S,leafVectors,neq,Ne.symm neq]
  have hl : [0,1] ∈ z t.center := by simp [center,z,S,leafVectors,neq,Ne.symm neq]
  have leaf : [1,0] ∈ vectors S z (joinMany Formula.atom t.first t.more) :=
    (mem_joinMany S z Formula.atom t.first t.more [1,0]).2 ⟨p,near,hp⟩
  have one : [1,1] ∈ vectors S z t.formula := by
    change _ ∈ andStep 1 (andStep 1 [[0,0]] (z t.center)) _
    exact mem_and (mem_and (List.mem_singleton_self _) hl) leaf
  have out := (mem_joinMany S z Formula.Star.formula s ss [1,1]).2 ⟨t,ht,one⟩
  unfold readsAtMost
  rw [compiler_reads]
  exact List.any_eq_true.mpr ⟨[1,1],out,by decide⟩

end PEqualNP.Research2583.LineStars

namespace PEqualNP.Research2583.LineStars
open PEqualNP.Research2583.StarFormula PEqualNP.Research2583.StarFormula.Formula
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.ReadK PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma code_arity {n} (f : Formula (Fin n)) (base : Nat) (g : Gate) (hg : g ∈ f.code base) :
    g.inputs.length = 2 := by
  induction f generalizing base with
  | atom => simp [Formula.code] at hg
  | node op a b ia ib =>
    simp only [Formula.code,List.mem_append,List.mem_singleton] at hg
    rcases hg with (h|h)|rfl
    · exact ia _ h
    · exact ib _ h
    · rfl

lemma compiler_AO2 {n} (f : Formula (Fin n)) : IsAO2 n f.circuit := by
  refine ⟨fun g hg => (code_mono f n g hg).1, ?_, fun g hg => code_arity f n g hg⟩
  intro j hj i hi
  have hj' : j < (f.code n).length := hj
  apply code_back f n le_rfl j hj' i
  simpa [gateAt, circuit, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'] using hi

lemma uniform_length {α β : Type} (xs : List α) (f : α → List β) (k : Nat)
    (hf : ∀ x ∈ xs, (f x).length = k) : (xs.flatMap f).length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have len := hf x (by simp)
    have tail := ih (fun b hb => hf b (by simp [hb]))
    simp [len,tail,Nat.succ_mul,Nat.add_comm]

lemma cons_head_tail {α : Type} (xs : List α) (h : xs ≠ []) : xs.head h :: xs.tail = xs := by
  cases xs with
  | nil => contradiction
  | cons a xs => rfl

/-- Every nonempty regular family of lines has a star circuit, with a joint
  two-variable witness at each incident pair. Neither point regularity nor
  uniqueness of the line joining two points is required. -/
theorem regular_stars (N q : Nat) (I : Fin N → Fin N → Prop) [DecidableRel I] (hn : 0 < N)
    (degree : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    ∃ D : Circuit, IsAO2 (N+N) D ∧
      (∀ z : Fin (N+N) → Bool, circuitFun (N+N) D z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) ∧
      D.size + 1 = N * (q+2) ∧ ∀ p l : Fin N, I p l →
        readsAtMost D (N+N) [p.val,N+l.val] 1 = true := by
  let ns (l : Fin N) : List (Fin (N+N)) :=
    (Finset.univ.filter (fun p => I p l)).toList.map (Fin.castAdd N)
  have count (l : Fin N) : (ns l).length = q + 1 := by simp [ns,degree l]
  have member (p l : Fin N) (h : I p l) : Fin.castAdd N p ∈ ns l := by
    apply List.mem_map.mpr; exact ⟨p, by simpa using h, rfl⟩
  have nonempty (l : Fin N) : ns l ≠ [] := by
    intro bad; have h := count l; rw [bad] at h; simp at h
  let star (l : Fin N) : Formula.Star (Fin (N+N)) :=
    ⟨Fin.natAdd N l, (ns l).head (nonempty l), (ns l).tail⟩
  have spokes (l : Fin N) : (star l).neighbors = ns l := by
    change (ns l).head _ :: (ns l).tail = ns l
    exact cons_head_tail _ _
  let allLines := (List.finRange N).map star
  have nlines : allLines.length = N := by simp [allLines]
  have nn : allLines ≠ [] := by intro bad; rw [bad] at nlines; simp at nlines; omega
  let s := allLines.head nn
  let ss := allLines.tail
  have splitLines : s :: ss = allLines := by
    change allLines.head nn :: allLines.tail = allLines
    exact cons_head_tail _ _
  have allMembers (l : Fin N) : star l ∈ s :: ss := by
    rw [splitLines]; apply List.mem_map.mpr; exact ⟨l,by simp,rfl⟩
  have cover : Presents (s :: ss) I := by
    constructor
    · intro t ht k hk
      rw [splitLines] at ht
      obtain ⟨l,_,rfl⟩ := List.mem_map.mp ht
      rw [spokes] at hk
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hk
      exact ⟨p,l,by simpa using hp,Or.inr ⟨rfl,rfl⟩⟩
    · intro p l ip
      exact ⟨star l,allMembers l,Fin.castAdd N p,spokes l ▸ member p l ip,Or.inr ⟨rfl,rfl⟩⟩
  let f := forest s ss
  refine ⟨f.circuit, compiler_AO2 f, ?_, ?_, ?_⟩
  · intro z
    rw [circuit_value]
    exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using forest_incidence cover z)
  · have uniform (t : Formula.Star (Fin (N+N))) (ht : t ∈ allLines) : t.variables.length = q+2 := by
      obtain ⟨l,_,rfl⟩ := List.mem_map.mp ht
      simp [Formula.Star.variables,spokes,count]
    have total := uniform_length allLines Formula.Star.variables (q+2) uniform
    change (f.code (N+N)).length + 1 = _
    rw [code_length, ← leaves_eq, ← varList_length, forest_vars,splitLines,total,nlines]
  · intro p l ip
    have different : Fin.castAdd N p ≠ Fin.natAdd N l := by
      intro eq; have h := congrArg Fin.val eq
      change p.val = N + l.val at h
      omega
    exact joint_witness (star l) (allMembers l) (Fin.castAdd N p) (Fin.natAdd N l)
      different rfl (spokes l ▸ member p l ip)

end PEqualNP.Research2583.LineStars

namespace PEqualNP.Research2583.LineStars
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK PEqualNP.TopForm

/-- A regular incidence structure admits a read-1 circuit of the exact line-star cost. -/
theorem regular_read_upper (N q : Nat) (I : Fin N → Fin N → Prop) [DecidableRel I] (hn : 0 < N)
    (degree : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    ∃ D : Circuit, IsAO2 (N+N) D ∧
      (∀ z : Fin (N+N) → Bool, circuitFun (N+N) D z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) ∧
      D.size + 1 = N * (q+2) ∧ IsReadK (N+N) D 1 := by
  obtain ⟨D,ao,sem,sz,pairs⟩ := regular_stars N q I hn degree
  exact ⟨D,ao,sem,sz,(PEqualNP.Research2583.read_iff_pairs I D sem 1).2 pairs⟩

#print axioms regular_read_upper
end PEqualNP.Research2583.LineStars
