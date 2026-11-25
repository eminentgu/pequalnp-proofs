import SidePeel
import RowGraph

namespace VertexPeel.LocalReaders
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.Core
open VertexPeel.ZeroFold VertexPeel.RowGraph VertexPeel.SideReaders VertexPeel.SidePeel
variable {n : ℕ}

/-- Some gate reading a changed raw input must itself change, even when a
different reader of that input is insensitive on the two chosen rows. -/
theorem changed_reader (C : Circuit) (ao : IsAO2 n C) (x y : Fin n → Bool)
    (S : Finset (Fin n)) (same : ∀ v ∉ S, x v=y v)
    (diff : wval C x C.output ≠ wval C y C.output) (out : ∀ v∈S, C.output ≠ v.val) :
    ∃ (k : ℕ) (hk : k<C.gates.length), (∃ a∈S, a.val ∈ C.gates[k].inputs) ∧
      wval C x (n+k) ≠ wval C y (n+k) := by
  classical
  by_contra! never
  have eqn (w : ℕ) : (∀ v∈S,w≠v.val) → wval C x w=wval C y w := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro ex
      by_cases raw : w<n
      · let i : Fin n := ⟨w,raw⟩
        exact (wval_in C x i).trans ((same i (fun h => ex i h rfl)).trans (wval_in C y i).symm)
      by_cases far : n+C.gates.length ≤ w
      · rw [wval_past _ _ _ far,wval_past _ _ _ far]
      obtain ⟨j,rfl⟩ : ∃ j,w=n+j := ⟨w-n,by omega⟩
      have hj : j<C.gates.length := by omega
      obtain ⟨a,b,ports,ha,hb,_⟩ := two n C ao j hj
      by_cases hit : ∃ v∈S,v.val ∈ C.gates[j].inputs
      · exact never j hj hit
      have side (t) (mem : t∈C.gates[j].inputs) : ∀ v∈S,t≠v.val :=
        fun v hv e => hit ⟨v,hv,e ▸ mem⟩
      rw [wval_gate _ x _ _ _ hj ports ha hb,wval_gate _ y _ _ _ hj ports ha hb,
        ih a ha (side a (by simp [ports])),ih b hb (side b (by simp [ports]))]
  exact diff (eqn _ out)

theorem prefix_agree (C : Circuit) (ao : IsAO2 n C) (B : Finset ℕ) (r : ℕ)
    (skip : ∀ k (hk : k<C.gates.length), k<r → ∀ t∈C.gates[k].inputs,t∉B)
    (x y : Fin n → Bool) (same : ∀ i : Fin n, i.val∉B → x i=y i) (w : ℕ) :
    w<n+r → w∉B → wval C x w=wval C y w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro early outside
    by_cases raw : w<n
    · let i : Fin n := ⟨w,raw⟩
      exact (wval_in C x i).trans ((same i outside).trans (wval_in C y i).symm)
    by_cases far : n+C.gates.length ≤ w
    · rw [wval_past _ _ _ far,wval_past _ _ _ far]
    obtain ⟨k,rfl⟩ : ∃ k,w=n+k := ⟨w-n,by omega⟩
    have hk : k<C.gates.length := by omega
    obtain ⟨a,b,ports,ha,hb,_⟩ := two n C ao k hk
    have avoid := skip k hk (by omega)
    rw [wval_gate _ x _ _ _ hk ports ha hb,wval_gate _ y _ _ _ hk ports ha hb,
      ih a ha (by omega) (avoid a (by simp [ports])),ih b hb (by omega) (avoid b (by simp [ports]))]

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

/-- Only the outside neighbors of the chosen side must see that side exclusively.
Other components can contain arbitrary edges. -/
def LocalSide (B : Finset ℕ) : Prop := ∀ a : Fin n, a.val∈B →
  ∃ t : Fin n, t.val∉B ∧ G.Adj t a ∧ ∀ v, G.Adj t v → v.val∈B

/-- Forbids a sound child below an OR which can light on an independent set. -/
def OrClosed : Prop := ∀ j (hj : j<C.gates.length), C.gates[j].op=.or →
  ∀ d∈C.gates[j].inputs, (∀ x : Fin n → Bool,wval C x d=true → graphFun G ∅ x=true) →
    ∀ x : Fin n → Bool,wval C x (n+j)=true → graphFun G ∅ x=true

private theorem first_local (B : Finset ℕ) (bounded : ∀ t∈B,t<n) (localB : LocalSide G B)
    (sq : NoFourCycle G) (ao : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅)
    (normal : OrClosed G C) (a : Fin n) (aB : a.val∈B) (high : 2≤G.degree a)
    (r : ℕ) (hr : r<C.gates.length) (d : ℕ) (ports : C.gates[r].inputs=[a.val,d] ∨ C.gates[r].inputs=[d,a.val])
    (hop : C.gates[r].op=.or) (distinct : d≠a.val) (back : d<n+r)
    (skip : ∀ k (hk : k<C.gates.length), k<r → ∀ t∈C.gates[k].inputs,t∉B) :
    ∃ b : Fin n, b.val∈B ∧ b.val∈C.gates[r].inputs ∧
      ∃ (k : ℕ) (hk : k<C.gates.length), k≠r ∧ b.val∈C.gates[k].inputs := by
  classical
  have act (x : Fin n → Bool) (h : x a=true ∨ wval C x d=true) : wval C x (n+r)=true := by
    rcases ports with p|p
    · rw [wval_or C x r a.val d hr p (by omega) back hop,wval_in C x a,Bool.or_eq_true]; exact h
    · rw [wval_or C x r d a.val hr p back (by omega) hop,wval_in C x a,Bool.or_eq_true]; exact h.symm
  have readA : a.val∈C.gates[r].inputs := by rcases ports with p|p <;> simp [p]
  have readD : d∈C.gates[r].inputs := by rcases ports with p|p <;> simp [p]
  by_cases dB : d∈B
  · let b : Fin n := ⟨d,bounded d dB⟩
    have ab : a ≠ b := fun e => distinct (congrArg Fin.val e).symm
    obtain ⟨u,ua,ub⟩ := separated_neighbor G sq ab high
    let x := bits {u,a}
    let y := bits {u,b}
    have diff : wval C x C.output ≠ wval C y C.output := by
      change circuitFun n C x ≠ circuitFun n C y
      rw [ok]
      exact fun eq => ub ((pair_iff G u b).mp (eq.symm.trans ((pair_iff G u a).mpr ua)))
    have rx := act x (Or.inl (by simp [x,bits]))
    have ry := act y (Or.inr ((wval_in C y b).trans (by simp [y,bits])))
    obtain ⟨k,hk,⟨v,hv,read⟩,ne⟩ := changed_reader C ao x y {a,b}
      (by intro i hi; simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi; simp [x,y,bits,hi.1,hi.2]) diff (fun v _ => no_raw_output G ok v)
    have kr : k≠r := fun e => ne (e ▸ rx.trans ry.symm)
    rcases (show v=a ∨ v=b by simpa using hv) with rfl|rfl
    · exact ⟨_,aB,readA,k,hk,kr,read⟩
    · exact ⟨_,dB,readD,k,hk,kr,read⟩
  · have unsound : ¬∀ x : Fin n → Bool,wval C x d=true → graphFun G ∅ x=true := by
      intro safe
      have on := normal r hr hop d readD safe (bits {a,a}) (act _ (Or.inl (by simp [bits])))
      exact (G.loopless.irrefl _) ((pair_iff G a a).mp on)
    push Not at unsound
    obtain ⟨I,di,neg⟩ := unsound
    obtain ⟨t,tB,ta,neighbors⟩ := localB a aB
    let J (v : Fin n) := if v.val∈B then false else I v
    let x (v : Fin n) := decide (v=t) || J v
    let y := Function.update x a true
    have jd : wval C J d=true := (prefix_agree C ao B r skip I J (by intro i hi; simp [J,hi]) d back dB).symm.trans di
    have xd : wval C x d=true := wire_mono C ao (by intro i hi; simp [x,hi]) d jd
    have rx := act x (Or.inr xd)
    have ry := act y (Or.inl (by simp [y]))
    have noEdge : ¬ ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true := by
      rintro ⟨u,v,uv,hu,hv⟩
      have selected (w) (hw : x w=true) : w=t ∨ w.val∉B ∧ I w=true := by
        by_cases mem : w.val ∈ B <;> simpa [x,J,mem] using hw
      rcases selected u hu with eu|iu
      · rcases selected v hv with ev|iv
        · exact uv.ne (eu.trans ev.symm)
        · exact iv.1 (neighbors v (eu ▸ uv))
      · rcases selected v hv with ev|iv
        · exact iu.1 (neighbors u (ev ▸ uv.symm))
        · have old : graphFun G ∅ I=true := by simp [graphFun]; exact ⟨u,v,uv,iu.2,iv.2⟩
          simp_all
    have diff : wval C x C.output ≠ wval C y C.output := by
      change circuitFun n C x ≠ circuitFun n C y
      rw [ok]
      have pos : graphFun G ∅ y=true := by
        simp [graphFun]
        exact ⟨t,a,ta,by simp [y,Function.update_of_ne ta.ne,x],by simp [y]⟩
      have negX : graphFun G ∅ x=false := by simp [graphFun,noEdge]
      rw [negX,pos]; decide
    obtain ⟨k,hk,⟨v,hv,read⟩,ne⟩ := changed_reader C ao x y {a}
      (by
        intro i hi
        have e : i≠a := by simpa using hi
        simp [y,e]) diff (fun v _ => no_raw_output G ok v)
    exact ⟨a,aB,readA,k,hk,fun e => ne (e ▸ rx.trans ry.symm),(Finset.mem_singleton.mp hv) ▸ read⟩

/-- In a circuit with no mixed OR, zeroing at least one candidate eliminates two gates,
including in the presence of other components that may share gates with this one. -/
theorem localized_two (B : Finset ℕ) (bounded : ∀ t∈B,t<n) (someB : B.Nonempty)
    (localB : LocalSide G B) (square : NoFourCycle G)
    (high : ∀ a : Fin n,a.val∈B → 2≤G.degree a)
    (stable : ∀ a : Fin n,a.val∈B → ¬Drops G a) (ao : IsAO2 n C)
    (ok : circuitFun n C = graphFun G ∅) (normal : OrClosed G C) :
    ∃ a : Fin n, a.val ∈ B ∧ ∃ j < C.size, ∃ k < C.size, k≠j ∧ ¬Mg C {a} j ∧ ¬Mg C {a} k := by
  classical
  let hits j := ∃ hj : j<C.gates.length, ∃ t∈B,t∈C.gates[j].inputs
  have someHit : ∃ j, hits j := by
    obtain ⟨v,hv⟩ := someB
    let a : Fin n := ⟨v,bounded v hv⟩
    obtain ⟨u,_,edge,_⟩ := localB a hv
    obtain ⟨x,y,eq,diff⟩ := sensitive G C ok edge
    obtain ⟨k,hk,⟨t,ht,read⟩,_⟩ := changed_reader C ao x y {a}
      (by intro i hi; exact eq i (by simpa using hi)) diff (fun v _ => no_raw_output G ok v)
    exact ⟨k,hk,t.val,(Finset.mem_singleton.mp ht) ▸ hv,read⟩
  let r := Nat.find someHit
  obtain ⟨hr,z,zB,reader⟩ := Nat.find_spec someHit
  change z∈C.gates[r].inputs at reader
  let a : Fin n := ⟨z,bounded z zB⟩
  have zeroA := fv_in0 C {a} a (by simp)
  have killed := kill C ao {a} r hr z reader zeroA
  obtain ⟨l,t,ins,hl,ht,op⟩ := two n C ao r hr
  have pick : z=l ∨ z=t := by simpa [ins] using reader
  by_cases zero : fv C {a} (n+r) = fun _ => false
  · obtain ⟨u,_,edge,_⟩ := localB a zB
    have left := remaining_of_stable G a ⟨u,a,edge⟩ (stable a zB)
    obtain ⟨k,hk,ne,drop⟩ := second_of_zero G C ao ok a u edge left r hr zero
    exact ⟨a,zB,r,hr,k,hk,ne,killed,drop⟩
  have isOr : C.gates[r].op=.or := op.resolve_left (by
    intro isAnd
    apply zero
    funext x
    rw [fv_and C {a} r l t hr ins hl ht isAnd]
    rcases pick with h|h
    · rw [←h]; change (fv C {a} a.val x && _)=_; rw [zeroA]; rfl
    · rw [←h]; change (_ && fv C {a} a.val x)=_; rw [zeroA,Bool.and_false])
  have ltNe : l≠t := by
    intro h
    have eq : l=z := by rcases pick with p|p <;> omega
    apply zero
    funext x
    rw [fv_or C {a} r l t hr ins hl ht isOr,←h,eq]
    change (fv C {a} a.val x || _) = _
    rw [zeroA]; rfl
  obtain ⟨d,ordered,distinct,early⟩ : ∃ d,(C.gates[r].inputs=[a.val,d] ∨ C.gates[r].inputs=[d,a.val]) ∧ d≠a.val ∧ d<n+r := by
    change ∃ d,(C.gates[r].inputs=[z,d] ∨ C.gates[r].inputs=[d,z]) ∧ d≠z ∧ d<n+r
    rcases pick with h|h
    · exact ⟨t,Or.inl (h ▸ ins),by omega,ht⟩
    · exact ⟨l,Or.inr (h ▸ ins),by omega,hl⟩
  have skip (k) (hk : k<C.gates.length) (kr : k<r) (v) (read : v ∈ C.gates[k].inputs) : v∉B :=
    fun h => Nat.find_min someHit kr ⟨hk,v,h,read⟩
  obtain ⟨b,hb,rb,k,hk,ne,kb⟩ := first_local G C B bounded localB square ao ok normal a zB
    (high a zB) r hr d ordered isOr distinct early skip
  have raw := fv_in0 C {b} b (by simp)
  exact ⟨b,hb,r,hr,k,hk,ne,kill C ao _ r hr b.val rb raw,kill C ao _ k hk b.val kb raw⟩
#print axioms localized_two
end VertexPeel.LocalReaders
