import CriticalCases

namespace PEqualNP.Research.GatePinning

open CircuitLowerBounds EdgeOwnership MetaComplexity MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_5465 (val val_gate val_ofFn)

abbrev RepairsAt {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : Nat) :=
  ∃ D : Circuit, Eligible G D ∧ D.size = C.size ∧ (∀ j < k, BadAt G D j → BadAt G C j) ∧ ¬BadAt G D k

def primaryOr {n} (C : Circuit) (k : Nat) (u v : Fin n) :=
  replace C k ⟨.or, [u.val,v.val]⟩

theorem primaryOr_value {n} {C : Circuit} {k : Nat} (u v : Fin n) (inside : k < C.size) (x : Fin n → Bool) :
    gateVal n (primaryOr C k u v) k x = (x u || x v) := by
  change val (primaryOr C k u v) (List.ofFn x) (n+k) = _
  rw [val_gate (n := n) (by simp) (by simpa [primaryOr,Circuit.size] using inside),
    show gateAt (primaryOr C k u v) k = _ from replace_at inside]
  simp [GateOp.eval,val_ofFn,show u.val < n+k by omega,show v.val < n+k by omega]

/-- Every critical edge meets a pair of primary inputs that individually activate the gate. -/
theorem repair_of_two_forcing_vertices {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hC : Eligible G C) {k : Nat} (inside : k < C.size)
    (hand : (gateAt C k).op = .and) (u v : Fin n)
    (forceU : ∀ x, x u = true → gateVal n C k x = true)
    (forceV : ∀ x, x v = true → gateVal n C k x = true)
    (cover : ∀ a b, needed G C k a b → a=u ∨ b=u ∨ a=v ∨ b=v) :
    RepairsAt G C k := by
  let D := primaryOr C k u v
  have legal : Monotone2 D := replace_mono hC.1.1 (by simp) (by simp)
  have size : D.size = C.size := replace_length ..
  have site : gateAt D k = ⟨.or,[u.val,v.val]⟩ := replace_at inside
  have below (x : Fin n → Bool) : gateVal n D k x = true → gateVal n C k x = true := by
    rw [primaryOr_value u v inside, Bool.or_eq_true]
    rintro (w | w)
    · exact forceU x w
    · exact forceV x w
  have eq : circuitFun n D = graphFun G ∅ := by
    apply subgate_correct G inside hC.1.1 hC.2.1 _ legal below
    intro a b hit
    change gateVal n (primaryOr C k u v) k (pairInput a b) = true
    rw [primaryOr_value u v inside]
    rcases cover a b hit with rfl | rfl | rfl | rfl <;> simp [pairInput]
  have minimal : IsMinimalMonoCircuit n D :=
    ⟨legal,fun E m f => size ▸ hC.1.2 E m (f.trans (eq.trans hC.2.1.symm))⟩
  have productive : Productive G D := by
    intro j hj op
    by_cases target : j = k
    · subst j; rw [site] at op; cases op
    · have op0 : (gateAt C j).op = .and := (congrArg Gate.op
          (show gateAt D j = gateAt C j from replace_elsewhere target)).symm.trans op
      obtain ⟨a,b,edge,owned⟩ := hC.2.2 j (size ▸ hj) op0
      refine ⟨a,b,edge,other_owners_survive hC.1.1 hand ?_ below target owned⟩
      intro w h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl | rfl
      · exact Or.inl u.isLt
      · exact Or.inl v.isLt
  refine ⟨D,⟨minimal,eq,productive⟩,size,?_,?_⟩
  · rintro j hj ⟨a,b,c,d,ab,cd,i,j,more⟩
    exact ⟨a,b,c,d,ab,cd,before_new_to_old hC.1.1 hj i,before_new_to_old hC.1.1 hj j,more⟩
  · rintro ⟨a,b,c,d,_,_,owned,_⟩
    have op := owned.2.1
    rw [site] at op
    cases op

def ForcesWire {n} (C : Circuit) (w : Nat) (u : Fin n) :=
  ∀ x : Fin n → Bool, x u = true → val C (List.ofFn x) w = true

private theorem and_value {n} {C : Circuit} {k s t : Nat} (inside : k < C.size)
    (site : gateAt C k = ⟨.and,[s,t]⟩) (hs : s < n+k) (ht : t < n+k) (x : Fin n → Bool) :
    gateVal n C k x = (val C (List.ofFn x) s && val C (List.ofFn x) t) := by
  change val C (List.ofFn x) (n+k) = _
  rw [val_gate (n := n) (by simp) inside, site]
  simp [GateOp.eval,hs,ht]

/-- An active operand of a gate owning a pair can be turned on by one endpoint alone. -/
theorem owned_operand_forces {n} {C : Circuit} {k w : Nat} {a b : Fin n}
    (legal : Monotone2 C) (owned : Owns n C k a b) (before : w < n+k)
    (input : w ∈ (gateAt C k).inputs) (on : val C (List.ofFn (pairInput a b)) w = true) :
    ForcesWire C w a ∨ ForcesWire C w b := by
  let e := pairInput a b
  have pre (x : Fin n → Bool) : val C (List.ofFn x) w =
      (Outside.L_meta_4846.wf (C.gates.take k) (List.ofFn x)).getD w false :=
    Outside.L_meta_4846.wire_take _ _ _ _ (by simpa using before) owned.1.le
  obtain ⟨p,hp,force⟩ := Outside.L_meta_4846.wire_reach n C legal e k owned.1
    (fun j hj => Outside.L_meta_4846.or_reach n C legal e j (hj.trans owned.1))
    (fun i path op => owned.2.2.2 i (Outside.L_meta_4846.cone_idx n C.gates k i path) path op)
    w (by rwa [← Outside.L_meta_4846.gateAt_eq C k owned.1]) ((pre e).symm.trans on)
  have force' : ForcesWire C w p := fun x hx => (pre x).trans (force x hx)
  have h : p=a ∨ p=b := by simpa [e,pairInput] using hp
  rcases h with rfl | rfl
  · exact Or.inl force'
  · exact Or.inr force'

/-- A binary AND can always be repaired when the critical edges lie in a two-edge
star and it owns both spokes. No common operand forced by the centre is assumed. -/
theorem repair_of_two_owned_spokes {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hC : Eligible G C) {k s t : Nat} (inside : k < C.size)
    (site : gateAt C k = ⟨.and,[s,t]⟩) (hs : s < n+k) (ht : t < n+k)
    (z u v : Fin n) (edge : G.Adj z u) (ownU : Owns n C k z u) (ownV : Owns n C k z v)
    (cover : ∀ a b, needed G C k a b →
      (a=z ∨ b=z) ∧ (a=u ∨ b=u ∨ a=v ∨ b=v)) : RepairsAt G C k := by
  have star := fun a b h => (cover a b h).1
  by_cases left : ForcesWire C s z
  · exact repair_of_star_pin G hC inside
      ⟨s,t,z,Or.inl site,hs,ht,left,star,z,u,edge,ownU,Or.inl rfl⟩
  by_cases right : ForcesWire C t z
  · exact repair_of_star_pin G hC inside
      ⟨t,s,z,Or.inr site,ht,hs,right,star,z,u,edge,ownU,Or.inl rfl⟩
  have leaf (a : Fin n) (own : Owns n C k z a) (x : Fin n → Bool) (hx : x a = true) :
      gateVal n C k x = true := by
    have both := own.2.2.1
    rw [and_value inside site hs ht, Bool.and_eq_true] at both
    have l := (owned_operand_forces hC.1.1 own hs (by simp [site]) both.1).resolve_left left
    have r := (owned_operand_forces hC.1.1 own ht (by simp [site]) both.2).resolve_left right
    rw [and_value inside site hs ht, Bool.and_eq_true]
    exact ⟨l x hx,r x hx⟩
  exact repair_of_two_forcing_vertices G hC inside (by simp [site]) u v
    (leaf u ownU) (leaf v ownV) (fun a b h => (cover a b h).2)

/-- The two-spoke hypothesis packages a finite description of the critical pairs. -/
def TwoOwnedSpokes {n} (G : SimpleGraph (Fin n)) (C : Circuit) (k : Nat) :=
  ∃ (s t : Nat) (z u v : Fin n), gateAt C k = ⟨.and,[s,t]⟩ ∧ s < n+k ∧ t < n+k ∧
    G.Adj z u ∧ Owns n C k z u ∧ Owns n C k z v ∧
    ∀ a b, needed G C k a b → (a=z ∨ b=z) ∧ (a=u ∨ b=u ∨ a=v ∨ b=v)

def TwoForcingVertices {n} (G : SimpleGraph (Fin n)) (C : Circuit) (k : Nat) :=
  ∃ u v : Fin n, (∀ x, x u = true → gateVal n C k x = true) ∧
    (∀ x, x v = true → gateVal n C k x = true) ∧
    ∀ a b, needed G C k a b → a=u ∨ b=u ∨ a=v ∨ b=v

/-- The original desk obligation reduces to the remaining earliest bad gates. -/
theorem exact_of_remaining_beyond_two_spokes
    (hard : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) → TopForm.NoFourCycle G →
      ∀ C : Circuit, Eligible G C → ∀ k < C.size, (∀ j < k, ¬BadAt G C j) → BadAt G C k →
      MultipleCritical G C k → ¬AdmitsStarPin G C k →
      ¬TwoOwnedSpokes G C k → ¬TwoForcingVertices G C k → RepairsAt G C k) : Exact1774 := by
  apply exact_of_remaining_critical_cases
  intro n G dec tri four C hC k inside early bad multi nstar
  by_cases spokes : TwoOwnedSpokes G C k
  · obtain ⟨s,t,z,u,v,site,hs,ht,edge,hu,hv,cover⟩ := spokes
    exact repair_of_two_owned_spokes G hC inside site hs ht z u v edge hu hv cover
  by_cases forcing : TwoForcingVertices G C k
  · obtain ⟨u,v,hu,hv,cover⟩ := forcing
    obtain ⟨_,_,_,_,_,_,owned,_⟩ := bad
    exact repair_of_two_forcing_vertices G hC inside owned.2.1 u v hu hv cover
  exact hard n G tri four C hC k inside early bad multi nstar spokes forcing

end PEqualNP.Research.GatePinning
