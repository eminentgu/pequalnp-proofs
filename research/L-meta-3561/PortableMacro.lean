import EncodedBank

namespace PEqualNP.Research3561.PortableMacro

/-- Evaluate the old wire on selected extremal rows and the new one on all rows. -/
def Dominates (pos neg : Fin 414 → Fin 414) (new old : Sig) : Prop :=
  (∀ i, bit true (pos i) old = true → bit true i new = true) ∧
  (∀ i, bit false i new = true → bit false (neg i) old = true)

def MonoFeasible (k : Nat) (B : Finset Sig) : Prop :=
  ∃ m ≤ k, ∃ S ⊆ B, Live m 0 S

private theorem binary_usable {w a b} (d : Bool) (va : Valid a) (vb : Valid b)
    (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ (proper a ∧ proper b ∧ a ≠ b) := by
  have rz : represented w zero := Or.inr (fun h => h.2.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws va
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws vb
  rcases operand_cases va ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases vb hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases e : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr ⟨hap,hbp,e⟩

private theorem pull {k : Nat} {B : Finset Sig} {a b : Sig} {d : Bool}
    (ma : a ∈ B) (mb : b ∈ B) (va : Valid a) (vb : Valid b)
    (h : MonoFeasible k (insert (bin d a b) B)) : MonoFeasible (k+1) B := by
  obtain ⟨m,hm,S,sub,run⟩ := h
  by_cases incl : S ⊆ B
  · exact ⟨m,by omega,S,incl,run⟩
  have liveG : bin d a b ∈ S := by
    by_contra hn
    exact incl (fun x hx => (Finset.mem_insert.mp (sub hx)).resolve_left (fun e => hn (e ▸ hx)))
  have newG : bin d a b ∉ B := fun hb => incl (by simpa [Finset.insert_eq_of_mem hb] using sub)
  have properG := live_proper run _ liveG
  rcases binary_usable d va vb (w:=B.toList) (Or.inl (Finset.mem_toList.mpr ma))
      (Or.inl (Finset.mem_toList.mpr mb)) with old | ⟨pa,pb,ab⟩
  · exact (newG (Finset.mem_toList.mp (old.resolve_right (fun h => h properG)))).elim
  · let U := S.erase (bin d a b)
    have subU : U ⊆ B := fun x h => (Finset.mem_insert.mp (sub (Finset.mem_erase.mp h).2)).resolve_left
      (Finset.mem_erase.mp h).1
    have fresh : bin d a b ∉ insert a (insert b U) := fun h => newG (by
      rcases Finset.mem_insert.mp h with e | h
      · exact e.symm ▸ ma
      · rcases Finset.mem_insert.mp h with e | h
        · exact e.symm ▸ mb
        · exact subU h)
    refine ⟨m+1,by omega,insert a (insert b U),Finset.insert_subset ma (Finset.insert_subset mb subU),Live.binary pa pb ab fresh ?_⟩
    simpa [U,Finset.insert_erase liveG] using run

private theorem propagates (d x y x' y' : Bool) (hx : x=true → x'=true) (hy : y=true → y'=true) :
    (if d then x || y else x && y)=true → (if d then x' || y' else x' && y')=true := by
  cases d <;> cases x <;> cases y <;> simp_all

private theorem combine {p n a b c e} (hc : Dominates p n a c) (he : Dominates p n b e) (d : Bool) :
    Dominates p n (bin d a b) (bin d c e) := by
  constructor
  · intro i; simpa only [bit_bin] using propagates d _ _ _ _ (hc.1 i) (he.1 i)
  · intro i; simpa only [bit_bin] using propagates d _ _ _ _ (hc.2 i) (he.2 i)

private theorem dominates_target {p n a} (v : Valid a) (h : Dominates p n a target) : a=target := by
  apply Prod.ext
  · apply Nat.eq_of_testBit_eq; intro i
    change a.1.testBit i = top.testBit i
    by_cases hi : i<414
    · have e := h.1 ⟨i,hi⟩ (by simp [bit,target,testBit_top,(p ⟨i,hi⟩).isLt])
      simpa [bit,testBit_top,hi] using e
    · simp [testBit_top,hi,v.1 i (by omega)]
  · apply Nat.eq_of_testBit_eq; intro i
    change a.2.testBit i = (0:Nat).testBit i
    by_cases hi : i<414
    · cases hbit : a.2.testBit i with
      | false => simp
      | true => have e := h.2 ⟨i,hi⟩ hbit; simp [bit,target] at e
    · simp [v.2 i (by omega)]

/-- Replacing live wires by dominating wires preserves a monotone suffix. -/
theorem transfer (p n : Fin 414 → Fin 414) {k t S} (run : Live k t S) (mono : t=0)
    (B : Finset Sig) (covers : ∀ a ∈ S, ∃ b ∈ B, Valid b ∧ Dominates p n b a) : MonoFeasible k B := by
  induction run generalizing B with
  | stop =>
    obtain ⟨b,hb,hv,hd⟩ := covers target (Finset.mem_singleton_self _)
    exact ⟨0,by omega,{target},Finset.singleton_subset_iff.mpr ((dominates_target hv hd) ▸ hb),Live.stop⟩
  | unary => omega
  | @binary k t U a b d _ _ _ _ _ ih =>
    obtain ⟨x,hx,vx,dx⟩ := covers a (Finset.mem_insert_self _ _)
    obtain ⟨y,hy,vy,dy⟩ := covers b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    apply pull hx hy vx vy (d:=d)
    apply ih mono
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hU
    · exact ⟨bin d x y,Finset.mem_insert_self _ _,valid_bin vx vy,combine dx dy d⟩
    · obtain ⟨w,hw,vw,dw⟩ := covers v (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU))
      exact ⟨w,Finset.mem_insert_of_mem hw,vw,dw⟩

inductive Prefix : Nat → Finset Sig → Finset Sig → Prop
  | nil (B) : Prefix 0 B B
  | gate {q B T a b} (d : Bool) (ha : a∈B) (hb : b∈B) (va : Valid a) (vb : Valid b)
      (tail : Prefix q (insert (bin d a b) B) T) : Prefix (q+1) B T

/-- A reusable cheap prefix can be replayed while leaving the suffix monotone. -/
theorem pull_prefix {q k B T} (hist : Prefix q B T) (h : MonoFeasible k T) : MonoFeasible (k+q) B := by
  induction hist with
  | nil => simpa using h
  | gate d ma mb va vb _ ih => simpa [Nat.add_assoc] using pull ma mb va vb (ih h)

/-- A cheaper reproduction of the current bank gives a smaller monotone proof obligation on
    the original ten input signals. Both constant signatures are free in the reproduction. -/
theorem shorter_original (p n : Fin 414 → Fin 414) {q k S T} (bound : k+q≤12)
    (hist : Prefix q (insert zero (insert one signals.toFinset)) T)
    (covers : ∀ a ∈ S, ∃ b ∈ T, Valid b ∧ Dominates p n b a) (run : Live k 0 S) :
    ∃ m ≤ 12, Live m 0 signals.toFinset := by
  obtain ⟨m,hm,U,inc,h⟩ := pull_prefix hist (transfer p n run rfl T covers)
  have sub : ∀ a ∈ U, a ∈ signals := by
    intro a ha
    obtain e | h₁ := Finset.mem_insert.mp (inc ha)
    · exact ((live_proper h _ ha).2.1 e).elim
    · obtain e | h₂ := Finset.mem_insert.mp h₁
      · exact ((live_proper h _ ha).2.2 e).elim
      · exact List.mem_toFinset.mp h₂
  refine ⟨m,by omega,?_⟩
  rwa [necessarySignals h sub]

end PEqualNP.Research3561.PortableMacro
