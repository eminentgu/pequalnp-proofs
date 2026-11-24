import MacroDominance
open PEqualNP.Outside.L_meta_2913.Main1672
namespace PEqualNP.Research3561.ProjectedMonotone

private def extIndex (key : Nat) (j : Fin 414) : Fin 414 :=
  Fin.ofNat 414 (index9 key (if j.val < 252 then j.val else 0))

def extremalHom : SigHom := pairHom (extIndex 0x80400a4d269349a260109820100804020100202010080400000101389c2010269349a4d029349a4d269349a4d269349a4d269349a10080084e271389c04271389c4e271389c4e271389c4e070384020100804020100804020100804020100800008040000004261302004261301c0e00028141008040200005028984c02130981026130084c26130984c26130984c261309808070380000040402010080402010080402010080402000000381c0a05010080802010140a020101c0e07038000a05000100005028140a05028140a05028140a040381c00020101008020100004020100804020100804020100808070381c0e070381c0e070381c0e07038000000020100804020100804020100804000000000000000000000000000) (extIndex 0x5badde6ed5bbb56ef376bb5e69a76addda9a79bb5a8ed6a3cdda77391c96e776a159a85679b50acf376b51a8b74d1dce4562b0dc6e371bb51a872798dda8f376b51a8b74d1dce4561b8dc6ed46a3cc6ed45bbcddad46a2dd3477391586e371bb51a8f379b516eb73b9c96eb7392dd6eb75ba696e565b9596eb74d2686eb74d0dce49a1badde6ed6a2dd349a3b9c8ac371b8dd34b74d2696e9a5b959e6ed6a2dd349a3b9c8ac372b0dd34b73b9c8ee373badce4722b1c86e722b2dcac772b2dcee372b158acf376b516e9a3b9c8ac561b8dc6e371b9c86e375b9c86e722b0dde6ed6a2dd3477391586e372b0dc6eb72b3cddad45ba68ee722b0dc6e561b8dd6e5679bb5a8b74d1dce4561b9586e3779bb5a8b74d1dce4561b8dcac37)

def inputBank : List Sig := [raw0,raw1,raw2,raw3,raw5,raw6,raw7,raw8,
  bin true raw0 raw4, bin true raw4 raw1]

def domCheck (a b : Sig) : Bool := (a.1 &&& b.1 == b.1) && (a.2 &&& b.2 == a.2)

lemma domCheck_sound {a b : Sig} (h : domCheck a b = true) : Dominates a b := by
  simp only [domCheck,Bool.and_eq_true,beq_iff_eq] at h
  constructor
  · intro i hi
    have eq := congrArg (fun x : Nat => x.testBit i) h.1
    simpa [Nat.testBit_and,hi] using eq
  · intro i hi
    have eq := congrArg (fun x : Nat => x.testBit i) h.2
    simpa [Nat.testBit_and,hi] using eq

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem bank_check : inputBank.all (fun a => raw.any (fun b =>
    domCheck (homProject4.fn b) (extremalHom.fn a))) = true := by decide +kernel

private lemma bank_covered {a : Sig} (ha : a ∈ inputBank.toFinset) :
    ∃ b ∈ raw.toFinset, Dominates (homProject4.fn b) (extremalHom.fn a) := by
  have h := List.all_eq_true.mp bank_check a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,hh⟩ := List.any_eq_true.mp h
  exact ⟨b,List.mem_toFinset.mpr hb,domCheck_sound hh⟩

/-- Indexed using the eight raw signals followed by both prepaid signals. -/
def forbiddenPairs : List (Nat × Nat) := [(0,2),(0,3),(0,5),(0,6),(0,7),(1,3),(1,4),(1,6),(1,7),(2,4),(2,5),(2,7),(2,8),(3,4),(3,5),(3,6),(3,8),(3,9),(4,5),(4,9),(5,6),(5,8),(6,7),(6,8),(6,9),(7,8),(7,9)]

def firstAnd (ij : Nat × Nat) := bin false (inputBank.getD ij.1 zero) (inputBank.getD ij.2 zero)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem empty_positives : forbiddenPairs.all (fun ij =>
  (extremalHom.fn (firstAnd ij)).1 == 0) = true := by decide +kernel

/-- Any live bank after one of these AND gates admits no 12-gate monotone suffix. -/
theorem forbidden_first_and {ij : Nat × Nat} (hp : ij ∈ forbiddenPairs) {S : Finset Sig}
    (sub : S ⊆ insert (firstAnd ij) inputBank.toFinset) : ¬ Live 12 0 S := by
  apply shadow_prefix_bound extremalHom (q:=0) (by decide) (Prefix.nil _)
  intro a ha
  rcases Finset.mem_insert.mp (sub ha) with rfl | h
  · refine ⟨raw4,by simp [raw],?_⟩
    rw [project4_raw4]
    have z := beq_iff_eq.mp (List.all_eq_true.mp empty_positives ij hp)
    constructor
    · intro i hi
      simp [z] at hi
    · intro i hi
      simp [zero] at hi
  · exact bank_covered h

end PEqualNP.Research3561.ProjectedMonotone
