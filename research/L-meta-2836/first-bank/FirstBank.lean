import VerifiedCore
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Research3561
namespace PEqualNP.Research2836.First

def encoded (x : Fin 9 → Bool) : List Bool :=
  List.ofFn (Function.update x 0 false) ++ [x 0 || x 4, x 0 || x 3]

def bank : List Sig := [zero,raw1,raw2,raw3,raw4,raw5,raw6,raw7,raw8,
  bin true raw0 raw4,bin true raw0 raw3]

def signals : List Sig := [raw1,raw2,raw3,raw4,raw5,raw6,raw7,raw8,
  bin true raw0 raw4,bin true raw0 raw3]
lemma bankValid : ∀ a ∈ bank, Valid a := validOfBound (by decide +kernel)
lemma signalValid : ∀ a ∈ signals, Valid a := validOfBound (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma bankMaps : ∀ (s : Bool) (i : Fin 414), bank.map (bit s i) = encoded (sample s i) := by
  decide +kernel
lemma everySignal : signals.all (fun a => unionSep true (signals.erase a) != top) = true := by decide +kernel
lemma necessarySignals {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ signals) : signals.toFinset = S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_, hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp everySignal a hr
  have cov : unionSep true (signals.erase a) = top := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [testBit_top]
    by_cases hi : i < 414
    · simp only [hi, decide_true]
      obtain ⟨b, hb, h⟩ := live_sep l i hi
      have ba : b ≠ a := fun he => hn (he ▸ hb)
      have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
      exact (mem_unionSep true _ _).2 ⟨b, hm, sep_weaken _ (live_proper l b hb).1 i hi h⟩
    · simp only [hi, decide_false]
      exact valid_unionSep (fun x hx => signalValid x (List.mem_of_mem_erase hx)) i (by omega)
  simp [cov] at fail
lemma bankTarget (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 9 → Bool, C.eval (encoded x) = edgeF x) : target ∈ execute C.gates bank := by
  let w := execute C.gates bank
  have hwv : ∀ a ∈ w, Valid a := execute_valid C.gates bank bankValid
  have hproj (s : Bool) (i : Fin 414) : bit s i (w.getD C.output zero) = s := by
    rw [← b_read]
    change ((execute C.gates bank).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ bankValid (fun g hg => (h g hg).1)]
    have eq := he (sample s i)
    rw [← bankMaps, sample_ok] at eq
    exact eq
  have hvout : Valid (w.getD C.output zero) := valid_getD hwv C.output
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply Nat.eq_of_testBit_eq; intro i
      rw [target, testBit_top]
      by_cases hi : i < 414
      · simpa [bit, hi] using hproj true ⟨i, hi⟩
      · rw [hvout.1 i (by omega)]; simp [hi]
    · apply Nat.eq_of_testBit_eq; intro i
      by_cases hi : i < 414
      · simpa [bit, target] using hproj false ⟨i, hi⟩
      · rw [hvout.2 i (by omega), target]; exact (Nat.zero_testBit i).symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

theorem extractedBank (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 9 → Bool, C.eval (encoded x) = edgeF x) :
    ∃ k t, k ≤ C.size ∧ Live k t signals.toFinset ∧ t + 9 ≤ k := by
  obtain ⟨k,t,S,hk,run,sub⟩ := extract C.gates bank bankValid legal (bankTarget C legal computes)
  have eq : signals.toFinset = S := necessarySignals run (by
    intro a ha
    have hb := sub a ha
    have positive := (live_proper run a ha).2.1
    simpa [signals,bank,List.mem_cons,positive] using hb)
  subst S
  have bound := (live_size run).2
  have card : signals.toFinset.card = 10 := by decide +kernel
  rw [card] at bound
  exact ⟨k,t,hk,run,by omega⟩


def firstWires : List Wire := signals.map fun a => (a, Tag.tNone)
lemma rootRep : Represents firstWires signals.toFinset plainTag := by
  refine ⟨?_,?_,?_⟩
  · change signals.Nodup; decide +kernel
  · rfl
  · intro w hw; obtain ⟨a,_,rfl⟩ := List.mem_map.mp hw; rfl

/-- The ten indispensable signals and a signed rectangle conflict exclude four NOTs. -/
theorem excludes_four : Impossible 13 4 firstWires :=
  KWCertificate.certified_sound (code := 0x6bbc2aeec804b) (by decide +kernel)

/-- Every size-thirteen candidate for the first bank gives a sampled live trace
with at most three NOTs. -/
theorem at_most_three (C : Circuit) (legal : FanInTwo C) (size : C.size ≤ 13)
    (correct : ∀ x : Fin 9 → Bool, C.eval (encoded x) = edgeF x) :
    ∃ k ≤ 13, ∃ t ≤ 3, Live k t signals.toFinset := by
  obtain ⟨k,t,budget,run,cap⟩ := extractedBank C legal correct
  refine ⟨k,by omega,t,?_,run⟩
  by_contra! tooMany
  have eq : t=4 := by omega
  subst t
  exact excludes_four k (by omega) _ _ rootRep (plainRun run)

end PEqualNP.Research2836.First
