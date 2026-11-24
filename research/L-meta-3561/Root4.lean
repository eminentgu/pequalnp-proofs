import SearchCore
import SignedReadOnceKW
namespace PEqualNP.Research3561

theorem kw_impossible_four : Impossible 13 4 wiresW := by
  intro m hm S τ rep restricted
  have inputs : sigsOf wiresW = signals := by simp [sigsOf,wiresW,List.map_map,Function.comp_def]
  have fs : signals.toFinset = S := inputs ▸ rep.2.1
  subst S
  have run := restricted.live
  have cap := (live_size run).2
  have size : signals.toFinset.card = 10 := by decide +kernel
  rw [size] at cap
  have exactSize : m = 13 := by omega
  subst m
  exact SignedReadOnceKW.no_four_nots run
end PEqualNP.Research3561
