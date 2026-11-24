import FirstMemo3
open PEqualNP.Research3561 PEqualNP.Research2836.First
namespace PEqualNP.Research2836.FirstMemo3
open KWMemo
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c_0 : span (nodeOK table) 12 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c_12 : span (nodeOK table) 12 12 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c_24 : span (nodeOK table) 12 24 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c_36 : span (nodeOK table) 12 36 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c_48 : span (nodeOK table) 12 48 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c_60 : span (nodeOK table) 12 60 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c_72 : span (nodeOK table) 12 72 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c_84 : span (nodeOK table) 12 84 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c_96 : span (nodeOK table) 10 96 = true := by decide +kernel
theorem allOK (i : Nat) (hi : i < 106) : nodeOK table i = true := by
  by_cases h_0 : i < 12
  · exact span_ok c_0 i (by omega) (by omega)
  by_cases h_12 : i < 24
  · exact span_ok c_12 i (by omega) (by omega)
  by_cases h_24 : i < 36
  · exact span_ok c_24 i (by omega) (by omega)
  by_cases h_36 : i < 48
  · exact span_ok c_36 i (by omega) (by omega)
  by_cases h_48 : i < 60
  · exact span_ok c_48 i (by omega) (by omega)
  by_cases h_60 : i < 72
  · exact span_ok c_60 i (by omega) (by omega)
  by_cases h_72 : i < 84
  · exact span_ok c_72 i (by omega) (by omega)
  by_cases h_84 : i < 96
  · exact span_ok c_84 i (by omega) (by omega)
  exact span_ok c_96 i (by omega) (by omega)
theorem root : Impossible 13 3 firstWires := by
  have h := checked_nodes table allOK 105 (by decide)
  have eq : permCheck firstWires (node 105).w = true := by decide +kernel
  exact perm_impossible (permCheck_perm eq) h
end PEqualNP.Research2836.FirstMemo3
