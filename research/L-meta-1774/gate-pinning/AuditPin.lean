import PinDesk
import PinTree
import CriticalTree
import LocalRigidity
import PrivateParents
import MatchingRigidity
import CriticalPairTree
import CriticalOrTree
import GroupedStarTree

open PEqualNP.Research.GatePinning
#print axioms other_owners_survive
#print axioms pin_correct
#print axioms pin_critical_star
#print axioms normal_of_first_repairs
#print axioms exact_of_critical_stars
#print axioms Tree.precise_critical_edges
#print axioms Tree.repaired
#print axioms Tree.not_minimum

#print axioms critical_exists
#print axioms repair_if_at_most_one_critical
#print axioms exact_of_remaining_critical_cases
#print axioms CriticalTree.only_needed
#print axioms CriticalTree.correct
#print axioms CriticalTree.ready
#print axioms CriticalTree.changed_owners
#print axioms CriticalTree.new_clean
#print axioms CriticalTree.not_minimum

#print axioms rewrite_correct_iff
#print axioms every_wire_fails
#print axioms and_parent_witness
#print axioms or_parent_witness
#print axioms or_multiple_critical
#print axioms and_parent_not_sound
#print axioms or_parent_not_complete

#print axioms LocalRigidity.only_gate
#print axioms LocalRigidity.critical_edges
#print axioms LocalRigidity.forbidden_rows


#print axioms owned_operand_forces
#print axioms repair_of_two_forcing_vertices
#print axioms repair_of_two_owned_spokes
#print axioms exact_of_remaining_beyond_two_spokes
#print axioms masked_owners_survive
#print axioms repair_of_masked_or
#print axioms repair_of_precomputed_pairs
#print axioms repair_of_grouped_star
#print axioms repair_of_precomputed_spokes

#print axioms CriticalOrTree.correct
#print axioms CriticalOrTree.ready
#print axioms CriticalOrTree.old_defect
#print axioms CriticalOrTree.owns_spokes
#print axioms CriticalOrTree.critical_spokes
#print axioms CriticalOrTree.no_star_pin
#print axioms CriticalOrTree.new_clean
#print axioms CriticalOrTree.not_minimum

#print axioms GroupedStarTree.correct
#print axioms GroupedStarTree.ready
#print axioms GroupedStarTree.old_defect
#print axioms GroupedStarTree.grouped_wire_outside
#print axioms GroupedStarTree.critical_spokes
#print axioms GroupedStarTree.both_unowned
#print axioms GroupedStarTree.clean
#print axioms GroupedStarTree.not_minimum


#print axioms CriticalPairTree.correct
#print axioms CriticalPairTree.ready
#print axioms CriticalPairTree.old_defect
#print axioms CriticalPairTree.both_outside
#print axioms CriticalPairTree.critical_matching
#print axioms CriticalPairTree.clean
#print axioms CriticalPairTree.not_minimum


#print axioms repair_of_private_parents
#print axioms exact_of_remaining_shared_cases
#print axioms MatchingRigidity.correct
#print axioms MatchingRigidity.ready
#print axioms MatchingRigidity.old_defect
#print axioms MatchingRigidity.not_minimum
#print axioms MatchingRigidity.only_gate
#print axioms MatchingRigidity.critical_edges
#print axioms MatchingRigidity.no_precomputed_pairs
#print axioms MatchingRigidity.three_gate_repair
