import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Research4387.Upper

abbrev Mask := BitVec 58

/-- Two constants, seven point columns, seven line columns, and the supplied
column for point 0 OR point 1, in the order of the L-meta-4387 receipt. -/
def seeds : List Mask := [
  0, BitVec.allOnes 58,
  95229015649943559, 63038587666488, 256462815680,
  4292497062759936, 8521481482240, 14003410187812864,
  55389823207997440, 189297016294081033, 155696362464477250,
  218994303132270608, 183565875465490436, 229736628138025984,
  270286071508633728, 288160007407550752, 95274182876594239]

/-- One line star uses two additional gates, and the other six use three
apiece. The last six gates join the seven stars. -/
def chain : List Mask := [
  98933359855537727, 521, 95229233422401991, 132534013687235015,
  262210, 14066427290157112, 69236073019965496, 557072,
  95235063194611719, 104664500684451847, 69636, 4301018365984256,
  58493748014513664, 1057792, 4292751074004928, 17944304641347520,
  133248, 63221765505528, 70368742109688, 16672,
  262731, 819803, 889439, 1947231,
  2080479, 2097151]

/-- Each instruction gives the first wire address, whether to use AND, and
the second wire address. Addresses start at zero in the original seed bank. -/
def instructions : List (ℕ × Bool × ℕ) := [
  (16, false, 5), (17, true, 9), (2, false, 4), (19, false, 8),
  (20, true, 10), (3, false, 7), (22, false, 8), (23, true, 11),
  (2, false, 6), (25, false, 7), (26, true, 12), (5, false, 6),
  (28, false, 8), (29, true, 13), (4, false, 5), (31, false, 7),
  (32, true, 14), (3, false, 4), (34, false, 6), (35, true, 15),
  (18, false, 21), (37, false, 24), (38, false, 27), (39, false, 30),
  (40, false, 33), (41, false, 36)]

private theorem indicesValid : ∀ k : Fin chain.length,
    let bank := seeds ++ chain.take k.val
    let op := instructions.getD k.val (0,false,0)
    op.1 < bank.length ∧ op.2.2 < bank.length ∧
      chain.get k = if op.2.1 then bank.getD op.1 0 &&& bank.getD op.2.2 0
        else bank.getD op.1 0 ||| bank.getD op.2.2 0 := by decide +kernel

/-- The numerical chain uses exactly 26 additional gates, passes the original
receipt's operand test, and ends in the designated target. -/
theorem upperWitness : chain.length = 26 ∧
    (∀ k : Fin chain.length,
      let bank := seeds ++ chain.take k.val
      ∃ a ∈ bank, ∃ b ∈ bank, chain.get k = a &&& b ∨ chain.get k = a ||| b) ∧
    chain.getLast? = some (2097151 : Mask) ∧ (2097151 : Mask) ∈ seeds ++ chain := by
  refine ⟨rfl,?_,by decide,by decide⟩
  intro k
  let bank := seeds ++ chain.take k.val
  let op := instructions.getD k.val (0,false,0)
  obtain ⟨ha,hb,eq⟩ := indicesValid k
  have mem (i : Nat) (hi : i < bank.length) : bank.getD i 0 ∈ bank := by
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
  refine ⟨bank.getD op.1 0,mem _ ha,bank.getD op.2.2 0,mem _ hb,?_⟩
  change chain.get k = (if op.2.1 then bank.getD op.1 0 &&& bank.getD op.2.2 0
    else bank.getD op.1 0 ||| bank.getD op.2.2 0) at eq
  split at eq
  · exact Or.inl eq
  · exact Or.inr eq

end PEqualNP.Research4387.Upper

#print axioms PEqualNP.Research4387.Upper.upperWitness
