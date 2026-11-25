import Mask4

namespace VertexPeel.Mask4

/-- Distinct minimal 21-bit patterns of triangles and four-cycles. -/
def girthMasks : List Code := [11, 21, 30, 38, 45, 51, 56, 257, 266, 276, 1026, 1033, 1060, 2051, 2056, 2096, 4097, 4098, 4104, 4116, 4132, 4144, 4352, 5120, 6144, 16388, 16401, 16418, 32773, 32784, 32808, 65537, 65540, 65546, 65552, 65570, 65576, 65792, 69632, 81920, 98304, 131078, 131096, 131104, 262146, 262148, 262153, 262161, 262168, 262176, 263168, 266240, 278528, 327680, 393216, 524291, 524293, 524294, 524296, 524304, 524320, 526336, 528384, 557056, 589824, 655360, 786432, 1048577, 1048578, 1048580, 1048584, 1048592, 1048608, 1048832, 1049600, 1050624, 1052672, 1064960, 1081344, 1114112, 1179648, 1310720, 1572864]

def smallGirthB (z : Code) : Bool := girthMasks.all fun m => (z &&& m) != m

/-- A node records the bit to choose and the forbidden patterns checked upon setting it. -/
structure Step where
  index : Nat
  tests : List Code

def accept (t : Step) (z : Code) : Bool := t.tests.all fun m => (z &&& m) != m

def enumCodes : List Step → Code → List Code
  | [], z => [z]
  | t::ts, z =>
    let new := z ||| BitVec.twoPow 21 t.index
    enumCodes ts z ++ (if accept t new then enumCodes ts new else [])

/-- First choose the internal mask, then the outside mask. Each stage descends
from its most significant bit, giving lexicographic order by these two masks. -/
def steps : List Step := [
  ⟨5,[]⟩,
  ⟨4,[]⟩,
  ⟨3,[56]⟩,
  ⟨2,[]⟩,
  ⟨1,[30, 38]⟩,
  ⟨0,[11, 21, 45, 51]⟩,
  ⟨20,[1048577, 1048578, 1048580, 1048584, 1048592, 1048608]⟩,
  ⟨19,[524291, 524293, 524294, 524296, 524304, 524320, 1572864]⟩,
  ⟨18,[262146, 262148, 262153, 262161, 262168, 262176, 786432, 1310720]⟩,
  ⟨17,[131078, 131096, 131104, 393216, 655360, 1179648]⟩,
  ⟨16,[65537, 65540, 65546, 65552, 65570, 65576, 327680, 589824, 1114112]⟩,
  ⟨15,[32773, 32784, 32808, 98304, 557056, 1081344]⟩,
  ⟨14,[16388, 16401, 16418, 81920, 278528, 1064960]⟩,
  ⟨13,[]⟩,
  ⟨12,[4097, 4098, 4104, 4116, 4132, 4144, 69632, 266240, 528384, 1052672]⟩,
  ⟨11,[2051, 2056, 2096, 6144, 526336, 1050624]⟩,
  ⟨10,[1026, 1033, 1060, 5120, 263168, 1049600]⟩,
  ⟨9,[]⟩,
  ⟨8,[257, 266, 276, 4352, 65792, 1048832]⟩,
  ⟨7,[]⟩,
  ⟨6,[]⟩]

def raw8144 : List Code := enumCodes steps 0

end VertexPeel.Mask4
