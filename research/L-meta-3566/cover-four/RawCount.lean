import Raw8144
import Raw4704

namespace VertexPeel.Mask4

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem girth_count : raw8144.length = 8144 := by decide +kernel
theorem raw_count : raw4704.length = 4704 := by decide +kernel

end VertexPeel.Mask4
#print axioms VertexPeel.Mask4.girth_count
#print axioms VertexPeel.Mask4.raw_count
