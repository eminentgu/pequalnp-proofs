import SearchCore

open PEqualNP.Research3561

def main : IO Unit := do
  for negations in [4, 3, 2, 1, 0] do
    let found := search 13 negations wiresW
    IO.println s!"negations={negations} circuit_found={found}"
    if found then throw <| IO.userError "a search branch survived"
