import JukzClaim

def main : IO Unit := do
  let alice : ClaimToken := { generation := 3, timestamp := 1000, nodeId := "alice" }
  let bob   : ClaimToken := { generation := 3, timestamp := 1200, nodeId := "bob"   }
  let carol : ClaimToken := { generation := 4, timestamp :=  500, nodeId := "carol" }

  -- mismo gen → gana timestamp más alto (bob)
  let w1 := ClaimToken.winner alice bob
  IO.println s!"alice vs bob  → {w1.nodeId} (gen={w1.generation} ts={w1.timestamp})"

  -- carol tiene gen más alta → gana aunque su ts sea menor
  let w2 := ClaimToken.winner bob carol
  IO.println s!"bob   vs carol → {w2.nodeId} (gen={w2.generation} ts={w2.timestamp})"

  -- alice reclama de nuevo
  let alice2 := alice.next 9999
  let w3 := ClaimToken.winner alice2 carol
  IO.println s!"alice2 vs carol → {w3.nodeId} (gen={w3.generation} ts={w3.timestamp})"
