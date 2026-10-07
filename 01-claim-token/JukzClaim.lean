-- ClaimToken: decide quién gana el rol de host en jukz
-- Gana el token con generación más alta; si empatan, gana el timestamp más reciente.

structure ClaimToken where
  generation : Nat      -- sube cada vez que el nodo reclama host
  timestamp  : Nat      -- unix ms en el momento del reclamo
  nodeId     : String
  deriving Repr

-- Orden total: primero generation, luego timestamp como desempate
def ClaimToken.beats (a b : ClaimToken) : Bool :=
  a.generation > b.generation ||
  (a.generation == b.generation && a.timestamp > b.timestamp)

-- Elige el token ganador entre dos candidatos
def ClaimToken.winner (a b : ClaimToken) : ClaimToken :=
  if a.beats b then a else b

-- Próxima generación para este nodo (usado al re-reclamar)
def ClaimToken.next (t : ClaimToken) (newTimestamp : Nat) : ClaimToken :=
  { t with generation := t.generation + 1, timestamp := newTimestamp }

-- ── Propiedades ────────────────────────────────────────────────────

-- Un token siempre se gana a sí mismo (reflexividad del winner)
theorem winner_self (t : ClaimToken) : ClaimToken.winner t t = t := by
  simp [ClaimToken.winner, ClaimToken.beats]

-- Si a gana contra b, winner devuelve a
theorem winner_left {a b : ClaimToken} (h : a.beats b = true) :
    ClaimToken.winner a b = a := by
  simp [ClaimToken.winner, h]

-- Si a no gana contra b, winner devuelve b
theorem winner_right {a b : ClaimToken} (h : a.beats b = false) :
    ClaimToken.winner a b = b := by
  simp [ClaimToken.winner, h]

-- next siempre produce una generación estrictamente mayor
theorem next_generation_increases (t : ClaimToken) (ts : Nat) :
    (t.next ts).generation = t.generation + 1 := by
  simp [ClaimToken.next]

-- Un token renovado siempre le gana al original (generación + 1)
theorem next_beats_original (t : ClaimToken) (ts : Nat) :
    (t.next ts).beats t = true := by
  simp [ClaimToken.beats, ClaimToken.next]
