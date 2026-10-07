-- Nivel 2: ClaimToken + DeviceKey + orden de fencing.
-- Espejo de rendezvous-worker/src/logic.ts (cmpToken, announce) y guard.ts (426 sin llave).

structure DeviceKey where
  deviceId : String
  deriving Repr, DecidableEq

-- nodeId son 32 hex en minúscula: su orden de texto es igual al orden numérico,
-- así que se modela como Nat.
structure ClaimToken where
  generation : Nat
  timestamp  : Nat   -- claimEpochMillis
  nodeId     : Nat
  deriving Repr, DecidableEq

-- El token viaja junto a la llave del dispositivo; none = cliente viejo
structure Announce where
  token : ClaimToken
  key   : Option DeviceKey
  deriving Repr

namespace ClaimToken

-- a ≻ b: generación, luego timestamp, luego nodeId (spec R1)
def Beats (a b : ClaimToken) : Prop :=
  a.generation > b.generation ∨
  (a.generation = b.generation ∧ a.timestamp > b.timestamp) ∨
  (a.generation = b.generation ∧ a.timestamp = b.timestamp ∧ a.nodeId > b.nodeId)

instance (a b : ClaimToken) : Decidable (Beats a b) :=
  inferInstanceAs (Decidable (_ ∨ _))

infix:50 " ≻ " => Beats

-- ── Orden estricto y total ─────────────────────────────────────────

theorem beats_irrefl (a : ClaimToken) : ¬ a ≻ a := by
  unfold Beats; omega

theorem beats_asymm {a b : ClaimToken} (h : a ≻ b) : ¬ b ≻ a := by
  unfold Beats at *; omega

theorem beats_trans {a b c : ClaimToken} (h₁ : a ≻ b) (h₂ : b ≻ c) : a ≻ c := by
  unfold Beats at *; omega

-- Dos tokens distintos nunca empatan: siempre hay un ganador
theorem beats_total {a b : ClaimToken} (h : a ≠ b) : a ≻ b ∨ b ≻ a := by
  cases a; cases b
  simp only [Beats, ne_eq, ClaimToken.mk.injEq] at *
  omega

theorem higher_gen_beats {a b : ClaimToken} (h : a.generation > b.generation) :
    a ≻ b := Or.inl h

theorem lower_gen_loses {a b : ClaimToken} (h : a.generation < b.generation) :
    ¬ a ≻ b := by
  unfold Beats; omega

end ClaimToken

-- ── Registro con fencing ───────────────────────────────────────────

open ClaimToken

abbrev Lease := Option ClaimToken

-- Sin llave se rechaza; con llave, el vigente gana salvo que el nuevo sea estrictamente mayor
def Lease.apply : Lease → Announce → Lease
  | s, ⟨t, key⟩ =>
    match key with
    | none   => s
    | some _ =>
      match s with
      | none     => some t
      | some cur => if t ≻ cur then some t else some cur

def Lease.gen : Lease → Nat
  | none   => 0
  | some t => t.generation

theorem no_key_rejected (s : Lease) (t : ClaimToken) :
    Lease.apply s ⟨t, none⟩ = s := rfl

theorem lower_never_overwrites (cur : ClaimToken) (a : Announce)
    (h : a.token.generation < cur.generation) :
    Lease.apply (some cur) a = some cur := by
  have := lower_gen_loses h
  obtain ⟨t, key⟩ := a
  cases key <;> simp_all [Lease.apply]

-- Dos anuncios en conflicto: el de generación mayor queda, llegue primero o segundo
theorem higher_gen_prevails (a b : ClaimToken) (ka kb : DeviceKey)
    (h : a.generation > b.generation) :
    Lease.apply (Lease.apply none ⟨a, some ka⟩) ⟨b, some kb⟩ = some a ∧
    Lease.apply (Lease.apply none ⟨b, some kb⟩) ⟨a, some ka⟩ = some a := by
  have hab := higher_gen_beats h
  have hba := beats_asymm hab
  simp [Lease.apply, hab, hba]

-- El orden de llegada no importa: dos anuncios válidos y distintos terminan igual
theorem order_independent (a b : ClaimToken) (ka kb : DeviceKey) (h : a ≠ b) :
    Lease.apply (Lease.apply none ⟨a, some ka⟩) ⟨b, some kb⟩ =
    Lease.apply (Lease.apply none ⟨b, some kb⟩) ⟨a, some ka⟩ := by
  rcases beats_total h with hab | hba
  · simp [Lease.apply, hab, beats_asymm hab]
  · simp [Lease.apply, hba, beats_asymm hba]

-- Fencing: la generación del registro nunca baja
theorem gen_monotone (s : Lease) (a : Announce) :
    Lease.gen s ≤ Lease.gen (Lease.apply s a) := by
  obtain ⟨t, key⟩ := a
  cases key with
  | none => exact Nat.le_refl _
  | some k =>
    cases s with
    | none => simp [Lease.gen]
    | some cur =>
      by_cases hb : t ≻ cur
      · have : cur.generation ≤ t.generation := by unfold Beats at hb; omega
        simp [Lease.apply, Lease.gen, hb, this]
      · simp [Lease.apply, Lease.gen, hb]

theorem gen_monotone_list (s : Lease) (as : List Announce) :
    Lease.gen s ≤ Lease.gen (as.foldl Lease.apply s) := by
  induction as generalizing s with
  | nil => simp
  | cons a as ih => exact Nat.le_trans (gen_monotone s a) (ih _)
