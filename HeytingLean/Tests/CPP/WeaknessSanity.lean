import Mathlib.Data.Set.Lattice
import HeytingLean.CPP.All

namespace HeytingLean.Tests.CPP

open HeytingLean.CPP

/-! Smoke checks for the CPP weakness layer (Mathlib-only). -/

section SetBool

def H : Set (Bool × Bool) := { (true, false) }

def μ : Bool → MeetQuantale (Set Bool)
  | true => (({true} : Set Bool) : MeetQuantale (Set Bool))
  | false => (({false} : Set Bool) : MeetQuantale (Set Bool))

-- Regression guard: the CPP layer should *not* create a global `Mul` instance on `Set Bool`
-- (pointwise set multiplication is intentionally scoped in Mathlib).
example : True := by
  fail_if_success
    have : Mul (Set Bool) := inferInstance
  trivial

#check weakness (H := H) μ

example : weakness (H := (∅ : Set (Bool × Bool))) μ = (⊥ : MeetQuantale (Set Bool)) := by
  simp [weakness]

example : μ true * μ false ≤ weakness (H := H) μ := by
  apply mul_le_weakness (H := H) (μ := μ)
  simp [H]

end SetBool

section Ratchet

-- Basic “ratchet direction” check on a concrete frame (`Set Bool`).
example :
    ((⊤ : Nucleus (Set Bool)).toSublocale ≤ (⊥ : Nucleus (Set Bool)).toSublocale) := by
  exact
    toSublocale_antitone (X := Set Bool)
      (m := (⊥ : Nucleus (Set Bool)))
      (n := (⊤ : Nucleus (Set Bool))) bot_le

end Ratchet

end HeytingLean.Tests.CPP
