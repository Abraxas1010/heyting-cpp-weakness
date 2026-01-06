# CPP Weakness / Meet-Quantale Layer — Technical Report

Date: 2026-01-05 (America/Detroit)

## Scope

This report documents the Lean-side “CPP weakness” algebraic core that was implemented and QA-verified:

- a relation-valued **weakness functional** `w(H, μ) := sSup { μ u * μ v | (u,v) ∈ H }`,
- a **non-invasive** “logic-channel tensor” view of any frame as a quantale via `(*) := (⊓)`,
- a small **nucleus ratchet** helper: `m ≤ n` induces inclusion `n.toSublocale ≤ m.toSublocale`.

The design goal was extraction-readiness: minimal surface area, no global instance pollution, and strict
build/run/robustness coverage.

## Implemented Lean modules

### `HeytingLean/CPP/Weakness.lean`

- Definition:
  - `HeytingLean.CPP.weakness` (polymorphic over `[CompleteLattice V] [Mul V]`).
- Kernel lemmas:
  - `HeytingLean.CPP.weakness_mono_rel` (monotone in `H`).
  - `HeytingLean.CPP.weakness_empty` (empty relation gives `⊥`).
  - `HeytingLean.CPP.mul_le_weakness` (membership lower bound).
- CPP-relevant algebraic property:
  - `HeytingLean.CPP.weakness_union` (`H₁ ∪ H₂` maps to `⊔` of weaknesses).

### `HeytingLean/CPP/MeetQuantale.lean`

- Wrapper type (prevents instance leakage):
  - `HeytingLean.CPP.MeetQuantale α` as a `structure` with field `val : α`.
  - `Coe`/`CoeTC` allow writing `(a : α)` and coercing `a : α` into `MeetQuantale α`.
- Transported lattice structure:
  - `CompleteLattice (MeetQuantale α)` is defined by pushing operations to `α` and using `sSup`/`sInf`
    over images.
- “Logic-channel tensor”:
  - `Mul (MeetQuantale α)` is `⊓` (requires `[SemilatticeInf α]`).
  - `One (MeetQuantale α)` is `⊤` (requires `[Top α]`).
- Quantale structure:
  - `IsQuantale (MeetQuantale α)` is provided under `[Order.Frame α]`, using Mathlib’s frame
    distributivity lemmas `_root_.inf_sSup_eq` and `_root_.sSup_inf_eq`.

### `HeytingLean/CPP/Ratchet.lean`

- `HeytingLean.CPP.toSublocale_antitone`:
  - if `m ≤ n : Nucleus X` then `n.toSublocale ≤ m.toSublocale`.
- `HeytingLean.CPP.omegaMap`:
  - the induced inclusion map `n.toSublocale → m.toSublocale`.

### `HeytingLean/CPP/All.lean`

- Umbrella module re-exporting `Weakness`, `MeetQuantale`, `Ratchet`.

### `HeytingLean/Tests/CPP/WeaknessSanity.lean`

Smoke checks (typeclass and basic lemma usage) on:

- `Set Bool` with `MeetQuantale (Set Bool)` as the value type.
- instance-hygiene regression guard: importing the CPP layer does not create a global `Mul (Set Bool)`.
- a small ratchet sanity check on nuclei (via `Mathlib.Order.Sublocale`).

## Key design decision: prevent global instance pollution

Originally, `MeetQuantale` was an `abbrev` alias. That is unsafe because adding `Mul (MeetQuantale α)`
effectively adds a `Mul`-instance for `α` itself (typeclass inference treats definitional equalities as
transparent), which can silently “manufacture” multiplications on types like `Set Bool`.

This was fixed by making `MeetQuantale` a real wrapper `structure`, with explicit coercions back and
forth. This keeps `Mul`/`One` local to the wrapper and preserves downstream typeclass hygiene.

## QA / verification performed (local)

Verification for this extracted package:

- `lake build --wfail`
- `lake build --wfail HeytingLean.Tests.CPP.WeaknessSanity`
- `lake build --wfail cpp_smoke && lake exe cpp_smoke`

## Immediate next implementable steps (high-confidence)

1. Add more algebraic API for `weakness` (e.g. `iUnion` versions; order-theoretic bounds) under minimal
   assumptions.
2. Add a small “bridge” module explicitly specializing weakness to Ω-cores / sublocales in your system
   (mostly typeclass-resolution documentation + examples).
3. Add one more import-only regression test in a “neutral” module (to catch accidental instance
   pollution beyond the `Set Bool` case).
