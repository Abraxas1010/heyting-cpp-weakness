# CPP Weakness / Meet-Quantale — Implementable Plan

Date: 2026-01-05 (America/Detroit)

## What is already implemented (DONE)

- `HeytingLean.CPP.weakness` with core lemmas and `weakness_union`.
- `HeytingLean.CPP.MeetQuantale` wrapper:
  - `Mul := (⊓)` and `One := ⊤`,
  - `IsQuantale` under `[Order.Frame α]`,
  - no global instance leakage (wrapper, not `abbrev`).
- `HeytingLean.CPP.toSublocale_antitone` + `omegaMap` (nucleus “ratchet” inclusion).
- Umbrella import: `HeytingLean.CPP.All`.
- Smoke tests: `HeytingLean.Tests.CPP.WeaknessSanity`.
- Regression guard: importing CPP does not create a global `Mul (Set Bool)`.
- Local verification: `lake build --wfail`, build/run `cpp_smoke`.

## What I’m confident implementing next (HIGH confidence)

1. **More weakness algebra (still minimal assumptions)**
   - `weakness_iUnion` / `weakness_sUnion` (for families of relations).
   - `weakness_image` / transport lemmas for reindexing relations.
2. **Bridge helpers for Ω-cores**
   - A small module that packages the common pattern:
     - `μ : U → Ω` (fixed points / Ω-core) ⇒ `μ : U → MeetQuantale Ω` by coercion,
     - then `weakness H μ` lives in the meet-quantale.
3. **Extend instance-hygiene regression coverage**
   - Add 1–2 more “fail-if-success” tests on other common frames in the codebase.

## What is plausible but needs research/proof search first (MEDIUM confidence)

- A “lens refinement” theorem relating:
  - tightening nuclei (`m ≤ n`) and the induced inclusion of Ω-cores,
  - reindexing a weakness computation along `omegaMap`.

This is likely true but depends on the exact order convention on nuclei and how your downstream
construction interprets “weakness” across lenses.
