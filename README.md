# heyting-cpp-weakness

Minimal Lean 4 / Mathlib formalization of the CPP “weakness” kernel and the meet-quantale
(`(*) := (⊓)`) view of frames/locales, packaged for reuse.

## What’s in the library

- `HeytingLean.CPP.weakness`:
  `weakness H μ := sSup ((fun p => μ p.1 * μ p.2) '' H)` for `H : Set (U×U)`, `μ : U → V`.
- `HeytingLean.CPP.MeetQuantale α`:
  a wrapper type that equips a frame `α` with `Mul := (⊓)` and `One := ⊤`, plus `IsQuantale`.
- `HeytingLean.CPP.toSublocale_antitone` / `omegaMap`:
  the nucleus “ratchet” direction: tightening nuclei induces inclusion of fixed-point sublocales.

## Build

```bash
lake update
lake build --wfail
lake build --wfail HeytingLean.Tests.CPP.WeaknessSanity
lake exe cpp_smoke
```

## Docs

- `docs/TECHNICAL_REPORT.md`
- `docs/IMPLEMENTABLE_PLAN.md`

