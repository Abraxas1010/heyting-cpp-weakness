<img src="assets/Apoth3osis.webp" alt="Apoth3osis Logo" width="140"/>

<sub><strong>Our tech stack is ontological:</strong><br>
<strong>Hardware — Physics</strong><br>
<strong>Software — Mathematics</strong><br><br>
<strong>Our engineering workflow is simple:</strong> discover, build, grow, learn & teach</sub>

---

<sub>
<strong>Notice of Proprietary Information</strong><br>
This document outlines foundational concepts and methodologies developed during internal research and development at Apoth3osis. To protect our intellectual property and adhere to client confidentiality agreements, the code, architectural details, and performance metrics presented herein may be simplified, redacted, or presented for illustrative purposes only. This paper is intended to share our conceptual approach and does not represent the full complexity, scope, or performance of our production-level systems. The complete implementation and its derivatives remain proprietary.
</sub>

---

# heyting-cpp-weakness

A small, extraction-ready Lean 4 / Mathlib package that isolates the *algebraic kernel* behind
CPP-style “weakness”, plus a safe “logic-channel tensor” on frames/locales:

- weakness as a supremum over an indistinction relation, and
- a meet-quantale wrapper (`(*) := (⊓)`, `1 := ⊤`) for any frame.

This repo is intentionally *not* the full CPP philosophy. It is the reusable core that lets you
state and prove CPP-shaped lemmas without dragging in a large surrounding system.


## Credo

> *"The genome doesn't specify the organism; it offers a set of pointers to regions in the space of all possible forms, relying on the laws of physics and computation to do the heavy lifting."*
> — **Michael Levin**

Our company operates as a lens for cognitive pointers: identifying established theoretical work and translating it into computationally parsable structures. By turning ideas into formal axioms, and axioms into verifiable code, we create the "Lego blocks" required to build complex systems with confidence.

### Acknowledgment

We humbly thank the collective intelligence of humanity for providing the technology and culture we cherish. We do our best to properly reference the authors of the works utilized herein, though we may occasionally fall short. Our formalization acts as a reciprocal validation—confirming the structural integrity of their original insights while securing the foundation upon which we build. In truth, all creative work is derivative; we stand on the shoulders of those who came before, and our contributions are simply the next link in an unbroken chain of human ingenuity.

---

## Why it matters (narrative)

In many “logic + computation” architectures you want a *single primitive* that:

- takes a relation expressing “indistinction / observational equivalence” between states, and
- produces a quantitative (or order-theoretic) summary of “how weak” that distinction is under a
  valuation `μ`.

CPP-style weakness is a canonical such primitive:

> **weakness** aggregates pairwise interactions `μ u ⊗ μ v` over indistinguishable pairs `(u,v) ∈ H`,
> then takes a supremum.

By keeping the definition polymorphic over a complete lattice + a tensor `(*)`, you can plug it into
different “channels” (different tensors / lattices) later. The meet-quantale wrapper supplies the
most conservative logic channel: *tensor is meet*, so combining evidence means intersecting
constraints.

Crucially, this package is written to be *instance-hygienic*: it does **not** pollute global
typeclass search with a new `Mul α` on your underlying frame.

## Mathematical content

### 1) Weakness functional

For `H : Set (U × U)` and `μ : U → V`, with `[CompleteLattice V] [Mul V]`, we define:

```lean
weakness H μ : V :=
  sSup ((fun p : U × U => μ p.1 * μ p.2) '' H)
```

Kernel lemmas (minimal assumptions; no quantale axioms needed):

- `weakness_mono_rel` : `H ⊆ H' → weakness H μ ≤ weakness H' μ`
- `weakness_empty` : `weakness ∅ μ = ⊥`
- `mul_le_weakness` : `(u,v) ∈ H → μ u * μ v ≤ weakness H μ`
- `weakness_union` : `weakness (H₁ ∪ H₂) μ = weakness H₁ μ ⊔ weakness H₂ μ`

### 2) Meet-quantale view of frames

Mathlib models quantales via `IsQuantale` (a distributivity mixin over `CompleteLattice` and
`Semigroup`). For any frame `α` (i.e. `[Order.Frame α]`), we provide a *wrapper type*:

- `MeetQuantale α` with coercions to/from `α`,
- `Mul (MeetQuantale α)` defined as `⊓`,
- `One (MeetQuantale α)` defined as `⊤`,
- `IsQuantale (MeetQuantale α)` proved using frame distributivity (`inf_sSup_eq`, `sSup_inf_eq`).

The key point: this is on a wrapper, not an `abbrev`, to avoid leaking a `Mul α` instance.

### 3) Nucleus “ratchet” direction (fixed points shrink when you tighten)

Mathlib represents nuclei and their fixed-point sublocales via `Nucleus` and `toSublocale`. We
package the standard antitone fact:

- `toSublocale_antitone : m ≤ n → n.toSublocale ≤ m.toSublocale`
- `omegaMap : n.toSublocale → m.toSublocale` induced by `m ≤ n`

This is the categorical backbone for talking about “ratcheting” between logical lenses.

## Computational / engineering notes

- Strict builds are supported (`--wfail`); the codebase is kept free of `sorry`/`admit`.
- Smoke coverage includes a regression guard ensuring that importing `HeytingLean.CPP.All` does *not*
  manufacture a global `Mul (Set Bool)` instance (pointwise set multiplication is scoped in Mathlib).

## Repo layout

- `HeytingLean/CPP/Weakness.lean` — definition + kernel lemmas
- `HeytingLean/CPP/MeetQuantale.lean` — wrapper + quantale structure
- `HeytingLean/CPP/Ratchet.lean` — nucleus/sublocale antitone map
- `HeytingLean/CPP/All.lean` — umbrella import
- `HeytingLean/Tests/CPP/WeaknessSanity.lean` — smoke tests (Mathlib-only)
- `docs/TECHNICAL_REPORT.md` — detailed technical report
- `docs/IMPLEMENTABLE_PLAN.md` — near-term implementation plan

## Quick start

```bash
lake update
lake build --wfail
lake build --wfail HeytingLean.Tests.CPP.WeaknessSanity
lake exe cpp_smoke
```

## Minimal usage example

```lean
import Mathlib.Data.Set.Lattice
import HeytingLean.CPP.All

open HeytingLean.CPP

def H : Set (Bool × Bool) := { (true, false) }

def μ : Bool → MeetQuantale (Set Bool)
  | true => (({true} : Set Bool) : MeetQuantale (Set Bool))
  | false => (({false} : Set Bool) : MeetQuantale (Set Bool))

#check weakness (H := H) μ

example : μ true * μ false ≤ weakness (H := H) μ := by
  apply mul_le_weakness (H := H) (μ := μ)
  simp [H]
```

## Docs

- `docs/TECHNICAL_REPORT.md`
- `docs/IMPLEMENTABLE_PLAN.md`

## Roadmap (small, high-confidence extensions)

- More “set algebra” for weakness (`iUnion`/`sUnion`, reindexing lemmas).
- A small bridge module specializing weakness computations to fixed-point sublocales (Ω-cores) in
  larger systems, without expanding the core API.
