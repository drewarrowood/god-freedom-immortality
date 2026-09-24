# God, freedom, immortality

Desk craft: a didactic Lean 4 joint symbolization of Kant’s practical triad beside Scott’s emendation of Gödel’s ontological argument. **Not a priority claim. Not published novelty.**

**Joint symbolization: yes. Three theorems under Scott + Universal + `ContingentR`: no.**

`PracticalTriad` (`GodFreedomImmortality/Triad.lean`) is one signature with all three names in it. A toy inhabitant shows that signature is satisfiable. The freedom slot is the postulate shape `KantPracticalFreedom`, which is a different `Prop` from `ContingentR`. Under **rigid** `Positive`, adding `ContingentR` to Scott’s hypotheses on a **universal** frame is impossible (modal collapse). That incompatibility is a theorem about contingency. It leaves the postulate slot alone.

Lean checks implications in a thin encoding. It does not decide metaphysics, theology, or whether anyone is free or immortal.

## Status (honest)

What this seed is: joint symbolization, with each piece marked hypothesis, theorem, or postulate. What it is not: a published result, a priority claim, or three theorems of one Scott package.

**Rediscovery** (already in the literature; say so in the open):

- Local T3 under `Symmetric R` — Benzmüller–Paleo, AFP [`GoedelGod`](https://www.isa-afp.org/entries/GoedelGod.html). Symmetry suffices for the necessity step.
- Collapse under `Universal R` (hence `ContingentR` / `ContingentAct` die) — Sobel; Benzmüller et al. on Scott-style collapse.

**Desk packaging only** (this repository’s arrangement, not a novelty claim):

- Named cuts: drop `Universal`; cut A3 or A5/A5R; rewrite essence (deferred; not formalized); redefine freedom as `KantPracticalFreedom`.
- `practical_triad_toy` — the joint signature has a toy inhabitant.
- Separation lemmas: `scott_T3_without_Survives`; `S5_Scott_does_not_rule_out_ContingentR` (rigid `Positive`, S5 frame, not `Universal`).

**Fair fail** of any stronger claim: a literature twin for that packaging claim, an isomorphic published model, or slogan text that says “T3 fails in S5” or “Kant triad proved” without naming **rigid `Positive`**, **local ≠ global**, and **`Universal` load-bearing**.

### Rigid `Positive` (A4 absorbed)

`Positive : Property → Prop` does not take a world. Scott’s A4 is not a separate hypothesis. Every S5 / T3 / `ContingentR` countermodel in this repo is a fact about **that** rigidity:

- `S5_does_not_yield_global_T3` — `Bool`, `idRel`, rigid positivity “true at `false`”. Global `∀ w ∃ GodLike` fails. Local T3 is not the claim that fails.
- `S5_Scott_does_not_rule_out_ContingentR` — two S5 clusters, rigid positivity “true at `c`”. `ContingentR` holds off the God-cluster.

World-relative `Positive` (WRP) is **not** formalized here. On the sister desk, the Bool / `idRel` global-T3-fail shape **dies** under WRP (`countermodel_A_shape_dies_under_WRP`): [godel-ontological PR #1](https://github.com/drewarrowood/godel-ontological/pull/1). Packaging sister, different repository. These modules were not copied across. Do not read the countermodels above as facts about Benzmüller–Scott HOML (world-relative positivity, per-world validity).

### `#print axioms`

Lean **4.34.0** (`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`), **2026-09-24, America/New_York**, after `lake build`. No `native_decide` (this pin stays on 4.34.0; kernel issue [#14576](https://github.com/leanprover/lean4/issues/14576) is why). No `sorry`.

| Theorem | Axioms |
| --- | --- |
| `local_T3_of_Symmetric` | `propext`, `Classical.choice`, `Quot.sound` |
| `T3R_necessarily_God_of_universal` | `propext`, `Classical.choice`, `Quot.sound` |
| `T3_necessarily_God` | `propext`, `Classical.choice`, `Quot.sound` |
| `ModalCollapseR_of_universal` | `propext`, `Classical.choice`, `Quot.sound` |
| `ContingentR_incompatible_with_Universal_Scott` | `propext`, `Classical.choice`, `Quot.sound` |
| `scott_T3_without_Survives` | `propext`, `Classical.choice`, `Quot.sound` |
| `practical_triad_toy_excludes_ContingentR` | `propext`, `Classical.choice`, `Quot.sound` |
| `S5_Scott_does_not_rule_out_ContingentR` | `propext` |
| `S5_does_not_yield_global_T3` | *none* |
| `practical_triad_toy` | *none* |

The classical trio is the footprint of `Classical.byContradiction` on the Scott chain (T1, and the “only positive properties” step into local T3). The two axiom-free rows are the rigid global-T3 countermodel and the toy signature. The S5 contingency countermodel uses only `propext`.

### Slogan fail-points

- “T3 in S5” without **rigid `Positive`** and without saying whether the claim is local or global `∀ w` / `Universal` → **fail**.
- “Triad proved”, or three theorems from Scott alone → **fail**. `KantPracticalFreedom` and `ImmortalityPostulate` are postulate shapes.
- “Freedom survives under Universal Scott” when freedom means `ContingentR` → **fail**. That package rules `ContingentR` out.
- Comfort-as-necessity satire is fair against **rigid + Universal** collapse. It is unfair aimed at WRP HOML, or at the Kant postulate slot (`KantPracticalFreedom`), which is not `ContingentR`.

## Build

[Lean 4](https://lean-lang.org/) **4.34.0**, pinned in `lean-toolchain`. No Mathlib.

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source "$HOME/.elan/env"
lake build
```

`lake build` succeeds with no `sorry` in the library.

## `sorry`

None. There is no open conjecture left as `sorry` in this seed. Postulates are hypothesis shapes (`Prop`s you may assume), not `sorry` and not global `axiom` commands.

## Proved, assumed, postulated

| | What | Where |
| --- | --- | --- |
| **Assumed** (hypotheses in the theorem type, not ambient axioms) | Scott **A1**, **A2**, **A3**. **A4** is not a separate hypothesis: `Positive` is rigid, so positivity does not vary by world. **A5** is positivity of necessary existence in the encoding where `□` is `∀` worlds. **A5R** is the same idea along an explicit relation `R`. | `God.lean` |
| **Assumed** when the theorem says so | **`Symmetric R`** (Brouwerian / axiom B) for *local* necessity. **`Universal R`** for *global* necessity and for the death of `ContingentR`. Both sit on **rigid** `Positive`. | `God.lean`, `Collapse.lean` |
| **Proved** from A1–A2 | **T1.** A positive property is exemplified at some world. | `T1_positive_possibly_exemplified` |
| **Proved** from A1–A3 | **C.** Some world has a God-like being. A5 is not used. | `C_possibly_God` |
| **Proved** from A1 | **T2.** God-likeness is an essence of a God-like being. | `T2_godlike_essence`, `T2R_godlike_essence` |
| **Proved** from A1 + A5R, no frame hypothesis | Local reflection: God at `w` ⇒ God at every `R`-successor. | `exists_God_implies_necessaryR` |
| **Proved** from A1 + A5R + **`Symmetric R`** | **Local T3.** `possibleR (∃ GodLike) → necessaryR (∃ GodLike)` at that world. Symmetry suffices. Benzmüller–Paleo (AFP [`GoedelGod`](https://www.isa-afp.org/entries/GoedelGod.html)) already had this; the lemma here is a rediscovery, not a priority claim. | `local_T3_of_Symmetric` |
| **Proved** from A1–A3 + A5R + **`Universal R`**, rigid `Positive` | **Global T3.** A God-like being at every world. `Universal` is load-bearing for this global claim in this encoding; `S5Frame` is not a substitute (countermodel below). | `T3R_necessarily_God_of_universal` |
| **Proved** from A1–A3 + A5 in the universal encoding | **T3** with `□ ≜ ∀ w`, **rigid** `Positive`. The box already quantifies over every world. This is the global reading. It is not the slogan “T3 in S5”. | `T3_necessarily_God` |
| **Proved** (countermodel, rigid `Positive`) | **S5 does not yield global T3.** Identity on `Bool` is an S5 frame, not universal; A1–A3 and A5R hold; God-likeness fails at one world. Local T3 is not what fails. WRP is not this theorem; the sister desk’s WRP stress test makes the Bool/`idRel` shape die. | `S5_does_not_yield_global_T3` |
| **Proved** from Universal + A1–A3 + A5R, rigid `Positive` | **Modal collapse**, hence **`ContingentR` and `ContingentAct` are impossible**. Sobel; Benzmüller et al. Rediscovery. | `ModalCollapseR_of_universal`, `ContingentR_incompatible_with_Universal_Scott` |
| **Proved** (countermodel, rigid `Positive`) | **Without `Universal`, `ContingentR` can remain.** Two S5 clusters; A1–A3 and A5R hold; `ContingentR` holds off the God-cluster. | `S5_Scott_does_not_rule_out_ContingentR` |
| **Proved** (separation) | **Likeness is not immortality.** A one-world Scott model satisfies `□ ∃x GodLike x` while a present person fails `Survives`. | `scott_T3_without_Survives` |
| **Proved** (toy) | The joint signature (Universal Scott + both postulate shapes) has an inhabitant, and that inhabitant still excludes `ContingentR`. | `practical_triad_toy`, `practical_triad_toy_excludes_ContingentR` |
| **Postulate** (not a theorem) | **`KantPracticalFreedom`**: every agent can determine some act. Not defined as `ContingentR`. Not derived from Scott. A `Unit` witness only shows the shape is not a contradiction. | `Freedom.lean` |
| **Postulate** (not a theorem) | **`ImmortalityPostulate`**: a present person `Survives` along a stage order (`later`, `present`). Not derived from `GodLike` or from `NE`. A `Nat` witness only shows the shape is not a contradiction. | `Immortality.lean` |

## Kant and Scott

These are different arguments, symbolized in one repository so the difference stays visible.

- **Scott / Gödel (theoretical, ontological).** From hypotheses about *positive properties*, a *God-like* being (one that has every positive property), and *necessary existence*, one asks whether `∃x GodLike x` is necessary. This package follows Scott’s emendation: A3 says God-likeness is positive, A5 says necessary existence is positive, positivity is rigid. See Scott’s notes on Gödel’s ontological argument, and Gödel’s own notes (c. 1941 / early 1970s).
- **Kant (practical).** In the *Critique of Practical Reason* (1788), the dialectic of pure practical reason treats **freedom**, the **immortality of the soul**, and the **existence of God** as ideas required for the moral law and the highest good — not as theorems scraped out of an ontological axiom set. Freedom is also tied, earlier in that book, to the fact of the moral law. This repository still marks practical freedom as a **postulate stub**, because it is not a theorem here and it is not `ContingentR`.

`GodLike` is a likeness predicate on individuals-at-worlds. `Survives` is person-identity across a stage order that need not be the modal frame (`PracticalTriad` keeps `Stage` and `W` separate). **Inventing a likeness is not an immortality proof.** Necessary existence (`NE` / `NER`) says an essence is exemplified at accessible worlds; that is not the postulate that a person persists.

## Layout

```
GodFreedomImmortality.lean               library root; imports the joint module
GodFreedomImmortality/Modal.lean         □ / ◇, and R, necessaryR, possibleR, frame conditions
GodFreedomImmortality/God.lean           Scott A1–A5 / A5R, local and global T3, S5 countermodel
GodFreedomImmortality/Collapse.lean      modal collapse, ContingentR, contingency countermodel
GodFreedomImmortality/Freedom.lean       ContingentAct theorem vs KantPracticalFreedom postulate
GodFreedomImmortality/Immortality.lean   Survives / ImmortalityPostulate; separation from Scott
GodFreedomImmortality/Triad.lean         joint signature and the incompatibility theorem
NOTES.md                                 cuts: drop Universal, cut an axiom, rewrite essence, redefine freedom
```

Import the joint statement with `import GodFreedomImmortality.Triad`.

## Literature

- Immanuel Kant, *Kritik der praktischen Vernunft* (1788), dialectic of pure practical reason: the postulates.
- Kurt Gödel, ontological-proof manuscripts / notes.
- Dana Scott, notes on Gödel’s ontological argument (the emendation used here).
- J. H. Sobel, modal collapse for Gödel/Scott premises (*Logic and Theism*, and the 1987 discussion).
- C. Benzmüller and B. Wenzel Paleo, mechanization of Gödel’s argument; Archive of Formal Proofs entry `GoedelGod` (symmetry suffices for the necessity theorem). Isabelle/HOL, not a dependency of this project.
- C. Benzmüller and others on Scott-style collapse and on Anderson/Fitting repairs that avoid it. Those repairs are **not** formalized in this seed; see NOTES.md.
- Sister desk (different repository; modules not copied): [godel-ontological PR #1](https://github.com/drewarrowood/godel-ontological/pull/1), `COUNTERMODEL_A.md` — rigid Countermodel A, and `countermodel_A_shape_dies_under_WRP`.
