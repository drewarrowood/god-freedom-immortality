# God, freedom, immortality

A small Lean 4 project that **jointly symbolizes** Kant’s practical triad — God, freedom, and immortality — next to Dana Scott’s emendation of Gödel’s ontological argument.

**Joint symbolization: yes. Three theorems under Scott + Universal + `ContingentR`: no.**

`PracticalTriad` (`GodFreedomImmortality/Triad.lean`) is one signature with all three names in it. A toy inhabitant shows that signature is not already a contradiction. The freedom slot in that signature is a Kantian postulate, not the Kripke contingency predicate `ContingentR`. Adding `ContingentR` to Scott’s hypotheses on a **universal** frame is impossible (modal collapse). That incompatibility is a theorem. It is not a refutation of the postulate.

Lean checks implications in a thin modal encoding. It does not decide metaphysics, theology, or whether anyone is free or immortal.

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
| **Assumed** when the theorem says so | **`Symmetric R`** (Brouwerian / axiom B) for *local* necessity. **`Universal R`** for *global* necessity and for the death of `ContingentR`. | `God.lean`, `Collapse.lean` |
| **Proved** from A1–A2 | **T1.** A positive property is exemplified at some world. | `T1_positive_possibly_exemplified` |
| **Proved** from A1–A3 | **C.** Some world has a God-like being. A5 is not used. | `C_possibly_God` |
| **Proved** from A1 | **T2.** God-likeness is an essence of a God-like being. | `T2_godlike_essence`, `T2R_godlike_essence` |
| **Proved** from A1 + A5R, no frame hypothesis | Local reflection: God at `w` ⇒ God at every `R`-successor. | `exists_God_implies_necessaryR` |
| **Proved** from A1 + A5R + **`Symmetric R`** | **Local T3.** `possibleR (∃ GodLike) → necessaryR (∃ GodLike)` at that world. Symmetry suffices. Benzmüller–Paleo (AFP [`GoedelGod`](https://www.isa-afp.org/entries/GoedelGod.html)) already had this; the lemma here is a rediscovery, not a priority claim. | `local_T3_of_Symmetric` |
| **Proved** from A1–A3 + A5R + **`Universal R`** | **Global T3.** A God-like being at every world. | `T3R_necessarily_God_of_universal` |
| **Proved** from A1–A3 + A5 in the universal encoding | **T3** with `□ ≜ ∀ w`. The box already quantifies over every world, so this is the global reading, not “T3 in S5”. | `T3_necessarily_God` |
| **Proved** (countermodel) | **S5 does not yield global T3.** Identity on `Bool` is an S5 frame, not universal; A1–A3 and A5R hold; God-likeness fails at one world. | `S5_does_not_yield_global_T3` |
| **Proved** from Universal + A1–A3 + A5R | **Modal collapse**, hence **`ContingentR` and `ContingentAct` are impossible**. Sobel; Benzmüller et al. Rediscovery, not a priority claim. | `ModalCollapseR_of_universal`, `ContingentR_incompatible_with_Universal_Scott` |
| **Proved** (countermodel) | **Without `Universal`, contingency can remain.** Two S5 clusters; A1–A3 and A5R hold; `ContingentR` holds off the God-cluster. | `S5_Scott_does_not_rule_out_ContingentR` |
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
