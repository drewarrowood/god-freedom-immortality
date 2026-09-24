# NOTES

Design cuts for this seed. Desk craft: a joint *symbolization* of Kant’s triad
beside Scott’s ontological hypotheses, each claim labeled hypothesis, theorem,
or postulate. **Not a priority claim. Not published novelty.**

It is not a single Scott package in which God, freedom-as-contingency, and
immortality are all theorems.

**Joint symbolization: yes. Three theorems under Scott + Universal + `ContingentR`: no.**

Modal style: **rigid** `Positive` (`Property → Prop`; A4 absorbed), hypotheses
as `Prop`s in the theorem type (not global `axiom` commands), `□`/`◇` as `∀`/`∃`
when the frame is universal, and named `R` otherwise. No Mathlib. World-relative
`Positive` is not in this repository.

## Status (honest)

Checked and kept:

- Local T3 under `Symmetric R`, and collapse under `Universal R`, are
  **rediscoveries** of Benzmüller–Paleo (AFP `GoedelGod`) and of Sobel /
  Benzmüller et al. The proofs are in this thin rigid encoding. They are not
  a priority claim.
- Desk-only packaging: the four cuts below; `practical_triad_toy`; separation
  lemmas `scott_T3_without_Survives` and `S5_Scott_does_not_rule_out_ContingentR`.
- `#print axioms` (table below), Lean 4.34.0, no `sorry`, no `native_decide`.

Not claimed:

- Not “T3 in S5” as a slogan. Local and global are different theorems. Global
  needs `Universal` **under rigid `Positive`**.
- Not “the triad is proved.” `KantPracticalFreedom` and `ImmortalityPostulate`
  are postulate shapes.
- Not a fact about world-relative Positive or about Benzmüller–Scott HOML.
  Sister desk, different repo: [godel-ontological #1](https://github.com/drewarrowood/godel-ontological/pull/1).
  There, `countermodel_A_shape_dies_under_WRP` — the Bool / `idRel` global-T3-fail
  shape dies once Positive is world-relative. That module is not copied here.

Fair fail of a stronger claim: a literature twin for the packaging, an
isomorphic published model, or slogan text that says “T3 fails in S5” or
“Kant triad proved” without naming **rigid `Positive`**, **local ≠ global**,
and **`Universal` load-bearing**.

### `#print axioms` (2026-09-24, America/New_York)

Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, after `lake build`.
No `native_decide` (pin stays on 4.34.0; kernel issue
[#14576](https://github.com/leanprover/lean4/issues/14576)).

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

The classical trio tracks `Classical.byContradiction` in the Scott chain.
`S5_does_not_yield_global_T3` and `practical_triad_toy` are axiom-free.
The rigid S5 contingency countermodel depends only on `propext`.

### Slogan fail-points

- “T3 in S5” without rigid `Positive` and without local vs global `∀ w` / `Universal` → fail.
- “Triad proved”, or three theorems from Scott alone → fail. The freedom and immortality slots are postulate shapes.
- “Freedom survives under Universal Scott” if freedom means `ContingentR` → fail.
- Comfort-as-necessity satire is fair on **rigid + Universal** collapse. Unfair if aimed at WRP HOML, or at `KantPracticalFreedom`.

## Cut 1 — drop `Universal`

Keep A1–A3 and A5R. **Rigid `Positive` stays.** Replace `Universal R` by a weaker frame.

- **Local T3** still has a proof if `Symmetric R` is assumed
  (`local_T3_of_Symmetric`). Reflexivity is not used. Rediscovery of the
  Benzmüller–Paleo symmetry fact, in this encoding.
- **Global T3** is not a theorem of `S5Frame` **under rigid `Positive`**.
  Countermodel: `W = Bool`, `R = idRel`, rigid positivity = truth at `false`.
  God-like only at `false` (`S5_does_not_yield_global_T3`). This is global
  `∀ w`, not local T3. The same Bool / `idRel` shape is what the sister WRP
  stress test kills; that stress test is not a theorem of this repo.
- **`ContingentR`** is not ruled out by `S5Frame` **under rigid `Positive`**
  either. Countermodel: clusters `{a,b}` and `{c}`, rigid positivity = truth
  at `c`, contingency at `a` (`S5_Scott_does_not_rule_out_ContingentR`).
  Collapse still holds at the God-world; it does not hold on the other cluster.

Dropping universality is how **`ContingentR`** can sit beside the rigid Scott
hypotheses in this encoding. The global ontological reading is what gets
weaker. The Kant postulate `KantPracticalFreedom` does not need this cut: it
was never `ContingentR`.

## Cut 2 — drop an axiom

A3 and A5/A5R stay hypotheses. They are not restored as ambient axioms.
`Positive` stays rigid either way.

- **Drop A5 / A5R.** T1 and C do not use them (`T1_positive_possibly_exemplified`,
  `C_possibly_God`). Reflection, local T3, global T3, and collapse all have
  A5 or A5R in the type. There is no theorem here of the form
  `A1 → A2 → A3 → ∀ w ∃ x GodLike`.
- **Drop A3.** T1 still applies to an arbitrary positive property. C and both
  T3 theorems have A3 in the type. Without “God-likeness is positive” this
  package does not produce a God-like being.

Cutting an axiom keeps a fragment of the Scott chain without the necessity
theorem and without Sobel collapse. It is not a Kantian postulate, and it is
not a novelty claim.

## Cut 3 — rewrite essence (deferred) and WRP (not in this repo)

Collapse, as checked here, uses Scott’s essence **and rigid `Positive`**: a
God-like being has only positive properties (A1, rigidity), so a truth at that
world is entailed by God-likeness and is necessary along `R` once necessary
existence is positive.

Anderson- and Fitting-style emendations change essence or positivity so that
this Sobel step fails. Benzmüller and others have studied those repairs in
HOML. **This seed does not formalize them.** Scott’s `Essence` / `EssenceR`
are unchanged, so Universal + A1–A3 + A5R, with rigid `Positive`, still yields
`ModalCollapseR` and still excludes `ContingentR`.

**World-relative `Positive` is a different cut, and it is not formalized here.**
WRP would put A4 back as a real hypothesis (positivity indexed by a world).
Nothing in `GodFreedomImmortality/` defines `PosW`, `A4` as a world-relative
axiom, or a theorem that global T3 follows from `Symmetric` alone. The sister
package does that stress test: under WRP, `countermodel_A_shape_dies_under_WRP`
([godel-ontological #1](https://github.com/drewarrowood/godel-ontological/pull/1),
`COUNTERMODEL_A.md` §F). Universal is load-bearing for global T3 **in the rigid
encoding of this repo**. It is not load-bearing in that WRP module. Do not
export the rigid countermodels as a claim about HOML.

## Cut 4 — redefine freedom

This is the cut the triad symbolization actually uses. It is desk packaging.

`ContingentR` / `ContingentAct` mean “true here, false at an accessible
world”. Under Universal + rigid Scott that impossibility is a **theorem**
(rediscovery of collapse).

`KantPracticalFreedom canDetermine` means “every agent determines some act”,
with `canDetermine` unanalyzed. It does not mention `R`. Collapse does not
apply to it. `PracticalTriad` stores the postulate, not a `ContingentR`
witness, which is why `practical_triad_toy` can inhabit the joint signature
while `PracticalTriad.excludes_ContingentR` still holds.

Immortality is the same kind of stub, not a derivation:
`Survives` is a person along a stage order, assumed via
`ImmortalityPostulate` if one wants it, and `Stage` is not identified with
the modal world type. Likeness (`GodLike`) and necessary existence (`NE`)
are different predicates. `scott_T3_without_Survives` is the separation
lemma: universal-encoding T3 can hold while `Survives` fails. There is no
further immortality proof. Inventing a likeness is not one.

## Status of the four cuts

| Cut | Formalized here as |
| --- | --- |
| Drop Universal | Theorems with `Universal` in the type, plus the two **rigid** S5 countermodels |
| Cut A3 or A5/A5R | Those hypotheses appear in the types that need them; T1/C omit A5 |
| Rewrite essence | Not formalized; rigid Scott essence still collapses under Universal |
| World-relative Positive | Not formalized; sister PR shows the Bool/`idRel` T3-fail shape dies under WRP |
| Redefine freedom (and do not derive immortality) | `KantPracticalFreedom`, `Survives`, `PracticalTriad` |
