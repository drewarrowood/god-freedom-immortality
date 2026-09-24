# NOTES

Design cuts for this seed. The aim is a joint *symbolization* of Kant’s triad
beside Scott’s ontological hypotheses, with each claim labeled hypothesis,
theorem, or postulate. It is not a single Scott package in which God,
freedom-as-contingency, and immortality are all theorems.

Modal style follows a thin encoding: rigid `Positive`, axioms as `Prop`s in
the theorem type (not global `axiom`s), `□`/`◇` as `∀`/`∃` when the frame is
universal, and named `R` otherwise. No Mathlib.

## What is deliberately not claimed

- Local necessity (`possibleR ∃GodLike → necessaryR ∃GodLike`) is proved under
  **`Symmetric R`**. That symmetry suffices was already in Benzmüller–Paleo,
  AFP `GoedelGod`. Rediscovery only.
- Global necessity and the death of `ContingentR` need **`Universal R`**
  (or the universal encoding, where `□` is already `∀ w`). `S5Frame` is not
  a substitute: `S5_does_not_yield_global_T3`,
  `S5_Scott_does_not_rule_out_ContingentR`.
- `KantPracticalFreedom` and `ImmortalityPostulate` are postulate shapes.
  Toy witnesses (`Unit`, `Nat`) show only that those `Prop`s are not
  contradictions by themselves.
- `GodLike` does not mention persons or stages. `scott_T3_without_Survives`
  satisfies Scott’s universal-encoding T3 and still falsifies `Survives`.

## Cut 1 — drop `Universal`

Keep A1–A3 and A5R. Replace `Universal R` by a weaker frame.

- **Local T3** still has a proof if `Symmetric R` is assumed
  (`local_T3_of_Symmetric`). Reflexivity is not used.
- **Global T3** is not a theorem of `S5Frame`. Countermodel: `Bool` with
  the identity relation, positivity = truth at `false`. God-like only at
  `false`.
- **`ContingentR`** is not ruled out by `S5Frame` either. Countermodel:
  clusters `{a,b}` and `{c}`, God-like only at `c`, contingency at `a`.
  Collapse still holds *at the God-world*; it does not hold on the other
  cluster.

Dropping universality is how contingency-as-freedom can coexist with the
Scott hypotheses in this encoding. The global ontological reading is what
gets weaker.

## Cut 2 — drop an axiom

A3 and A5/A5R stay hypotheses. They are not restored as ambient axioms.

- **Drop A5 / A5R.** T1 and C do not use them (`T1_positive_possibly_exemplified`,
  `C_possibly_God`). Reflection, local T3, global T3, and collapse all have
  A5 or A5R in the type. There is no theorem here of the form
  `A1 → A2 → A3 → ∀ w ∃ x GodLike`.
- **Drop A3.** T1 still applies to an arbitrary positive property. C and both
  T3 theorems have A3 in the type. Without “God-likeness is positive” this
  package does not produce a God-like being.

Cutting an axiom is a way to keep a fragment of the Scott chain without the
necessity theorem and without Sobel collapse. It is not a Kantian postulate.

## Cut 3 — rewrite essence

Collapse, as checked here, uses Scott’s essence: a God-like being has only
positive properties (A1, rigidity), so any truth at that world is entailed
by God-likeness and is necessary along `R` once necessary existence is positive.

Anderson- and Fitting-style emendations change essence or positivity so that
this Sobel step fails. Benzmüller and others have studied those repairs in
HOML. **This seed does not formalize them.** Scott’s `Essence` / `EssenceR`
are unchanged, so Universal + A1–A3 + A5R still yields
`ModalCollapseR` and still excludes `ContingentR`.

A world-relative (non-rigid) `Positive`, which would put A4 back as a real
hypothesis, is also not developed here.

## Cut 4 — redefine freedom

This is the cut the triad actually uses.

`ContingentR` / `ContingentAct` mean “true here, false at an accessible
world”. Under Universal + Scott that is a **theorem of impossibility**.

`KantPracticalFreedom canDetermine` means “every agent determines some act”,
with `canDetermine` unanalyzed. It does not mention `R`. Collapse does not
apply to it. `PracticalTriad` stores the postulate, not a `ContingentR`
witness, which is why `practical_triad_toy` can inhabit the joint signature
while `PracticalTriad.excludes_ContingentR` still holds.

Immortality is handled the same way rather than by a fake derivation:
`Survives` is a person along a stage order, assumed via
`ImmortalityPostulate` if one wants it, and `Stage` is not identified with
the modal world type. Likeness (`GodLike`) and necessary existence (`NE`)
stay different predicates. That is the whole of the immortality content;
there is no further proof.

## Status of the four cuts

| Cut | Formalized here as |
| --- | --- |
| Drop Universal | Theorems with `Universal` in the type, plus the two S5 countermodels |
| Cut A3 or A5/A5R | Those hypotheses appear in the types that need them; T1/C omit A5 |
| Rewrite essence | Not formalized; collapse stands for Scott’s essence |
| Redefine freedom (and do not derive immortality) | `KantPracticalFreedom`, `Survives`, `PracticalTriad` |
