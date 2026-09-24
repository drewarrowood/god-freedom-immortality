import GodFreedomImmortality.Freedom
import GodFreedomImmortality.Immortality

/-
# The practical triad, jointly — not as three Scott theorems

Kant’s practical philosophy names three ideas together: **God**, **freedom**,
and **immortality** (*Critique of Practical Reason*, the dialectic of pure
practical reason). This module is the one place that imports all three
symbolizations used in this package.

| Piece | Status here |
| --- | --- |
| Scott A1, A2, A3, A5R, and `Universal R` | **Hypotheses.** From them, global God-likeness and the death of `ContingentR` are **theorems**. |
| `KantPracticalFreedom` | **Postulate shape.** Not `ContingentR`. Not derived from Scott. |
| `ImmortalityPostulate` (`Survives`) | **Postulate shape.** Not `GodLike` and not `NE`. Not derived from Scott. |

**Joint symbolization: yes** — `PracticalTriad` packages the Scott hypotheses
together with the two postulate shapes, and `practical_triad_toy` shows that
package is satisfiable in a trivial model.

**Three theorems under Scott + Universal + `ContingentR`: no** —
`PracticalTriad.excludes_ContingentR` / `ContingentR_incompatible_with_Universal_Scott`
say that adding contingency to Universal Scott is impossible. The freedom
slot in `PracticalTriad` is the Kantian postulate, which is why the toy
model can exist.

A toy inhabitant is a check that the joint `Prop`s are not already a
contradiction. It is not evidence that the postulates are true, and it is
not a metaphysical argument.
-/

namespace GodFreedomImmortality

/-- Joint signature of this package.

* Modal worlds (`W`, `R`) and Scott’s `Positive` are the ontological block.
* `Stage` / `later` / `present` are a **separate** order for persistence.
  They are not identified with `W` or with `R`.
* `canDetermine` is a **separate** practical vocabulary. It is not `ContingentAct`.

Nothing constructs a `PracticalTriad` from Scott’s hypotheses alone: the
postulate fields have to be supplied.
-/
structure PracticalTriad
    (W Ind Agent Act Person Stage : Type) (R : Access W) where
  Positive : Property W Ind → Prop
  scottA1 : A1 Positive
  scottA2 : A2 Positive
  scottA3 : A3 Positive
  /-- Scott’s A5 relativized to `R` (positivity of necessary existence along `R`). -/
  scottA5R : A5R R Positive
  /-- Frame hypothesis for the *global* ontological reading. -/
  universalFrame : Universal R
  canDetermine : Agent → Act → Prop
  /-- Postulate. Not a field of type `ContingentR`. -/
  freedomPostulate : KantPracticalFreedom canDetermine
  later : Stage → Stage → Prop
  present : Stage → Person → Prop
  /-- Postulate. Not a consequence of `scottA1`–`scottA5R`. -/
  immortalityPostulate : ImmortalityPostulate later present

/-- **Theorem.** A joint signature that includes Universal Scott cannot also
carry `ContingentR`. Contingency-as-freedom is the reading that collapse rules
out. `freedomPostulate` is not used, because it is not that reading. -/
theorem PracticalTriad.excludes_ContingentR
    {W Ind Agent Act Person Stage : Type} {R : Access W}
    (T : PracticalTriad W Ind Agent Act Person Stage R)
    (φ : W → Prop) (w : W) :
    ¬ ContingentR R φ w :=
  ContingentR_incompatible_with_Universal_Scott R T.universalFrame T.Positive
    T.scottA1 T.scottA2 T.scottA3 T.scottA5R φ w

/-- **Theorem.** The same exclusion for an individual-relative act. -/
theorem PracticalTriad.excludes_ContingentAct
    {W Ind Agent Act Person Stage : Type} {R : Access W}
    (T : PracticalTriad W Ind Agent Act Person Stage R)
    (α : Property W Ind) (w : W) (x : Ind) :
    ¬ ContingentAct R α w x :=
  ContingentAct_impossible_under_Universal_Scott R T.universalFrame T.Positive
    T.scottA1 T.scottA2 T.scottA3 T.scottA5R α w x

/-! ## Toy inhabitant

One modal world (so `universalRel` is universal and Scott A1–A3 + A5R hold),
one agent who “determines” a single trivial act, and `Nat` as a stage order
with `s < t`. The stage order is not the modal frame.
-/

namespace TriadToy

def Positive : Property Unit Unit → Prop := fun φ => φ () ()

theorem hA1 : A1 Positive := fun _ => Iff.rfl

theorem hA2 : A2 Positive := fun _ _ hφ hent => hent () () hφ

theorem hA3 : A3 Positive := fun _ h => h

theorem hA5R : A5R (universalRel Unit) Positive := by
  intro φ hEss v _hv
  cases v
  exact ⟨(), hEss.1⟩

def canDetermine : Unit → Unit → Prop := fun _ _ => True

theorem hFreedom : KantPracticalFreedom canDetermine := fun _ => ⟨(), trivial⟩

def later : Nat → Nat → Prop := fun s t => s < t

def present : Nat → Unit → Prop := fun _ _ => True

theorem hImmortality : ImmortalityPostulate later present := by
  intro _ s _
  exact ⟨s + 1, Nat.lt_succ_self s, trivial⟩

end TriadToy

/-- **Joint symbolization is formally satisfiable** in a toy model:
Universal Scott hypotheses, `KantPracticalFreedom`, and `ImmortalityPostulate`
together. See `PracticalTriad.excludes_ContingentR` for what this model
still cannot contain. -/
theorem practical_triad_toy :
    Nonempty (PracticalTriad Unit Unit Unit Unit Unit Nat (universalRel Unit)) :=
  ⟨{
    Positive := TriadToy.Positive
    scottA1 := TriadToy.hA1
    scottA2 := TriadToy.hA2
    scottA3 := TriadToy.hA3
    scottA5R := TriadToy.hA5R
    universalFrame := universalRel_is_universal Unit
    canDetermine := TriadToy.canDetermine
    freedomPostulate := TriadToy.hFreedom
    later := TriadToy.later
    present := TriadToy.present
    immortalityPostulate := TriadToy.hImmortality
  }⟩

/-- The toy signature symbolizes the triad and still excludes `ContingentR`. -/
theorem practical_triad_toy_excludes_ContingentR :
    ∀ φ : Unit → Prop, ∀ w : Unit,
      ¬ ContingentR (universalRel Unit) φ w := by
  intro φ w
  have ⟨T⟩ := practical_triad_toy
  exact T.excludes_ContingentR φ w

end GodFreedomImmortality
