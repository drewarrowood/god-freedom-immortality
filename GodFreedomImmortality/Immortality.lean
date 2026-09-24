import GodFreedomImmortality.God

/-
# Immortality — a persistence postulate

Scott’s package does not define immortality. This module names one:

* `Survives later present p s` — person `p`, present at stage `s`, is still
  present at some stage strictly related by `later`.
* `ImmortalityPostulate` — every present person survives.

That is a **hypothesis shape**. It is not a theorem of A1–A5, and it is not
a rephrasing of `GodLike` or of `NE`.

`GodLike` is a likeness: having every positive property at a world.
`NE` is exemplification of an essence at accessible worlds.
Neither mentions a person or a stage order. Inventing a likeness is not an
immortality proof. `scott_T3_without_Survives` is a one-world Scott model
in which the universal-encoding necessity theorem holds (`□ ∃x GodLike x`)
and a present person still fails to survive.
-/

namespace GodFreedomImmortality

/-- **Persistence.** `p` survives stage `s` when some `later` stage still
presents `p`.

`later` and `present` are parameters. The definition does not assert that
anyone survives, and it does not consult `Positive` or `GodLike`. -/
def Survives {Person Stage : Type}
    (later : Stage → Stage → Prop)
    (present : Stage → Person → Prop)
    (p : Person) (s : Stage) : Prop :=
  ∃ t : Stage, later s t ∧ present t p

/-- **Postulate shape (Kantian immortality), not a theorem of Scott.**

Whoever is present survives along `later`. Kant’s postulate in the second
*Critique* is the endless duration of the soul required for moral progress
toward holiness. This is only the persistence skeleton of that idea: a
person-identity claim across a stage order. It is not derived from
`GodLike`, and a proof of it is not offered. -/
def ImmortalityPostulate {Person Stage : Type}
    (later : Stage → Stage → Prop)
    (present : Stage → Person → Prop) : Prop :=
  ∀ p : Person, ∀ s : Stage, present s p → Survives later present p s

/-- The postulate shape is not a contradiction: on `Nat` with `s < t`,
everyone present (here: everyone, at every stage) survives.

This does **not** prove that any soul is immortal, and it does not use
Scott’s hypotheses. -/
theorem ImmortalityPostulate_shape_satisfiable :
    ImmortalityPostulate (fun s t : Nat => s < t)
      (fun (_ : Nat) (_ : Unit) => True) := by
  intro _ s _
  exact ⟨s + 1, Nat.lt_succ_self s, trivial⟩

/-! ## Likeness is not survival

One world, one individual, Scott A1–A5 in the universal encoding (so
`T3_necessarily_God` applies), and a separate person who is present at the
only stage but for whom `later` never holds. Necessity of a God-like being
comes out true; `Survives` comes out false.
-/

namespace LikenessCountermodel

abbrev W := Unit
abbrev Ind := Unit
abbrev Person := Unit
abbrev Stage := Unit

def Positive : Property W Ind → Prop := fun φ => φ () ()

def later : Stage → Stage → Prop := fun _ _ => False

def present : Stage → Person → Prop := fun _ _ => True

theorem hA1 : A1 Positive := fun _ => Iff.rfl

theorem hA2 : A2 Positive := fun _ _ hφ hent => hent () () hφ

theorem hA3 : A3 Positive := fun _ h => h

theorem hA5 : A5 Positive := by
  intro φ hEss v
  cases v
  exact ⟨(), hEss.1⟩

theorem necessity_of_God :
    □ (fun w : W => ∃ x : Ind, GodLike Positive w x) :=
  T3_necessarily_God Positive hA1 hA2 hA3 hA5

theorem person_is_present : present () () := trivial

theorem person_does_not_survive : ¬ Survives later present () () := by
  intro ⟨_, hLater, _⟩
  exact hLater

end LikenessCountermodel

/-- **Not a theorem of Scott.** The universal-encoding necessity claim can
hold while a present person fails `Survives`.

`GodLike` / `NE` are not an immortality proof. -/
theorem scott_T3_without_Survives :
    A1 LikenessCountermodel.Positive ∧
    A2 LikenessCountermodel.Positive ∧
    A3 LikenessCountermodel.Positive ∧
    A5 LikenessCountermodel.Positive ∧
    □ (fun w : LikenessCountermodel.W =>
        ∃ x : LikenessCountermodel.Ind, GodLike LikenessCountermodel.Positive w x) ∧
    LikenessCountermodel.present () () ∧
    ¬ Survives LikenessCountermodel.later LikenessCountermodel.present () () :=
  ⟨LikenessCountermodel.hA1, LikenessCountermodel.hA2,
    LikenessCountermodel.hA3, LikenessCountermodel.hA5,
    LikenessCountermodel.necessity_of_God,
    LikenessCountermodel.person_is_present,
    LikenessCountermodel.person_does_not_survive⟩

end GodFreedomImmortality
