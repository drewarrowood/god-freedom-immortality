import GodFreedomImmortality.Collapse

/-
# Freedom — two different types

**Contingency** (`ContingentR`, `ContingentAct`) is a Kripke reading:
the act holds here and fails at an accessible world. Under `Universal R`
plus Scott A1–A3 and A5R it is **impossible** (modal collapse). That is a
theorem. It is not Kant’s doctrine of freedom.

**Kantian practical freedom** (`KantPracticalFreedom`) is a postulate shape:
an agent can determine some act. It does not mention accessibility, and
nothing below derives it from Scott’s hypotheses. In the second *Critique*,
freedom is also bound up with the fact of the moral law (the *ratio essendi*
of that law), while God and immortality are introduced as postulates of
pure practical reason for the highest good. This module still does **not**
promote practical freedom to a theorem, and it does not identify it with
`ContingentR`.

Collapse therefore does not “refute Kantian freedom” in this package. It
refutes only the contingency reading, and only under Universal + Scott.
-/

namespace GodFreedomImmortality

/-- **Postulate shape, not a theorem, and not `ContingentR` / `ContingentAct`.**

`canDetermine a α` is an unanalyzed practical predicate (the agent can
determine act `α`). The postulate says that every agent determines some act.
Passing it as a hypothesis is adopting it; this definition does not assert it,
and Scott A1–A5 do not prove it. -/
def KantPracticalFreedom {Agent Act : Type}
    (canDetermine : Agent → Act → Prop) : Prop :=
  ∀ a : Agent, ∃ α : Act, canDetermine a α

/-- The postulate shape is not a contradiction. A one-agent, one-act witness
in which `canDetermine` is trivially true.

This is **not** a proof that anyone is free, and **not** a derivation from
`GodLike` or from `ContingentR`. -/
theorem KantPracticalFreedom_shape_satisfiable :
    KantPracticalFreedom (fun (_ : Unit) (_ : Unit) => True) :=
  fun _ => ⟨(), trivial⟩

/-- **Theorem (contingency reading).** Under Universal + Scott A1–A3 + A5R,
no individual act is `ContingentAct`.

Sobel collapse, re-checked here; see `Collapse.lean`. The Kantian postulate
is a different `Prop` and is not the thing ruled out. -/
theorem ContingentAct_impossible_under_Universal_Scott {W Ind : Type}
    (R : Access W) (hU : Universal R)
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA2 : A2 Positive)
    (hA3 : A3 Positive) (hA5 : A5R R Positive)
    (α : Property W Ind) (w : W) (x : Ind) :
    ¬ ContingentAct R α w x :=
  ContingentAct_impossible_of_universal R hU Positive hA1 hA2 hA3 hA5 α w x

/-- **Theorem.** The same package rules out `ContingentR` for an arbitrary
world-proposition, not only for acts. -/
theorem ContingentR_impossible_under_Universal_Scott {W Ind : Type}
    (R : Access W) (hU : Universal R)
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA2 : A2 Positive)
    (hA3 : A3 Positive) (hA5 : A5R R Positive)
    (φ : W → Prop) (w : W) :
    ¬ ContingentR R φ w :=
  ContingentR_incompatible_with_Universal_Scott R hU Positive hA1 hA2 hA3 hA5 φ w

end GodFreedomImmortality
