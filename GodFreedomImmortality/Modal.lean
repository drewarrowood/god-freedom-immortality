/-
# Minimal modal vocabulary

Two layers, kept visibly distinct:

* **Universal encoding.** `□ φ` is `∀ w, φ w` and `◇ φ` is `∃ w, φ w`.
  That is universal accessibility baked into the quantifiers. It is a valid
  S5 frame, and it is strictly stronger than “S5” (an equivalence relation
  may have more than one cluster).
* **Named accessibility.** `necessaryR` / `possibleR` take an explicit
  relation `R`. Frame conditions (`Symmetric`, `Universal`, `S5Frame`, …)
  are ordinary `Prop`s, so a theorem that needs one must put it in the type.

No Mathlib. No metaphysical reading of `□`.
-/

namespace GodFreedomImmortality

/-- Necessity on a world-proposition: true at every world. -/
def necessary {W : Type} (φ : W → Prop) : Prop :=
  ∀ w : W, φ w

/-- Possibility on a world-proposition: true at some world. -/
def possible {W : Type} (φ : W → Prop) : Prop :=
  ∃ w : W, φ w

/-- Box notation for necessity in the universal encoding. -/
prefix:max "□" => necessary

/-- Diamond notation for possibility in the universal encoding. -/
prefix:max "◇" => possible

/-- A property of individuals, evaluated relative to a world (an intension). -/
abbrev Property (W Ind : Type) := W → Ind → Prop

/-- Negation of a property (pointwise). -/
def propNeg {W Ind : Type} (φ : Property W Ind) : Property W Ind :=
  fun w x => ¬ φ w x

/-- The unsatisfiable property. -/
def propFalse {W Ind : Type} : Property W Ind :=
  fun _ _ => False

/-- The universal (always-true) property. -/
def propTrue {W Ind : Type} : Property W Ind :=
  fun _ _ => True

/-- Necessary entailment under universal accessibility: `□ ∀x (φ x → ψ x)`. -/
def necEntails {W Ind : Type} (φ ψ : Property W Ind) : Prop :=
  ∀ w : W, ∀ x : Ind, φ w x → ψ w x

theorem necEntails_false_of_nowhere {W Ind : Type} (φ : Property W Ind)
    (h : ∀ w : W, ∀ x : Ind, ¬ φ w x) :
    necEntails φ (propFalse : Property W Ind) := by
  intro w x hφ
  exact (h w x) hφ

theorem necEntails_true {W Ind : Type} (φ : Property W Ind) :
    necEntails φ (propTrue : Property W Ind) := by
  intro _ _ _; trivial

@[simp] theorem propNeg_true {W Ind : Type} :
    propNeg (propTrue : Property W Ind) = propFalse := by
  funext w x; simp [propNeg, propTrue, propFalse]

/-! ## Accessibility -/

/-- Accessibility relation on worlds. -/
abbrev Access (W : Type) := W → W → Prop

/-- Necessity at `w` along `R`: true at every `R`-successor of `w`. -/
def necessaryR {W : Type} (R : Access W) (φ : W → Prop) (w : W) : Prop :=
  ∀ v : W, R w v → φ v

/-- Possibility at `w` along `R`: true at some `R`-successor of `w`. -/
def possibleR {W : Type} (R : Access W) (φ : W → Prop) (w : W) : Prop :=
  ∃ v : W, R w v ∧ φ v

/-- Reflexivity (modal T). -/
def Reflexive {W : Type} (R : Access W) : Prop :=
  ∀ w : W, R w w

/-- Symmetry (modal B, the Brouwerian frame condition). -/
def Symmetric {W : Type} (R : Access W) : Prop :=
  ∀ w v : W, R w v → R v w

/-- Euclidean: `R w v → R w u → R v u`. With reflexivity, this is an S5 frame. -/
def Euclidean {W : Type} (R : Access W) : Prop :=
  ∀ w v u : W, R w v → R w u → R v u

/-- Universal (total) accessibility: every world sees every world. -/
def Universal {W : Type} (R : Access W) : Prop :=
  ∀ w v : W, R w v

/-- Brouwerian frame condition. Alias of `Symmetric` (axiom B: `φ → □◇φ`). -/
abbrev Brouwerian {W : Type} (R : Access W) : Prop :=
  Symmetric R

/-- S5 frame: reflexive and Euclidean (hence also symmetric and transitive). -/
def S5Frame {W : Type} (R : Access W) : Prop :=
  Reflexive R ∧ Euclidean R

theorem Universal.symmetric {W : Type} {R : Access W} (h : Universal R) :
    Symmetric R := fun w v _ => h v w

theorem Universal.reflexive {W : Type} {R : Access W} (h : Universal R) :
    Reflexive R := fun w => h w w

theorem Universal.euclidean {W : Type} {R : Access W} (h : Universal R) :
    Euclidean R := fun _w v u _ _ => h v u

theorem Universal.s5 {W : Type} {R : Access W} (h : Universal R) : S5Frame R :=
  ⟨h.reflexive, h.euclidean⟩

/-- Reflexive + Euclidean ⇒ symmetric. -/
theorem S5Frame.symmetric {W : Type} {R : Access W} (h : S5Frame R) :
    Symmetric R := by
  intro w v hwv
  exact h.2 w v w hwv (h.1 w)

/-- The constantly-true relation. -/
def universalRel (W : Type) : Access W := fun _ _ => True

theorem universalRel_is_universal (W : Type) : Universal (universalRel W) :=
  fun _ _ => trivial

/-- Identity accessibility. An S5 frame; not universal once there are two worlds. -/
def idRel (W : Type) : Access W := fun w v => w = v

theorem idRel_reflexive (W : Type) : Reflexive (idRel W) := fun _ => rfl

theorem idRel_symmetric (W : Type) : Symmetric (idRel W) := fun _ _ h => h.symm

theorem idRel_euclidean (W : Type) : Euclidean (idRel W) :=
  fun _ _ _ hwv hwu => hwv.symm.trans hwu

theorem idRel_s5 (W : Type) : S5Frame (idRel W) :=
  ⟨idRel_reflexive W, idRel_euclidean W⟩

end GodFreedomImmortality
