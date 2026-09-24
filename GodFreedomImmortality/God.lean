import GodFreedomImmortality.Modal

/-
# Scott’s emendation, as hypotheses

Dana Scott’s reading of Gödel’s ontological-proof notes, in the thin style
of a universal-frame encoding plus an explicit accessibility relation.

**Honesty.** Lean checks implications. `A1`–`A5` / `A5R` are hypotheses in
the theorem types, not facts about the world, and not Kant’s postulate of
God. A proved `□ ∃x GodLike x` is not a metaphysical existence claim.

Rigid `Positive : Property → Prop` absorbs Scott’s **A4** (`P(φ) → □ P(φ)`):
positivity does not vary with the world, so A4 is not a separate hypothesis.

What the necessity theorem needs, in this file:

* **Local** `possibleR (∃ GodLike) → necessaryR (∃ GodLike)` at a world:
  `Symmetric R` (Brouwerian / axiom B). Reflexivity is not used.
  Benzmüller–Paleo (AFP `GoedelGod`) already showed that symmetry suffices
  for this step. The lemma below is a rediscovery in a thin encoding, not
  a priority claim.
* **Global** `∀ w, ∃ x, GodLike w x`: `Universal R`. An S5 frame is not
  enough; `FrameCountermodel` is a two-world identity frame (S5, not
  universal) in which A1–A3 and A5R hold and God-likeness fails at a world.
-/

namespace GodFreedomImmortality

/-! ## Definitions -/

/-- **D1.** God-like at a world: possesses every positive property there.

This is a *likeness* (a bundle of positive properties). It does not mention
persons, a time order, or survival. See `Immortality.lean`. -/
def GodLike {W Ind : Type} (Positive : Property W Ind → Prop) : Property W Ind :=
  fun w x => ∀ φ : Property W Ind, Positive φ → φ w x

/-- **D2.** Essence in the universal encoding (`□` = all worlds). -/
def Essence {W Ind : Type} (φ : Property W Ind) (w : W) (x : Ind) : Prop :=
  φ w x ∧ ∀ ψ : Property W Ind, ψ w x → □ (fun v => ∀ y : Ind, φ v y → ψ v y)

/-- **D3.** Necessary existence in the universal encoding. -/
def NE {W Ind : Type} : Property W Ind :=
  fun w x => ∀ φ : Property W Ind, Essence φ w x → □ (fun v => ∃ y : Ind, φ v y)

/-- **D2 along `R`.** Essence quantified only over `R`-successors. -/
def EssenceR {W Ind : Type} (R : Access W) (φ : Property W Ind) (w : W) (x : Ind) : Prop :=
  φ w x ∧ ∀ ψ : Property W Ind, ψ w x →
    necessaryR R (fun v => ∀ y : Ind, φ v y → ψ v y) w

/-- **D3 along `R`.** Necessary existence along `R`. -/
def NER {W Ind : Type} (R : Access W) : Property W Ind :=
  fun w x => ∀ φ : Property W Ind, EssenceR R φ w x →
    necessaryR R (fun v => ∃ y : Ind, φ v y) w

/-! ## Scott hypotheses (not ambient axioms, not theorems) -/

/-- **A1.** A property is positive iff its negation is not. -/
def A1 {W Ind : Type} (Positive : Property W Ind → Prop) : Prop :=
  ∀ φ : Property W Ind, Positive (propNeg φ) ↔ ¬ Positive φ

/-- **A2.** Whatever a positive property necessarily entails is positive.
Entailment here is the universal-encoding `necEntails`. -/
def A2 {W Ind : Type} (Positive : Property W Ind → Prop) : Prop :=
  ∀ φ ψ : Property W Ind, Positive φ → necEntails φ ψ → Positive ψ

/-- **A3.** Being God-like is positive. -/
def A3 {W Ind : Type} (Positive : Property W Ind → Prop) : Prop :=
  Positive (GodLike Positive)

/-- **A5 (universal encoding).** Necessary existence (`NE`, box over all worlds)
is positive. Scott’s consistency repair, in the encoding where `□` is `∀ w`. -/
def A5 {W Ind : Type} (Positive : Property W Ind → Prop) : Prop :=
  Positive (NE : Property W Ind)

/-- **A5 along `R`.** Necessary existence *along `R`* is positive.
This is the hypothesis paired with an explicit frame condition.
It is not the same `Prop` as `A5` unless `R` reaches every world. -/
def A5R {W Ind : Type} (R : Access W) (Positive : Property W Ind → Prop) : Prop :=
  Positive (NER R)

/-! ## Universal-encoding chain (`□` already quantifies over every world)

These theorems do **not** take a separate `Universal R` argument because the
box in `NE` / `Essence` is already the universal encoding. Read them as the
global, total-frame special case — not as “T3 in S5”.
-/

theorem positive_propTrue {W Ind : Type} (Positive : Property W Ind → Prop)
    (hA2 : A2 Positive) {φ : Property W Ind} (hφ : Positive φ) :
    Positive (propTrue : Property W Ind) :=
  hA2 φ propTrue hφ (necEntails_true φ)

/-- **T1.** A positive property is exemplified at some world. Uses A1 and A2.
A5 is not a hypothesis. -/
theorem T1_positive_possibly_exemplified {W Ind : Type}
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA2 : A2 Positive)
    (φ : Property W Ind) (hP : Positive φ) :
    ◇ (fun w : W => ∃ x : Ind, φ w x) := by
  apply Classical.byContradiction
  intro h
  have nowhere : ∀ (w : W) (x : Ind), ¬ φ w x := by
    intro w x hx
    exact h ⟨w, x, hx⟩
  have hFalse : Positive (propFalse : Property W Ind) :=
    hA2 φ propFalse hP (necEntails_false_of_nowhere φ nowhere)
  have hNegTrue : Positive (propNeg (propTrue : Property W Ind)) := by
    rw [propNeg_true]; exact hFalse
  have hNotTrue : ¬ Positive (propTrue : Property W Ind) :=
    (hA1 propTrue).mp hNegTrue
  have hTrue : Positive (propTrue : Property W Ind) :=
    positive_propTrue Positive hA2 hP
  exact hNotTrue hTrue

/-- **C.** Possibly (some world) a God-like being exists. Uses A1–A3, not A5. -/
theorem C_possibly_God {W Ind : Type} (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA2 : A2 Positive) (hA3 : A3 Positive) :
    ◇ (fun w : W => ∃ x : Ind, GodLike Positive w x) :=
  T1_positive_possibly_exemplified Positive hA1 hA2 (GodLike Positive) hA3

theorem godlike_has_only_positive {W Ind : Type}
    (Positive : Property W Ind → Prop) (hA1 : A1 Positive)
    {w : W} {x : Ind} {ψ : Property W Ind}
    (hg : GodLike Positive w x) (hψ : ψ w x) :
    Positive ψ := by
  apply Classical.byContradiction
  intro hNot
  have hNeg : Positive (propNeg ψ) := (hA1 ψ).mpr hNot
  have : propNeg ψ w x := hg (propNeg ψ) hNeg
  exact this hψ

/-- **T2.** God-likeness is an essence of any God-like being. Uses A1.
A4 is not required: `Positive` is rigid. -/
theorem T2_godlike_essence {W Ind : Type}
    (Positive : Property W Ind → Prop) (hA1 : A1 Positive)
    {w : W} {x : Ind} (hg : GodLike Positive w x) :
    Essence (GodLike Positive) w x := by
  refine ⟨hg, ?_⟩
  intro ψ hψ
  have hPos : Positive ψ := godlike_has_only_positive Positive hA1 hg hψ
  intro v y hy
  exact hy ψ hPos

theorem godlike_has_NE {W Ind : Type}
    (Positive : Property W Ind → Prop) (hA5 : A5 Positive)
    {w : W} {x : Ind} (hg : GodLike Positive w x) :
    NE w x :=
  hg NE hA5

/-- Reflection in the universal encoding: God at `w` ⇒ God at every world.
Hypotheses: A1 and A5. No separate frame parameter (the box is already total). -/
theorem exists_God_implies_necessary {W Ind : Type}
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA5 : A5 Positive)
    {w : W} (hEx : ∃ x : Ind, GodLike Positive w x) :
    □ (fun v : W => ∃ y : Ind, GodLike Positive v y) := by
  obtain ⟨x, hx⟩ := hEx
  have hEss : Essence (GodLike Positive) w x := T2_godlike_essence Positive hA1 hx
  have hNE : NE w x := godlike_has_NE Positive hA5 hx
  exact hNE (GodLike Positive) hEss

/-- **T3 in the universal encoding.** `□ ∃x GodLike x` from A1–A3 and A5.
The box quantifies over every world. This is not a theorem of S5 alone,
and it is not Kant’s postulate that God exists. -/
theorem T3_necessarily_God {W Ind : Type}
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA2 : A2 Positive) (hA3 : A3 Positive) (hA5 : A5 Positive) :
    □ (fun w : W => ∃ x : Ind, GodLike Positive w x) := by
  obtain ⟨w0, hEx⟩ := C_possibly_God Positive hA1 hA2 hA3
  exact exists_God_implies_necessary Positive hA1 hA5 hEx

theorem exists_God_at_every_world {W Ind : Type}
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA2 : A2 Positive) (hA3 : A3 Positive) (hA5 : A5 Positive)
    (w : W) :
    ∃ x : Ind, GodLike Positive w x :=
  T3_necessarily_God Positive hA1 hA2 hA3 hA5 w

/-! ## R-relative chain (frame conditions appear in the type) -/

/-- **T2 along `R`.** Same A1 argument as `T2_godlike_essence`; the entailed
properties are required only at `R`-successors. -/
theorem T2R_godlike_essence {W Ind : Type} (R : Access W)
    (Positive : Property W Ind → Prop) (hA1 : A1 Positive)
    {w : W} {x : Ind} (hg : GodLike Positive w x) :
    EssenceR R (GodLike Positive) w x := by
  refine ⟨hg, ?_⟩
  intro ψ hψ
  have hPos : Positive ψ := godlike_has_only_positive Positive hA1 hg hψ
  intro v _hv y hy
  exact hy ψ hPos

theorem godlike_has_NER {W Ind : Type} (R : Access W)
    (Positive : Property W Ind → Prop) (hA5 : A5R R Positive)
    {w : W} {x : Ind} (hg : GodLike Positive w x) :
    NER R w x :=
  hg (NER R) hA5

/-- **Local reflection.** God at `w` ⇒ God at every `R`-successor.
Hypotheses: A1 and A5R. **No frame hypothesis.** -/
theorem exists_God_implies_necessaryR {W Ind : Type} (R : Access W)
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA5 : A5R R Positive)
    {w : W} (hEx : ∃ x : Ind, GodLike Positive w x) :
    necessaryR R (fun v => ∃ y : Ind, GodLike Positive v y) w := by
  obtain ⟨x, hx⟩ := hEx
  exact godlike_has_NER R Positive hA5 hx (GodLike Positive)
    (T2R_godlike_essence R Positive hA1 hx)

/-- **Local T3.** Diamond-God at `w` yields box-God at `w`, **if `R` is symmetric**.

Frame hypothesis in the type: `Symmetric R` (Brouwerian).
A1 and A5R are the Scott hypotheses used; A2 and A3 are not needed for this
arrow (they are what produce the diamond, via `C_possibly_God`, in the
universal encoding).

Rediscovery: symmetry is enough for this necessity step
(Benzmüller–Paleo, AFP `GoedelGod`). Not a priority claim.
-/
theorem local_T3_of_Symmetric {W Ind : Type} (R : Access W)
    (hSym : Symmetric R)
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA5 : A5R R Positive)
    {w : W}
    (hPos : possibleR R (fun v => ∃ x : Ind, GodLike Positive v x) w) :
    necessaryR R (fun v => ∃ x : Ind, GodLike Positive v x) w := by
  obtain ⟨v, hwv, hEx⟩ := hPos
  have hAtW : ∃ x : Ind, GodLike Positive w x :=
    exists_God_implies_necessaryR R Positive hA1 hA5 hEx w (hSym w v hwv)
  exact exists_God_implies_necessaryR R Positive hA1 hA5 hAtW

/-- Local T3 packaged under the name `Brouwerian` (the same hypothesis as symmetry). -/
theorem local_T3_of_Brouwerian {W Ind : Type} (R : Access W)
    (hB : Brouwerian R)
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA5 : A5R R Positive)
    {w : W}
    (hPos : possibleR R (fun v => ∃ x : Ind, GodLike Positive v x) w) :
    necessaryR R (fun v => ∃ x : Ind, GodLike Positive v x) w :=
  local_T3_of_Symmetric R hB Positive hA1 hA5 hPos

/-- **Global T3.** God-like at every world.
Frame hypothesis in the type: `Universal R`.
Scott hypotheses: A1, A2, A3, A5R. Drop any one of those four, or drop
`Universal`, and this theorem’s type is a different claim — see
`FrameCountermodel` for an S5 frame that is not universal. -/
theorem T3R_necessarily_God_of_universal {W Ind : Type} (R : Access W)
    (hU : Universal R)
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA2 : A2 Positive)
    (hA3 : A3 Positive) (hA5 : A5R R Positive) :
    ∀ w : W, ∃ x : Ind, GodLike Positive w x := by
  obtain ⟨w0, hEx⟩ := C_possibly_God Positive hA1 hA2 hA3
  intro w
  exact exists_God_implies_necessaryR R Positive hA1 hA5 hEx w (hU w0 w)

/-! ## Universal encoding ↔ `Universal R` -/

theorem Essence_iff_EssenceR_of_Universal {W Ind : Type} {R : Access W}
    (hU : Universal R) (φ : Property W Ind) (w : W) (x : Ind) :
    Essence φ w x ↔ EssenceR R φ w x := by
  constructor
  · intro hEss
    refine ⟨hEss.1, ?_⟩
    intro ψ hψ v _hv y hy
    exact hEss.2 ψ hψ v y hy
  · intro hEss
    refine ⟨hEss.1, ?_⟩
    intro ψ hψ v y hy
    exact hEss.2 ψ hψ v (hU w v) y hy

/-- Under `Universal R`, `NE` and `NER R` are the same property, so Scott’s
universal-encoding A5 is exactly A5R. -/
theorem NER_eq_NE_of_Universal {W Ind : Type} {R : Access W} (hU : Universal R) :
    (NER R : Property W Ind) = NE := by
  funext w x
  apply propext
  constructor
  · intro hNER φ hEss
    intro v
    have hEssR : EssenceR R φ w x :=
      (Essence_iff_EssenceR_of_Universal hU φ w x).mp hEss
    exact hNER φ hEssR v (hU w v)
  · intro hNE φ hEssR
    intro v _hv
    have hEss : Essence φ w x :=
      (Essence_iff_EssenceR_of_Universal hU φ w x).mpr hEssR
    exact hNE φ hEss v

theorem A5R_of_A5_of_Universal {W Ind : Type} {R : Access W} (hU : Universal R)
    (Positive : Property W Ind → Prop) (hA5 : A5 Positive) :
    A5R R Positive := by
  simpa [A5R, A5, NER_eq_NE_of_Universal hU] using hA5

theorem A5_of_A5R_of_Universal {W Ind : Type} {R : Access W} (hU : Universal R)
    (Positive : Property W Ind → Prop) (hA5 : A5R R Positive) :
    A5 Positive := by
  simpa [A5R, A5, NER_eq_NE_of_Universal hU] using hA5

/-! ## Countermodel: S5 does not yield global T3

`W = Bool`, `R =` identity. That is an S5 frame (one-point clusters) and it
is not universal. Positivity is “true of the only individual at `false`”.
A1–A3 and A5R hold; a God-like individual exists at `false` and not at `true`.
So the `Universal` hypothesis of `T3R_necessarily_God_of_universal` is not
discharged by `S5Frame`.
-/

namespace FrameCountermodel

abbrev W := Bool
abbrev Ind := Unit

def R : Access Bool := idRel Bool

def Pos : Property W Ind → Prop := fun φ => φ false ()

theorem Pos_A1 : A1 Pos := fun _ => Iff.rfl

theorem Pos_A2 : A2 Pos := fun _ _ hφ hent => hent false () hφ

theorem God_iff (w : W) (x : Ind) : GodLike Pos w x ↔ w = false := by
  constructor
  · intro hg
    exact hg (fun v _ => v = false) rfl
  · intro hw φ hP
    cases hw
    cases x
    exact hP

theorem Pos_A3 : A3 Pos := fun _ hP => hP

theorem NER_at_false (x : Ind) : NER R false x := by
  intro φ hEss v hv
  cases hv
  cases x
  exact ⟨(), hEss.1⟩

theorem Pos_A5R : A5R R Pos := NER_at_false ()

theorem god_at_false : ∃ x : Ind, GodLike Pos false x :=
  ⟨(), (God_iff false ()).mpr rfl⟩

theorem not_god_at_true : ¬ ∃ x : Ind, GodLike Pos true x := by
  intro ⟨x, hx⟩
  have : true = false := (God_iff true x).mp hx
  cases this

theorem not_universal : ¬ Universal R := by
  intro hU
  have : false = true := hU false true
  cases this

theorem is_s5 : S5Frame R := idRel_s5 Bool

end FrameCountermodel

/-- **Global T3 needs more than S5.** There is an S5 frame, not a universal
one, in which A1–A3 and A5R hold and `∀ w ∃ x GodLike` fails. -/
theorem S5_does_not_yield_global_T3 :
    ∃ (W Ind : Type) (R : Access W) (Positive : Property W Ind → Prop),
      S5Frame R ∧ ¬ Universal R ∧
      A1 Positive ∧ A2 Positive ∧ A3 Positive ∧ A5R R Positive ∧
      ¬ ∀ w : W, ∃ x : Ind, GodLike Positive w x :=
  ⟨Bool, Unit, FrameCountermodel.R, FrameCountermodel.Pos,
    FrameCountermodel.is_s5, FrameCountermodel.not_universal,
    FrameCountermodel.Pos_A1, FrameCountermodel.Pos_A2,
    FrameCountermodel.Pos_A3, FrameCountermodel.Pos_A5R,
    fun h => FrameCountermodel.not_god_at_true (h true)⟩

end GodFreedomImmortality
