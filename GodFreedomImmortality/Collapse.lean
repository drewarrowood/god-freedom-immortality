import GodFreedomImmortality.God

/-
# Modal collapse

Sobel observed that Scott-style premises yield **modal collapse** (`φ → □φ`).
Benzmüller et al. re-checked this in HOML. The theorems here are a
rediscovery in this thin encoding, not a priority claim.

Collapse is what makes **contingency** (`ContingentR`: true here, false at
an accessible world) impossible. That is a theorem under `Universal R` plus
A1–A3 and A5R. It is not a theorem of S5 alone: `ContingencyCountermodel`
is an S5 frame with two clusters in which A1–A3 and A5R hold and a
proposition is still contingent off the God-cluster.

Kantian practical freedom is **not** defined in this file. See `Freedom.lean`.
-/

namespace GodFreedomImmortality

/-! ## Contingency -/

/-- True at `w`, and false at some `R`-successor. -/
def ContingentR {W : Type} (R : Access W) (φ : W → Prop) (w : W) : Prop :=
  φ w ∧ possibleR R (fun v => ¬ φ v) w

/-- An individual-relative act `α`, read as contingency of `fun v => α v x`. -/
def ContingentAct {W Ind : Type} (R : Access W)
    (α : Property W Ind) (w : W) (x : Ind) : Prop :=
  ContingentR R (fun v => α v x) w

/-- Contingency in the universal encoding (`◇` = some world). -/
def Contingent {W : Type} (φ : W → Prop) (w : W) : Prop :=
  φ w ∧ ◇ (fun v => ¬ φ v)

/-! ## Collapse statements -/

/-- At `w`, whatever is true is `R`-necessary. -/
def ModalCollapseAt {W : Type} (R : Access W) (w : W) : Prop :=
  ∀ φ : W → Prop, φ w → necessaryR R φ w

/-- Collapse at every world. -/
def ModalCollapseR {W : Type} (R : Access W) : Prop :=
  ∀ w : W, ModalCollapseAt R w

/-- Sobel collapse in the universal encoding: `φ w → □ φ`. -/
def ModalCollapse {W : Type} : Prop :=
  ∀ (φ : W → Prop) (w : W), φ w → □ φ

theorem ContingentR_impossible_of_collapseAt {W : Type} (R : Access W)
    {w : W} (hMC : ModalCollapseAt R w) (φ : W → Prop) :
    ¬ ContingentR R φ w := by
  intro ⟨hφ, ⟨v, hRv, hnφ⟩⟩
  exact hnφ (hMC φ hφ v hRv)

theorem ContingentAct_impossible_of_collapseAt {W Ind : Type} (R : Access W)
    {w : W} (hMC : ModalCollapseAt R w) (α : Property W Ind) (x : Ind) :
    ¬ ContingentAct R α w x :=
  ContingentR_impossible_of_collapseAt R hMC (fun v => α v x)

theorem Contingent_impossible_of_ModalCollapse {W : Type}
    (hMC : ModalCollapse (W := W)) (φ : W → Prop) (w : W) :
    ¬ Contingent φ w := by
  intro ⟨hφ, ⟨v, hnφ⟩⟩
  exact hnφ (hMC φ w hφ v)

/-! ## Collapse at a God-world, and under Universal + Scott -/

/-- Constant property induced by a world-proposition. -/
def constProp {W Ind : Type} (φ : W → Prop) : Property W Ind :=
  fun v _ => φ v

/-- Sobel step at a world that already has a God-like being.
A1 + A5R only: lift `φ` to `constProp`, then essence plus necessary existence
push `φ` along every `R`-edge. No `Universal` hypothesis. -/
theorem local_collapse_of_God {W Ind : Type} (R : Access W)
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA5 : A5R R Positive)
    {w : W} (hEx : ∃ x : Ind, GodLike Positive w x)
    (φ : W → Prop) (hφ : φ w) :
    necessaryR R φ w := by
  obtain ⟨x, hx⟩ := hEx
  have hEss : EssenceR R (GodLike Positive) w x :=
    T2R_godlike_essence R Positive hA1 hx
  have hNE : NER R w x := godlike_has_NER R Positive hA5 hx
  have hBoxG :
      necessaryR R (fun v => ∃ y : Ind, GodLike Positive v y) w :=
    hNE (GodLike Positive) hEss
  have hTrans :
      necessaryR R
        (fun v => ∀ y : Ind, GodLike Positive v y → constProp (Ind := Ind) φ v y) w :=
    hEss.2 (constProp (Ind := Ind) φ) hφ
  intro v hv
  obtain ⟨y, hy⟩ := hBoxG v hv
  exact hTrans v hv y hy

theorem ModalCollapseAt_of_God {W Ind : Type} (R : Access W)
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA5 : A5R R Positive)
    {w : W} (hEx : ∃ x : Ind, GodLike Positive w x) :
    ModalCollapseAt R w :=
  fun φ hφ => local_collapse_of_God R Positive hA1 hA5 hEx φ hφ

/-- **Collapse everywhere** from `Universal R` and Scott A1–A3 + A5R.
`Universal` is used: it is what puts a God-like being at every world
(`T3R_necessarily_God_of_universal`), and collapse is then local at each. -/
theorem ModalCollapseR_of_universal {W Ind : Type} (R : Access W)
    (hU : Universal R)
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA2 : A2 Positive)
    (hA3 : A3 Positive) (hA5 : A5R R Positive) :
    ModalCollapseR R := by
  intro w
  exact ModalCollapseAt_of_God R Positive hA1 hA5
    (T3R_necessarily_God_of_universal R hU Positive hA1 hA2 hA3 hA5 w)

/-- **Theorem.** `ContingentR` is incompatible with Universal accessibility
plus Scott A1–A3 + A5R. -/
theorem ContingentR_impossible_of_universal {W Ind : Type} (R : Access W)
    (hU : Universal R)
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA2 : A2 Positive)
    (hA3 : A3 Positive) (hA5 : A5R R Positive)
    (φ : W → Prop) (w : W) :
    ¬ ContingentR R φ w :=
  ContingentR_impossible_of_collapseAt R
    (ModalCollapseR_of_universal R hU Positive hA1 hA2 hA3 hA5 w) φ

theorem ContingentAct_impossible_of_universal {W Ind : Type} (R : Access W)
    (hU : Universal R)
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA2 : A2 Positive)
    (hA3 : A3 Positive) (hA5 : A5R R Positive)
    (α : Property W Ind) (w : W) (x : Ind) :
    ¬ ContingentAct R α w x :=
  ContingentR_impossible_of_universal R hU Positive hA1 hA2 hA3 hA5
    (fun v => α v x) w

/-- Same incompatibility, stated as one package: the five assumptions cannot
hold together with a contingent proposition. -/
theorem ContingentR_incompatible_with_Universal_Scott {W Ind : Type}
    (R : Access W) (hU : Universal R)
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA2 : A2 Positive)
    (hA3 : A3 Positive) (hA5 : A5R R Positive)
    (φ : W → Prop) (w : W) :
    ¬ ContingentR R φ w :=
  ContingentR_impossible_of_universal R hU Positive hA1 hA2 hA3 hA5 φ w

/-! ## Universal encoding (`□ = ∀ w`): Sobel collapse from A1–A5

Here universality sits inside `□`, not in a separate `Universal R` argument.
`A5_of_A5R_of_Universal` / `A5R_of_A5_of_Universal` record that this matches
the R-relative package when `R` is universal.
-/

theorem ModalCollapse_of_Scott {W Ind : Type}
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA2 : A2 Positive)
    (hA3 : A3 Positive) (hA5 : A5 Positive) :
    ModalCollapse (W := W) := by
  intro φ w hφ v
  obtain ⟨x, hx⟩ := exists_God_at_every_world Positive hA1 hA2 hA3 hA5 w
  have hEss : Essence (GodLike Positive) w x :=
    T2_godlike_essence Positive hA1 hx
  have hTrans : □ (fun u => ∀ y : Ind,
      GodLike Positive u y → constProp (Ind := Ind) φ u y) :=
    hEss.2 (constProp (Ind := Ind) φ) hφ
  obtain ⟨y, hy⟩ := exists_God_at_every_world Positive hA1 hA2 hA3 hA5 v
  exact hTrans v y hy

theorem Contingent_impossible_of_Scott {W Ind : Type}
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA2 : A2 Positive)
    (hA3 : A3 Positive) (hA5 : A5 Positive)
    (φ : W → Prop) (w : W) :
    ¬ Contingent φ w :=
  Contingent_impossible_of_ModalCollapse
    (ModalCollapse_of_Scott Positive hA1 hA2 hA3 hA5) φ w

/-- In the universal encoding, contingency along *any* `R` dies as well:
collapse says `φ` is true at every world, hence at every successor. -/
theorem ContingentR_impossible_of_Scott_encoding {W Ind : Type}
    (R : Access W)
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA2 : A2 Positive)
    (hA3 : A3 Positive) (hA5 : A5 Positive)
    (φ : W → Prop) (w : W) :
    ¬ ContingentR R φ w := by
  intro ⟨hφ, ⟨v, _hv, hnφ⟩⟩
  exact hnφ (ModalCollapse_of_Scott Positive hA1 hA2 hA3 hA5 φ w hφ v)

/-! ## Countermodel: without `Universal`, ContingentR can survive

Three worlds, two S5 clusters `{a, b}` and `{c}`. Positivity is truth at `c`.
A1–A3 and A5R hold, God-likeness holds only at `c`, and `fun w => w = a` is
`ContingentR` at `a`. So A1–A3 + A5R + `S5Frame` do **not** refute
contingency. `Universal` was load-bearing in
`ContingentR_incompatible_with_Universal_Scott`.
-/

namespace ContingencyCountermodel

inductive WD where
  | a
  | b
  | c
  deriving DecidableEq, Repr

abbrev Ind := Unit

/-- `{a, b}` and `{c}`. -/
def cluster : WD → Bool
  | .a => false
  | .b => false
  | .c => true

def R : Access WD := fun w v => cluster w = cluster v

def Pos : Property WD Ind → Prop := fun φ => φ WD.c ()

theorem R_refl : Reflexive R := fun _ => rfl

theorem R_symm : Symmetric R := fun _ _ h => h.symm

theorem R_eucl : Euclidean R := fun _ _ _ hwv hwu => hwv.symm.trans hwu

theorem R_s5 : S5Frame R := ⟨R_refl, R_eucl⟩

theorem R_not_universal : ¬ Universal R := by
  intro hU
  have h : cluster WD.a = cluster WD.c := hU WD.a WD.c
  simp [cluster] at h

theorem Pos_A1 : A1 Pos := fun _ => Iff.rfl

theorem Pos_A2 : A2 Pos := fun _ _ hφ hent => hent WD.c () hφ

theorem God_iff (w : WD) (x : Ind) : GodLike Pos w x ↔ w = WD.c := by
  constructor
  · intro hg
    exact hg (fun v _ => v = WD.c) rfl
  · intro hw φ hP
    cases hw
    cases x
    exact hP

theorem Pos_A3 : A3 Pos := fun _ hP => hP

theorem NER_at_c (x : Ind) : NER R WD.c x := by
  intro φ hEss v hv
  cases v with
  | a => simp [R, cluster] at hv
  | b => simp [R, cluster] at hv
  | c =>
    cases x
    exact ⟨(), hEss.1⟩

theorem Pos_A5R : A5R R Pos := NER_at_c ()

theorem god_only_at_c :
    (∃ x : Ind, GodLike Pos WD.c x) ∧ ¬ ∃ x : Ind, GodLike Pos WD.a x :=
  ⟨⟨(), (God_iff WD.c ()).mpr rfl⟩, fun ⟨x, hx⟩ => by
    have : WD.a = WD.c := (God_iff WD.a x).mp hx
    cases this⟩

/-- True only at `a`. -/
def φa : WD → Prop := fun w => w = WD.a

theorem contingent_at_a : ContingentR R φa WD.a :=
  ⟨rfl, ⟨WD.b, rfl, fun h => by cases h⟩⟩

theorem not_collapse_at_a : ¬ ModalCollapseAt R WD.a := by
  intro hMC
  have : WD.b = WD.a := hMC φa rfl WD.b rfl
  cases this

theorem collapse_at_c : ModalCollapseAt R WD.c :=
  ModalCollapseAt_of_God R Pos Pos_A1 Pos_A5R god_only_at_c.1

end ContingencyCountermodel

/-- **S5 + Scott does not kill contingency.** Dropping `Universal` is a real
cut: this model satisfies A1–A3, A5R, and `S5Frame`, and `ContingentR` still
holds at a non-God world. -/
theorem S5_Scott_does_not_rule_out_ContingentR :
    ∃ (W Ind : Type) (R : Access W) (Positive : Property W Ind → Prop)
      (φ : W → Prop) (w : W),
      S5Frame R ∧ ¬ Universal R ∧
      A1 Positive ∧ A2 Positive ∧ A3 Positive ∧ A5R R Positive ∧
      ContingentR R φ w ∧ ¬ ModalCollapseAt R w :=
  ⟨ContingencyCountermodel.WD, Unit, ContingencyCountermodel.R,
    ContingencyCountermodel.Pos, ContingencyCountermodel.φa,
    ContingencyCountermodel.WD.a,
    ContingencyCountermodel.R_s5, ContingencyCountermodel.R_not_universal,
    ContingencyCountermodel.Pos_A1, ContingencyCountermodel.Pos_A2,
    ContingencyCountermodel.Pos_A3, ContingencyCountermodel.Pos_A5R,
    ContingencyCountermodel.contingent_at_a,
    ContingencyCountermodel.not_collapse_at_a⟩

end GodFreedomImmortality
