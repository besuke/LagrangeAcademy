module

public import Mathlib.Basic.Real.Basic

/-!
# PRDC の条件と仮定

PRDC のノートのクーポンの条件を、Lean の型として書く（第3章）。

- キャップの有無は `Cap` の 2 通りで表す。契約で「上限を適用しない」は `Cap.none` である。
  RiemannFinMath（Rust）は、同じ条件を `cap = f64::INFINITY` で表す。この対応は第5章で扱う。
- 仮定（基準の FX が正、レバレッジが正、有限のキャップならフロア以上）は、構造体の欄として
  持たせる。仮定を満たさない条件は、型として作れない。
- クーポンのレート `couponRate` は、契約のクーポンの定義そのもの（切り詰め）である。
  分解（フロアとコールの和）は定義に含めず、第5章で定理として示す。
-/

@[expose] public section

namespace LagrangeAcademy

/-- クーポンの上限：有限のキャップ、または上限を適用しない。 -/
inductive Cap where
  /-- 上限 `c` を適用する。 -/
  | finite (c : ℝ)
  /-- 上限を適用しない。 -/
  | none

/-- PRDC のクーポンの条件。クーポンのレートは `clamp(leverage * S / fxBase - subtraction, floor, cap)`。 -/
structure PrdcTerms where
  /-- 基準の FX レート（国内通貨 / 外国通貨）。 -/
  fxBase : ℝ
  leverage : ℝ
  /-- 差し引く率。 -/
  subtraction : ℝ
  floor : ℝ
  cap : Cap
  fxBase_pos : 0 < fxBase
  leverage_pos : 0 < leverage
  /-- 有限のキャップは、フロア以上である。 -/
  floor_le_cap : ∀ c : ℝ, cap = Cap.finite c → floor ≤ c

namespace PrdcTerms

/-- クーポンの FX に対する傾き `a = leverage / fxBase`。 -/
noncomputable def slope (t : PrdcTerms) : ℝ := t.leverage / t.fxBase

/-- 傾きは正（仮定 `fxBase_pos` と `leverage_pos` から）。 -/
theorem slope_pos (t : PrdcTerms) : 0 < t.slope :=
  div_pos t.leverage_pos t.fxBase_pos

/-- 契約のクーポンのレート：FX レート `S` に対して、`a S - subtraction` をフロアで下から、
キャップがあれば上から切り詰める。 -/
noncomputable def couponRate (t : PrdcTerms) (S : ℝ) : ℝ :=
  match t.cap with
  | Cap.finite c => min (max (t.slope * S - t.subtraction) t.floor) c
  | Cap.none => max (t.slope * S - t.subtraction) t.floor

/-- クーポンがフロアに達する FX 水準 `K₁ = (subtraction + floor) / a`。 -/
noncomputable def floorStrike (t : PrdcTerms) : ℝ := (t.subtraction + t.floor) / t.slope

/-- クーポンがキャップ `c` に達する FX 水準 `K₂ = (subtraction + c) / a`。 -/
noncomputable def capStrike (t : PrdcTerms) (c : ℝ) : ℝ := (t.subtraction + c) / t.slope

end PrdcTerms

end LagrangeAcademy

end
