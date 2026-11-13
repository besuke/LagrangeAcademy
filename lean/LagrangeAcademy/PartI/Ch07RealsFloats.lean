module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# 第7章 実数と数値計算

なぜ数学の実数とコンピュータの浮動小数点数は異なるのか。

- 有理数 `ℚ` は正確に計算できる（`#eval` で `3/10` と表示される）。ただし、`decide` では
  カーネルの簡約が途中で止まって証明にならない（`scripts/ch07_checks.lean` にコメントで記録）。
  `norm_num` で示す（`rat_add`）。
- 実数 `ℝ` は、Mathlib ではコーシー列の商として作られ、計算できない（`noncomputable`）。
  等式は計算ではなく証明で示す（`real_add`）。
- 浮動小数点数 `Float` は、Lean 4.35.0 では IEEE 754 の倍精度（binary64）のビット列の論理モデル
  `Float.Model` を包んだ構造体である。カーネルはこのモデルで計算するので、`decide` で `Float` の
  性質を証明できる（`float_add_ne`、`float_add_not_assoc`、`float_absorb`、`float_zero_ne_neg_zero`）。
  コンパイルしたコード（`#eval`）は、モデルではなく C の演算を使う。両者が一致することは、
  カーネルが確かめることではない。
- 第1章の整数のペイオフの恒等式を、実数に広げる（`call_sub_put_payoff_real`）。
- 連続複利の割引係数 `exp (-(r * T))` は、`r, T ≥ 0` なら `0` より大きく `1` 以下である
  （`discount_pos`、`discount_le_one`）。
- Mathlib は `exp 1` の小数の上下限を証明している。それを使って、`2.718 < exp 1 < 2.719` を示す
  （`exp_one_bounds`）。
-/

@[expose] public section

namespace LagrangeAcademy.Ch07

/-! ## 有理数と実数 -/

/-- 有理数では、`1/10 + 2/10 = 3/10` が正確に成り立つ。`norm_num` は、分数の式を正規化して
確かめる。 -/
theorem rat_add : (1 / 10 + 2 / 10 : ℚ) = 3 / 10 := by norm_num

/-- 実数でも成り立つ。実数は計算できない（`noncomputable`）が、`norm_num` は記号の上で式を
正規化するので、同じように証明できる。 -/
theorem real_add : (0.1 + 0.2 : ℝ) = 0.3 := by norm_num

/-! ## 浮動小数点数：モデルの上の証明 -/

/-- 浮動小数点数では、`0.1 + 0.2` は `0.3` と等しくない。`decide` は、`Float.Model` のビット列の
計算をカーネルにさせて確かめる。 -/
theorem float_add_ne : (0.1 + 0.2 : Float) ≠ 0.3 := by decide

/-- 浮動小数点数の足し算は結合的でない。 -/
theorem float_add_not_assoc : ((0.1 + 0.2) + 0.3 : Float) ≠ 0.1 + (0.2 + 0.3) := by decide

/-- 大きな数に小さな数を足すと、小さな数が丸めで消える（情報落ち）。 -/
theorem float_absorb : ((1e16 : Float) + 1) - 1e16 = 0 := by decide

/-- `0.0` と `-0.0` は、モデル（ビット列）としては等しくない。IEEE 754 の比較 `==` では
等しいと判定される（`scripts/ch07_checks.lean`）。`=` と `==` は別の関係である。 -/
theorem float_zero_ne_neg_zero : (0.0 : Float) ≠ -0.0 := by decide

/-! ## ペイオフの恒等式を実数に広げる -/

/-- 第1章の `call_sub_put_payoff` の実数版。`s` と `k` の大小で場合を分ける。 -/
theorem call_sub_put_payoff_real (s k : ℝ) : max (s - k) 0 - max (k - s) 0 = s - k := by
  rcases le_total s k with h | h
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
    ring
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
    ring

/-! ## 連続複利の割引係数 -/

/-- 割引係数は正である。 -/
theorem discount_pos (r T : ℝ) : 0 < Real.exp (-(r * T)) :=
  Real.exp_pos _

/-- 利子率と期間が非負なら、割引係数は 1 以下である。 -/
theorem discount_le_one {r T : ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T) : Real.exp (-(r * T)) ≤ 1 :=
  Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hr hT))

/-! ## 実数の値を有理数で挟む -/

/-- Mathlib の `Real.exp_one_gt_d9`（`2.7182818283 < exp 1`）と `Real.exp_one_lt_d9`
（`exp 1 < 2.7182818286`）を使って、`exp 1` を小数 3 桁で挟む。 -/
theorem exp_one_bounds : 2.718 < Real.exp 1 ∧ Real.exp 1 < 2.719 := by
  constructor
  · linarith [Real.exp_one_gt_d9]
  · linarith [Real.exp_one_lt_d9]

end LagrangeAcademy.Ch07

end
