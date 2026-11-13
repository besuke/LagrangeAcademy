module

public import LagrangeAcademy.PartI.Ch06StructuresClasses
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# 第8章 Mathlibの数学構造と確率論

確率論の概念は、Lean でどのように表現されるのか。有限の確率空間を中心にする。

- 有限の確率空間を自分で定義する（`FinProb`）。確率は非負で和が 1 の関数、期待値は有限和である。
  期待値の線形性と単調性を示す（`FinProb.expect_add`、`FinProb.expect_smul`、
  `FinProb.expect_mono` など）。
- Mathlib の測度論の言葉では、有限の型の上の確率測度による積分は、1 点集合の測度による
  有限和になる（`integral_eq_sum`、Mathlib の `MeasureTheory.integral_fintype` を使う）。
- 金融数学への接続：第6章の 1 期間の二項モデルで、リスク中立確率 `q` を有限の確率空間にし、
  危険資産の 1 期後の価格の期待値が `(1 + r)` 倍の今日の価格になることを示す
  （`Binomial.expect_stock`）。これは、割り引いた価格がリスク中立確率のもとで
  （1 期間の）マルチンゲールになる、という性質の最も簡単な場合である。
-/

@[expose] public section

namespace LagrangeAcademy.Ch08

open LagrangeAcademy.Ch06

/-! ## 有限の確率空間 -/

/-- 有限の型 `Ω` の上の確率：各結果の確率 `prob ω` は非負で、すべての和は 1。 -/
structure FinProb (Ω : Type*) [Fintype Ω] where
  prob : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ prob ω
  sum_one : ∑ ω, prob ω = 1

namespace FinProb

variable {Ω : Type*} [Fintype Ω] (P : FinProb Ω)

/-- 確率変数 `X : Ω → ℝ` の期待値。 -/
def expect (X : Ω → ℝ) : ℝ := ∑ ω, P.prob ω * X ω

/-- 定数の期待値は、その定数である。確率の和が 1 であることを使う。 -/
theorem expect_const (c : ℝ) : P.expect (fun _ => c) = c := by
  unfold expect
  rw [← Finset.sum_mul, P.sum_one, one_mul]

/-- 期待値は足し算を保つ。 -/
theorem expect_add (X Y : Ω → ℝ) : P.expect (fun ω => X ω + Y ω) = P.expect X + P.expect Y := by
  unfold expect
  rw [← Finset.sum_add_distrib]
  congr 1
  funext ω
  ring

/-- 期待値は定数倍を保つ。 -/
theorem expect_smul (c : ℝ) (X : Ω → ℝ) : P.expect (fun ω => c * X ω) = c * P.expect X := by
  unfold expect
  rw [Finset.mul_sum]
  congr 1
  funext ω
  ring

/-- 非負の確率変数の期待値は非負である。 -/
theorem expect_nonneg {X : Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) : 0 ≤ P.expect X :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (P.nonneg ω) (h ω)

/-- 期待値は単調である：どの結果でも `X ≤ Y` なら、`E[X] ≤ E[Y]`。 -/
theorem expect_mono {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) : P.expect X ≤ P.expect Y :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (P.nonneg ω)

end FinProb

/-! ## Mathlib の測度論との対応 -/

open MeasureTheory in
/-- 有限の型の上の確率測度 `μ` による積分は、1 点集合の測度 `μ.real {ω}` で重みをつけた有限和である。
有限の型の上の関数は可積分なので、Mathlib の `integral_fintype` の仮定を満たす。 -/
theorem integral_eq_sum {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) :
    ∫ ω, f ω ∂μ = ∑ ω, μ.real {ω} * f ω := by
  rw [integral_fintype (Integrable.of_finite)]
  rfl

/-! ## 金融数学への接続：リスク中立確率 -/

namespace Binomial

/-- 第6章の 1 期間の二項モデル（係数は実数）のリスク中立確率を、結果 `true`（上がる）と
`false`（下がる）の上の確率にする。`0 < q < 1` は第6章で証明した。 -/
noncomputable def riskNeutral (m : OnePeriodBinomial ℝ) : FinProb Bool where
  prob ω := if ω then m.q else 1 - m.q
  nonneg ω := by
    cases ω
    · simp only [Bool.false_eq_true, ite_false]
      linarith [m.q_lt_one]
    · simp only [ite_true]
      exact le_of_lt m.q_pos
  sum_one := by simp

/-- 危険資産の 1 期後の価格：今日の価格 `s₀` に、上がれば `u`、下がれば `d` を掛ける。 -/
def stock (m : OnePeriodBinomial ℝ) (s₀ : ℝ) (ω : Bool) : ℝ :=
  s₀ * (if ω then m.u else m.d)

/-- リスク中立確率のもとで、危険資産の 1 期後の価格の期待値は、今日の価格の `(1 + r)` 倍である。
つまり、安全資産で割り引いた価格の期待値は、今日の価格に等しい。 -/
theorem expect_stock (m : OnePeriodBinomial ℝ) (s₀ : ℝ) :
    (riskNeutral m).expect (stock m s₀) = (1 + m.r) * s₀ := by
  have h : m.u - m.d ≠ 0 := sub_ne_zero.mpr (ne_of_gt m.d_lt_u)
  simp only [FinProb.expect, riskNeutral, stock, Fintype.univ_bool, Finset.mem_singleton,
    Bool.true_eq_false, not_false_eq_true, Finset.sum_insert, Finset.sum_singleton, ite_true,
    Bool.false_eq_true, ite_false, OnePeriodBinomial.q]
  field_simp
  ring

/-- 1 期後の支払いが非負の派生証券の、割り引いた期待値は非負である。 -/
theorem discounted_expect_nonneg (m : OnePeriodBinomial ℝ) {V : Bool → ℝ} (hV : ∀ ω, 0 ≤ V ω) :
    0 ≤ (riskNeutral m).expect V / (1 + m.r) :=
  div_nonneg ((riskNeutral m).expect_nonneg hV) (by linarith [m.d_pos, m.d_lt])

end Binomial

end LagrangeAcademy.Ch08

end
