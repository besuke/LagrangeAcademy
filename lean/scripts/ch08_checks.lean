/-
  第8章の確認用スクリプト。ライブラリには入れない（lake build の対象ではない）。
  `lean/` で次を実行すると、各行の結果が表示される。
    lake env lean scripts/ch08_checks.lean
  いくつかの定義は、Lean が受け付けない例である。実行するとエラーが出る。
  どの行も、すぐに終わる計算だけを置く。
-/
import LagrangeAcademy
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Martingale.Basic

open LagrangeAcademy.Ch08

-- 1. 確率の和が 1 でない関数では、FinProb の要素を作れない
noncomputable def rejected_prob : FinProb Bool where
  prob _ := 1 / 3
  nonneg _ := by norm_num
  sum_one := by norm_num

-- 2. Mathlib の積分の定理は、可積分性を仮定に置いている（無限の測度では成り立たないため）
#check @MeasureTheory.integral_fintype

-- 3. Mathlib のマルチンゲールの定義：適合していて、s ≤ t なら条件つき期待値 μ[f t | ℱ s] が f s にほぼ確実に等しい
#print MeasureTheory.Martingale

-- 4. Mathlib v4.35.0 にある Brownian motion の定義
#print ProbabilityTheory.IsPreBrownianReal
#print ProbabilityTheory.IsBrownianReal

-- 5. Brownian motion の増分の分布についての Mathlib の定理と、その公理への依存
#check @ProbabilityTheory.IsPreBrownianReal.hasLaw_sub
#print axioms ProbabilityTheory.IsPreBrownianReal.hasLaw_sub
