/-
  第11章の確認用スクリプト。ライブラリには入れない（lake build の対象ではない）。
  `lean/` で次を実行すると、各行の結果が表示される。
    lake env lean scripts/ch11_checks.lean
  1 つの定義は、Lean が受け付けない例である。実行するとエラーが出る。
  どの行も、すぐに終わる計算だけを置く。
-/
import LagrangeAcademy

open LagrangeAcademy.Ch10 LagrangeAcademy.Ch11

-- 1. 正規化（名前は normalizeBy。Mathlib の normalize と別）には、市場の資産であるニューメレールが要る（外から与えた正の関数では正規化できない）
#check @normalizeBy

-- 2. 状態価格から確率を作るには、正の状態価格 ψ と、すべての資産（ニューメレールを含む）の価格の表し方 hp が要る
#check @numeraireProb

-- 3. コールをニューメレールにしようとすると、下がる状態の支払い 0 が正であることを示せない
noncomputable def rejected_callNumeraire : Numeraire twoStateCall where
  n := 2
  price_pos := by norm_num [twoStateCall]
  pay_pos ω := by cases ω <;> norm_num [twoStateCall]

-- 4. ニューメレールの変更の公式を、2 状態の例の数で確かめる：Q^S(上) = Q^B(上) * (120/100) / (1/(19/20))
example : (29 / 50 : ℝ) = 29 / 57 * ((120 / 100) / (1 / (19 / 20))) := by norm_num
