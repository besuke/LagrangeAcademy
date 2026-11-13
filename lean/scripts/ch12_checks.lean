/-
  第12章の確認用スクリプト。ライブラリには入れない（lake build の対象ではない）。
  `lean/` で次を実行すると、各行の結果が表示される。
    lake env lean scripts/ch12_checks.lean
  1 つの例は、Lean が受け付けない例である。実行するとエラーが出る。
  どの行も、すぐに終わる計算だけを置く。
-/
import LagrangeAcademy

open LagrangeAcademy.Ch10 LagrangeAcademy.Ch12

-- 1. 中心の定理が使う Mathlib の強い分離定理（仮定：凸・コンパクトな s と、凸・閉な t が交わらない）
#check @geometric_hahn_banach_compact_closed

-- 2. 中心の定理と、その公理への依存
#check @exists_statePrice_of_noArbitrage
#print axioms exists_statePrice_of_noArbitrage

-- 3. 3 状態の拡大市場で、π = 7/10 はちょうど裁定になる境界である（7/10 で無裁定とはいえない）
example : ¬ (threeStateExt (7 / 10)).NoArbitrage := fun h =>
  h _ (threeStateExt_isArbitrage_sell le_rfl)

-- 4. 正の状態価格の構成は、π = 7/10 では最後の重み 3/10 + 2(1/4 - π)/3 が 0 になって失敗する
example : (0 : ℝ) < 3 / 10 + 2 * (1 / 4 - 7 / 10) / 3 := by norm_num
