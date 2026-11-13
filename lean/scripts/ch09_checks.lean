/-
  第9章の確認用スクリプト。ライブラリには入れない（lake build の対象ではない）。
  `lean/` で次を実行すると、各行の結果が表示される。
    lake env lean scripts/ch09_checks.lean
  1 つの定義は、Lean が受け付けない例である。実行するとエラーが出る。
  どの行も、すぐに終わる計算だけを置く。
-/
import LagrangeAcademy

open LagrangeAcademy.Ch06 LagrangeAcademy.Ch08 LagrangeAcademy.Ch09

-- 1. 結論を導いた定理と、結論を仮定から読み出すだけの定理は、公理への依存では区別できない
#print axioms LagrangeAcademy.Ch08.Binomial.expect_stock
#print axioms expect_stock_of_spec

-- 2. 読み出すだけの定理の項は、構造体の射影である
#print expect_stock_of_spec

-- 3. 矛盾した仮定の構造体には、要素を作れない（1 + r < d と d < 1 + r を同時には示せない）
noncomputable def rejected_bad : BadBinomial where
  r := 0
  d := 2
  lt_d := by norm_num
  d_lt := by norm_num

-- 4. 矛盾した仮定から証明した「定理」も、公理への依存は標準の 3 つ以下である
#print axioms BadBinomial.anything
