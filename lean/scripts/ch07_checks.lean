/-
  第7章の確認用スクリプト。ライブラリには入れない（lake build の対象ではない）。
  `lean/` で次を実行すると、各行の結果が表示される。
    lake env lean scripts/ch07_checks.lean
  いくつかの行は、Lean が受け付けない例である。実行するとエラーが出る。
  どの行も、すぐに終わる計算だけを置く。
-/
import LagrangeAcademy

-- 1. 有理数は正確に計算できる
#eval (1 / 10 + 2 / 10 : ℚ)

-- 2. 浮動小数点数では 0.1 + 0.2 は 0.3 にならない（2 進数の丸め）
#eval (0.1 + 0.2 : Float)
#eval (0.1 + 0.2 : Float) == 0.3

-- 3. 浮動小数点数の足し算は結合的でない
#eval ((0.1 + 0.2) + 0.3 : Float) == 0.1 + (0.2 + 0.3)
#eval ((1e16 : Float) + 1) - 1e16

-- 4. IEEE 754 の比較 == では 0.0 と -0.0 は等しい（ライブラリの float_zero_ne_neg_zero と比べる）
#eval (0.0 : Float) == -0.0

-- 5. Float は IEEE 754 の倍精度のビット列のモデルを包んだ構造体。#eval はモデルではなく C の演算で計算する
#print Float
#print Float.Model

-- 6. 偽の等式は rfl では閉じない
example : (0.1 + 0.2 : Float) = 0.3 := rfl

-- 7. 実数は、コーシー列の同値類（Mathlib の構成）を包んだ構造体である
#print Real

-- 8. #eval は、Mathlib の表示用のインスタンス（unsafe）で、内部のコーシー列を表示するだけで、小数の値は出さない
#eval (1 : ℝ) + 1

-- 9. 実数の等号の Decidable のインスタンスは noncomputable（選択公理による）で、decide はそれを計算できない
example : (1 : ℝ) + 1 = 2 := by decide

-- 10. 有理数の等式を decide で示そうとした記録（実行するコードとしては置かない）
--    2026-11-13 に、ライブラリの rat_add を `by decide` で書いたとき、lake build は次のエラーを出した。
--      Tactic `decide` failed to reduce
--        @decide (1 / 10 + 2 / 10 = 3 / 10) (instDecidableEqRat (1 / 10 + 2 / 10) (3 / 10))
--      to `true` or `false`.
--      ... reduction got stuck at
--        match ((1 / 10).add (2 / 10)).num, (Rat.mul 3 (Rat.inv 10)).num with ...
--    rat_add は norm_num で証明した。
