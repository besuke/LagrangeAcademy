/-
  第1章の確認用スクリプト。ライブラリには入れない（lake build の対象ではない）。
  `lean/` で次を実行すると、各行の結果が表示される。
    lake env lean scripts/ch01_checks.lean
  このファイルの 4 つの定理のうち 3 つは、Lean が受け付けない例である。実行するとエラーが出る。
-/
import LagrangeAcademy

open LagrangeAcademy.Ch01

-- 1. 計算する：個別の値と、1000 個の n でのテスト
#eval sumTo 10
#eval (List.range 1000).all (fun n => 2 * sumTo n == n * (n + 1))

-- 2. decide は決定手続きである：有限の範囲を持たない全称命題には使えない
theorem rejected_unbounded : ∀ n, 2 * sumTo n = n * (n + 1) := by
  decide

-- 3. decide は偽の命題を計算で偽と判定する
theorem rejected_false_bounded : ∀ n, n < 10 → 2 * sumTo n = n * n := by
  decide

-- 4. 書き換えの手順を誤ると、検査は通らない（この章のコードを書く途中で実際に起きた誤り）
theorem rejected_rewrite (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumTo, Nat.mul_add, ih, Nat.mul_comm 2 (n + 1), ← Nat.mul_add, Nat.mul_comm]

-- 5. エラーになった定理は sorryAx に依存すると記録される
#print axioms rejected_false_bounded
#print axioms rejected_rewrite

-- 6. native_decide は受け付けられるが、コンパイラを信頼する公理が加わる（第4章）
theorem accepted_by_native_decide : ∀ n, n < 100 → 2 * sumTo n = n * (n + 1) := by
  native_decide

#print axioms accepted_by_native_decide
