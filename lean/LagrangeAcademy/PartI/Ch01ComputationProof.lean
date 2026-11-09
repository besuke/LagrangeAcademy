module

/-!
# 第1章 計算と証明

Lean 本体だけを使う（Mathlib は使わない）。

- `sumTo n` は 0 から `n` までの自然数の和である。
- 同じ和について、個別の値の計算（`sumTo_ten`）、有限個の場合の検査
  （`two_mul_sumTo_of_lt_100`）、すべての `n` についての証明（`two_mul_sumTo`）を並べ、
  何が違うかを見る。
- すべての `n` についての同じ命題を、書き換えを人が 1 つずつ与える証明（`two_mul_sumTo`）と、
  自動証明 `grind` に探させる証明（`two_mul_sumTo'`）の 2 通りで示す。カーネルが検査するのは、
  どちらの場合も出来上がった証明項である。
- 金融数学への接続として、整数の価格でのペイオフの恒等式（`call_sub_put_payoff`）を示す。
  実数に広げるのは第7章、価格の関係（プット・コール・パリティ）は第II部で扱う。

Lean が受け付けない例は、ライブラリに入れず `scripts/ch01_checks.lean` に置く。
-/

@[expose] public section

namespace LagrangeAcademy.Ch01

/-- 0 から `n` までの自然数の和 `0 + 1 + ⋯ + n`。 -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

/-- 個別の値：定義を計算すれば、両辺は同じ値になる。 -/
theorem sumTo_ten : sumTo 10 = 55 := rfl

/-- 有限個の場合：`n < 100` の 100 通りを、決定手続き `decide` がすべて計算して確かめる。 -/
theorem two_mul_sumTo_of_lt_100 : ∀ n, n < 100 → 2 * sumTo n = n * (n + 1) := by
  decide

/-- すべての `n`：帰納法の各段で、どの等式で書き換えるかを人が与える。 -/
theorem two_mul_sumTo (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumTo, Nat.mul_add, ih, Nat.mul_comm 2 (n + 1), Nat.mul_comm n (n + 1), ← Nat.mul_add]

/-- 同じ命題を、自動証明 `grind` に探させる。人が与えるのは帰納法の枠組みだけである。 -/
theorem two_mul_sumTo' (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => grind [sumTo]

/-- 整数の価格で、満期のコールのペイオフからプットのペイオフを引くと `s - k` になる
（`s` は満期の原資産価格、`k` は行使価格）。 -/
theorem call_sub_put_payoff (s k : Int) : max (s - k) 0 - max (k - s) 0 = s - k := by
  omega

end LagrangeAcademy.Ch01

end
