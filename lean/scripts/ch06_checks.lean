/-
  第6章の確認用スクリプト。ライブラリには入れない（lake build の対象ではない）。
  `lean/` で次を実行すると、各行の結果が表示される。
    lake env lean scripts/ch06_checks.lean
  いくつかの定義と定理は、Lean が受け付けない例である。実行するとエラーが出る。
-/
import LagrangeAcademy

open LagrangeAcademy.Ch05 LagrangeAcademy.Ch06

-- 1. 構造体は、構成子が 1 つの帰納型である
#print PosNat

-- 2. Decidable も構造体の型クラスで、真理値 decide と、それが命題を反映することの証明を項に持つ
#print Decidable

-- 3. インスタンスの検索：IsEven 10 の Decidable のインスタンスとして何が見つかるか
#synth Decidable (IsEven 10)

-- 4. 構造体の項の証明が作れない値は、PosNat の項にできない
def rejected_zero : PosNat := ⟨0, by decide⟩

-- 5. 仮定 d < 1 + r を満たさない値では、OnePeriodBinomial の項を作れない
def rejected_model : OnePeriodBinomial ℚ where
  r := 1 / 100
  u := 12 / 10
  d := 11 / 10
  d_pos := by norm_num
  d_lt := by norm_num
  lt_u := by norm_num

-- 6. ℕ は可換環ではない（引き算が逆演算にならない）ので、add_sq_ring のインスタンスが見つからない
#synth CommRing ℕ
example (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := LagrangeAcademy.Ch06.add_sq_ring a b
