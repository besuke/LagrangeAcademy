/-
  第10章の確認用スクリプト。ライブラリには入れない（lake build の対象ではない）。
  `lean/` で次を実行すると、各行の結果が表示される。
    lake env lean scripts/ch10_checks.lean
  1 つの例は、Lean が受け付けない例である。実行するとエラーが出る。
  どの行も、すぐに終わる計算だけを置く。
-/
import LagrangeAcademy

open LagrangeAcademy.Ch10 LagrangeAcademy.Ch10.FiniteMarket

-- 1. 株が割高な市場（合成の値）：株の価格 130 は、満期の支払い（120 か 90）のどれよりも大きい
noncomputable def overpriced : FiniteMarket Bool Bool where
  price i := if i then 130 else 19 / 20
  pay i ω := if i then (if ω then 120 else 90) else 1

-- 2. 株を 1 単位売り、債券を 120 単位買うと裁定になる（費用 -16、支払いは 30 か 0）
example : overpriced.IsArbitrage (fun i => if i then -1 else 120) := by
  refine ⟨?_, ?_, Or.inl ?_⟩
  · simp [overpriced, cost]; norm_num
  · intro ω; cases ω <;> norm_num [overpriced, payoff]
  · simp [overpriced, cost]; norm_num

example : ¬ overpriced.NoArbitrage := fun h =>
  h (fun i => if i then -1 else 120) ⟨by simp [overpriced, cost]; norm_num,
    fun ω => by cases ω <;> norm_num [overpriced, payoff],
    Or.inl (by simp [overpriced, cost]; norm_num)⟩

-- 3. 状態価格は正でなければならない：ある状態の重みが 0 では、noArbitrage_of_statePrice の仮定を満たせない
example : ∀ ω : Fin 3, (0 : ℝ) < ![2 / 5, 0, 3 / 10] ω := by
  intro ω; fin_cases ω <;> norm_num

-- 4. 一物一価・支配・パリティは、無裁定の仮定 hna を引数に持つ
#check @law_of_one_price
#check @put_call_parity
#check @call_price_convex
