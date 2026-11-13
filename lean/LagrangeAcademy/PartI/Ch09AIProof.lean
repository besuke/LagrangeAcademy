module

public import LagrangeAcademy.PartI.Ch08Probability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# 第9章 AIと形式的証明

AI が数学的証明を生成する時代に、Lean はどのような役割を果たすのか。カーネルは、証明が命題に
合っていることを確かめる。命題が意図に合っていることは確かめない。この章では、カーネルの検査を
通るが、意図した主張を述べていない定理の型を、小さな例で組み立てる。

- 結論を構造体の項に置き、射影で読み出す定理（`expect_stock_of_spec`）。第8章の
  `Binomial.expect_stock` は結論を導いていた。仕様の構造体が実際に満たされることは、
  第8章の定理から示せる（`stockMartingaleSpec_holds`）。
- 矛盾した仮定からは何でも証明できる（`BadBinomial.anything`）。仮定が満たせることを示しておく
  （`badBinomial_isEmpty`、`onePeriodBinomial_nonempty`）。
- 弱い命題へのすり替え：`∃ p, 0 < p ∧ p < 1` は正しいが、リスク中立確率 `q` については何も
  述べない（`exists_prob_weak`）。第6章の `q_pos`・`q_lt_one` と比べる。

どの定理も、標準の 3 つの公理だけに依存する。`#print axioms` では、これらの型の問題は見つからない。
-/

@[expose] public section

namespace LagrangeAcademy.Ch09

open LagrangeAcademy.Ch06 LagrangeAcademy.Ch08 LagrangeAcademy.Ch08.Binomial

/-! ## 結論を構造体の項に置く -/

/-- 1 期間の二項モデルについての「仕様」：危険資産の割り引いた価格の期待値が今日の価格に等しい
ことを、構造体の項として置く。これは仮定であり、証明ではない。 -/
structure StockMartingaleSpec (m : OnePeriodBinomial ℝ) : Prop where
  martingale : ∀ s₀ : ℝ, (riskNeutral m).expect (stock m s₀) = (1 + m.r) * s₀

/-- 仕様の項を読み出すだけの定理。カーネルの検査は通るが、何も導いていない。命題は第8章の
`Binomial.expect_stock` と同じ結論を述べるが、仮定 `h` に結論そのものが入っている。 -/
theorem expect_stock_of_spec (m : OnePeriodBinomial ℝ) (h : StockMartingaleSpec m) (s₀ : ℝ) :
    (riskNeutral m).expect (stock m s₀) = (1 + m.r) * s₀ :=
  h.martingale s₀

/-- 仕様は、第8章の定理によって、どのモデルでも満たされる。これで、上の定理の仮定 `h` を
外すことができる。 -/
theorem stockMartingaleSpec_holds (m : OnePeriodBinomial ℝ) : StockMartingaleSpec m :=
  ⟨expect_stock m⟩

/-! ## 矛盾した仮定 -/

/-- 誤って書いた仮定：`1 + r < d` と `d < 1 + r` を同時に要求している。 -/
structure BadBinomial where
  r : ℝ
  d : ℝ
  lt_d : 1 + r < d
  d_lt : d < 1 + r

/-- 矛盾した仮定からは、どんな命題も証明できる。カーネルの検査は通る。 -/
theorem BadBinomial.anything (m : BadBinomial) (P : Prop) : P :=
  absurd (lt_trans m.lt_d m.d_lt) (lt_irrefl _)

/-- `BadBinomial` の要素は存在しない。仮定が満たせないことを、定理として示せる。 -/
theorem badBinomial_isEmpty : IsEmpty BadBinomial :=
  ⟨fun m => BadBinomial.anything m False⟩

/-- 第6章の `OnePeriodBinomial` の仮定は満たせる。合成の値の例 `exampleModel` が要素である。 -/
theorem onePeriodBinomial_nonempty : Nonempty (OnePeriodBinomial ℚ) :=
  ⟨exampleModel⟩

/-! ## 弱い命題へのすり替え -/

/-- `0` と `1` の間に数がある。正しいが、リスク中立確率 `q` については何も述べていない。
第6章の `OnePeriodBinomial.q_pos` と `OnePeriodBinomial.q_lt_one` は、特定の `m.q` について述べる。 -/
theorem exists_prob_weak : ∃ p : ℝ, 0 < p ∧ p < 1 :=
  ⟨1 / 2, by norm_num, by norm_num⟩

end LagrangeAcademy.Ch09

end
