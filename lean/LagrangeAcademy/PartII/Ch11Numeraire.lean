module

public import LagrangeAcademy.PartII.Ch10FiniteMarket
public import LagrangeAcademy.PartI.Ch08Probability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# 第11章 ニューメレールと価格の正規化

第10章の 1 期間の有限市場 `FiniteMarket` で、状態価格 → 基準資産の選択 → ニューメレール →
確率測度の順に進む。第10章と第8章の定義・定理は変えずに使う。

- ニューメレール：市場で取引される資産で、今日の価格も満期のどの状態の支払いも正のもの
  （`Numeraire`）。外から与えた正の関数（割引係数など）は、ここではニューメレールと呼ばない。
- 価格の正規化（`normalizeBy`）：価格と支払いをニューメレールの価格と支払いで割る。裁定かどうかは
  変わらない（`isArbitrage_normalize_iff`、`noArbitrage_normalize_iff`）。この部分は状態価格を
  仮定しない。
- 状態価格からの確率測度：正の状態価格 `ψ` とニューメレール `N` から、
  `Q^N(ω) = ψ ω * pay N ω / price N` が第8章の `FinProb` になる（`numeraireProb`）。正規化した
  価格は `Q^N` のもとでの期待値である（`price_div_eq_expect`）。逆に、そのような正の確率があれば
  無裁定である（`noArbitrage_of_numeraireProb`）。
- ニューメレールの変更：`Q^M(ω) = Q^N(ω) * (pay M ω / price M) / (pay N ω / price N)`
  （`numeraireProb_change`）。この密度の `Q^N` での期待値は 1 である（`expect_density_eq_one`）。
- 第10章の 2 状態の例：状態価格は資産の価格から一意に決まる（`twoState_statePrice_unique`）。
  債券と株をニューメレールにした確率を計算する。債券の場合は、第6章の `q`（と第8章の
  `riskNeutral`）に一致する（`twoState_bondProb_eq_q`、`twoState_bondProb_eq_riskNeutral`）。
  コールはニューメレールにならない（`twoStateCall_not_numeraire`）。

割引債、マネーマーケット口座、短期金利の関係は、時間の構造を扱う章で扱う。
-/

@[expose] public section

namespace LagrangeAcademy.Ch11

open LagrangeAcademy.Ch10 LagrangeAcademy.Ch10.FiniteMarket
open LagrangeAcademy.Ch08 LagrangeAcademy.Ch06

variable {I Ω : Type*} [Fintype I] [Fintype Ω]

/-! ## ニューメレール -/

/-- 市場 `M` のニューメレール：市場で取引される資産 `n` で、今日の価格が正で、満期のどの状態でも
支払いが正のもの。 -/
structure Numeraire (M : FiniteMarket I Ω) where
  n : I
  price_pos : 0 < M.price n
  pay_pos : ∀ ω, 0 < M.pay n ω

/-! ## 価格の正規化 -/

/-- ニューメレール `N` で正規化した市場：価格を `price N` で、支払いを `pay N ω` で割る。 -/
noncomputable def normalizeBy (M : FiniteMarket I Ω) (N : Numeraire M) : FiniteMarket I Ω where
  price i := M.price i / M.price N.n
  pay i ω := M.pay i ω / M.pay N.n ω

variable (M : FiniteMarket I Ω) (N : Numeraire M)

/-- 正規化した市場で、ニューメレール自身の価格は 1 である。 -/
theorem normalize_price_self : (normalizeBy M N).price N.n = 1 :=
  div_self (ne_of_gt N.price_pos)

/-- 正規化した市場で、ニューメレール自身の支払いは、どの状態でも 1 である。 -/
theorem normalize_pay_self (ω : Ω) : (normalizeBy M N).pay N.n ω = 1 :=
  div_self (ne_of_gt (N.pay_pos ω))

/-- 正規化した費用は、もとの費用をニューメレールの価格で割ったものである。 -/
theorem cost_normalize (θ : I → ℝ) : (normalizeBy M N).cost θ = M.cost θ / M.price N.n := by
  unfold cost normalizeBy
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- 正規化した支払いは、もとの支払いをニューメレールの支払いで割ったものである。 -/
theorem payoff_normalize (θ : I → ℝ) (ω : Ω) :
    (normalizeBy M N).payoff θ ω = M.payoff θ ω / M.pay N.n ω := by
  unfold payoff normalizeBy
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- 正の数で割っても、0 との大小は変わらない。 -/
theorem div_sign {x c : ℝ} (hc : 0 < c) :
    (x / c ≤ 0 ↔ x ≤ 0) ∧ (0 ≤ x / c ↔ 0 ≤ x) ∧ (x / c < 0 ↔ x < 0) ∧ (0 < x / c ↔ 0 < x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hc, zero_mul]
  · rw [le_div_iff₀ hc, zero_mul]
  · rw [div_lt_iff₀ hc, zero_mul]
  · rw [lt_div_iff₀ hc, zero_mul]

/-- 正規化しても、裁定かどうかは変わらない。状態価格は仮定しない。 -/
theorem isArbitrage_normalize_iff (θ : I → ℝ) :
    (normalizeBy M N).IsArbitrage θ ↔ M.IsArbitrage θ := by
  have hp := div_sign (x := M.cost θ) N.price_pos
  have hω := fun ω => div_sign (x := M.payoff θ ω) (N.pay_pos ω)
  unfold IsArbitrage
  simp only [cost_normalize, payoff_normalize]
  rw [hp.1, hp.2.2.1]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun ω => (hω ω).2.1.mp (h2 ω), ?_⟩
    rcases h3 with h | ⟨ω, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨ω, (hω ω).2.2.2.mp h⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun ω => (hω ω).2.1.mpr (h2 ω), ?_⟩
    rcases h3 with h | ⟨ω, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨ω, (hω ω).2.2.2.mpr h⟩

/-- 正規化しても、無裁定かどうかは変わらない。ニューメレールの選び方によらない。 -/
theorem noArbitrage_normalize_iff : (normalizeBy M N).NoArbitrage ↔ M.NoArbitrage := by
  unfold NoArbitrage
  simp only [isArbitrage_normalize_iff]

/-! ## 状態価格からの確率測度 -/

variable {M}

/-- 正の状態価格 `ψ`（第10章）とニューメレール `N` から作る確率：
`Q^N(ω) = ψ ω * pay N ω / price N`。和が 1 になるのは、ニューメレールの価格も状態価格で
表せる（`hp N.n`）からである。 -/
noncomputable def numeraireProb (N : Numeraire M) {ψ : Ω → ℝ} (hψ : ∀ ω, 0 < ψ ω)
    (hp : ∀ i, M.price i = ∑ ω, ψ ω * M.pay i ω) : FinProb Ω where
  prob ω := ψ ω * M.pay N.n ω / M.price N.n
  nonneg ω := div_nonneg (mul_nonneg (hψ ω).le (N.pay_pos ω).le) N.price_pos.le
  sum_one := by
    rw [← Finset.sum_div, ← hp N.n]
    exact div_self (ne_of_gt N.price_pos)

/-- `Q^N` のどの状態の確率も正である。 -/
theorem numeraireProb_pos (N : Numeraire M) {ψ : Ω → ℝ} (hψ : ∀ ω, 0 < ψ ω)
    (hp : ∀ i, M.price i = ∑ ω, ψ ω * M.pay i ω) (ω : Ω) : 0 < (numeraireProb N hψ hp).prob ω :=
  div_pos (mul_pos (hψ ω) (N.pay_pos ω)) N.price_pos

/-- ニューメレールで測った価格は、`Q^N` のもとでの、ニューメレールで測った支払いの期待値である：
`price i / price N = E_{Q^N}[pay i / pay N]`。 -/
theorem price_div_eq_expect (N : Numeraire M) {ψ : Ω → ℝ} (hψ : ∀ ω, 0 < ψ ω)
    (hp : ∀ i, M.price i = ∑ ω, ψ ω * M.pay i ω) (i : I) :
    M.price i / M.price N.n
      = (numeraireProb N hψ hp).expect (fun ω => M.pay i ω / M.pay N.n ω) := by
  unfold FinProb.expect numeraireProb
  rw [hp i, Finset.sum_div]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have h1 := ne_of_gt (N.pay_pos ω)
  have h2 := ne_of_gt N.price_pos
  field_simp

/-- 逆向き：ニューメレール `N` と、どの状態でも正の確率 `Q` があって、ニューメレールで測った価格が
`Q` のもとでの期待値になるなら、市場は無裁定である。状態価格 `price N * Q ω / pay N ω` を作り、
第10章の `noArbitrage_of_statePrice` を使う。 -/
theorem noArbitrage_of_numeraireProb (N : Numeraire M) (Q : FinProb Ω) (hQ : ∀ ω, 0 < Q.prob ω)
    (hprice : ∀ i, M.price i / M.price N.n = Q.expect (fun ω => M.pay i ω / M.pay N.n ω)) :
    M.NoArbitrage := by
  refine noArbitrage_of_statePrice (ψ := fun ω => M.price N.n * Q.prob ω / M.pay N.n ω)
    (fun ω => div_pos (mul_pos N.price_pos (hQ ω)) (N.pay_pos ω)) fun i => ?_
  have h := hprice i
  have h2 := ne_of_gt N.price_pos
  rw [div_eq_iff h2] at h
  rw [h]
  unfold FinProb.expect
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have h1 := ne_of_gt (N.pay_pos ω)
  field_simp

/-! ## ニューメレールの変更 -/

/-- ニューメレールの変更の公式：2 つのニューメレール `N`、`N'` について、
`Q^{N'}(ω) = Q^N(ω) * (pay N' ω / price N') / (pay N ω / price N)`。 -/
theorem numeraireProb_change (N N' : Numeraire M) {ψ : Ω → ℝ} (hψ : ∀ ω, 0 < ψ ω)
    (hp : ∀ i, M.price i = ∑ ω, ψ ω * M.pay i ω) (ω : Ω) :
    (numeraireProb N' hψ hp).prob ω
      = (numeraireProb N hψ hp).prob ω
        * ((M.pay N'.n ω / M.price N'.n) / (M.pay N.n ω / M.price N.n)) := by
  unfold numeraireProb
  have h1 := ne_of_gt (N.pay_pos ω)
  have h2 := ne_of_gt N.price_pos
  have h3 := ne_of_gt N'.price_pos
  field_simp

/-- ニューメレールの変更の密度 `(pay N' / price N') / (pay N / price N)` の、`Q^N` のもとでの
期待値は 1 である。 -/
theorem expect_density_eq_one (N N' : Numeraire M) {ψ : Ω → ℝ} (hψ : ∀ ω, 0 < ψ ω)
    (hp : ∀ i, M.price i = ∑ ω, ψ ω * M.pay i ω) :
    (numeraireProb N hψ hp).expect
      (fun ω => (M.pay N'.n ω / M.price N'.n) / (M.pay N.n ω / M.price N.n)) = 1 := by
  unfold FinProb.expect
  rw [← (numeraireProb N' hψ hp).sum_one]
  exact Finset.sum_congr rfl fun ω _ => (numeraireProb_change N N' hψ hp ω).symm

/-! ## 第10章の 2 状態の例 -/

/-- 第10章の 2 状態の市場（資産：`false` が債券、`true` が株。状態：`true` が上がる状態、
`false` が下がる状態）で、債券と株の価格を表す状態価格は、`ψ(上) = 29/60`、`ψ(下) = 7/15` に
限られる。資産の価格と支払いから、2 つの 1 次方程式を解いて求める。 -/
theorem twoState_statePrice_unique {ψ : Bool → ℝ}
    (hp : ∀ i, twoState.price i = ∑ ω, ψ ω * twoState.pay i ω) :
    ψ true = 29 / 60 ∧ ψ false = 7 / 15 := by
  have hb := hp false
  have hs := hp true
  simp [twoState] at hb hs
  constructor <;> linarith

/-- その状態価格。 -/
noncomputable def twoStatePsi : Bool → ℝ := fun ω => if ω then 29 / 60 else 7 / 15

theorem twoStatePsi_pos : ∀ ω, 0 < twoStatePsi ω := by
  intro ω; cases ω <;> norm_num [twoStatePsi]

theorem twoStatePsi_price : ∀ i, twoState.price i = ∑ ω, twoStatePsi ω * twoState.pay i ω := by
  intro i; cases i <;> simp [twoState, twoStatePsi] <;> norm_num

/-- 債券（資産 `false`）は、ニューメレールになる。 -/
noncomputable def twoStateBond : Numeraire twoState where
  n := false
  price_pos := by norm_num [twoState]
  pay_pos ω := by simp [twoState]

/-- 株（資産 `true`）も、ニューメレールになる。 -/
noncomputable def twoStateStock : Numeraire twoState where
  n := true
  price_pos := by norm_num [twoState]
  pay_pos ω := by cases ω <;> norm_num [twoState]

/-- 債券をニューメレールにした確率：`Q^B(上) = 29/57`、`Q^B(下) = 28/57`。 -/
theorem twoState_bondProb :
    (numeraireProb twoStateBond twoStatePsi_pos twoStatePsi_price).prob true = 29 / 57 ∧
    (numeraireProb twoStateBond twoStatePsi_pos twoStatePsi_price).prob false = 28 / 57 := by
  simp [numeraireProb, twoStateBond, twoState, twoStatePsi]
  constructor <;> norm_num

/-- 株をニューメレールにした確率：`Q^S(上) = 29/50`、`Q^S(下) = 21/50`。 -/
theorem twoState_stockProb :
    (numeraireProb twoStateStock twoStatePsi_pos twoStatePsi_price).prob true = 29 / 50 ∧
    (numeraireProb twoStateStock twoStatePsi_pos twoStatePsi_price).prob false = 21 / 50 := by
  simp [numeraireProb, twoStateStock, twoState, twoStatePsi]
  constructor <;> norm_num

/-- 第10章の 2 状態の市場を、第6章の 1 期間の二項モデルとして読む：債券の価格 `19/20` から
`1 + r = 20/19`、株の価格 `100` と支払い `120`、`90` から `u = 6/5`、`d = 9/10`。 -/
noncomputable def twoStateBinomial : OnePeriodBinomial ℝ where
  r := 1 / 19
  u := 6 / 5
  d := 9 / 10
  d_pos := by norm_num
  d_lt := by norm_num
  lt_u := by norm_num

/-- 債券をニューメレールにした確率は、第6章のリスク中立確率 `q` に一致する：
`Q^B(上) = q`、`Q^B(下) = 1 - q`。 -/
theorem twoState_bondProb_eq_q :
    (numeraireProb twoStateBond twoStatePsi_pos twoStatePsi_price).prob true
        = twoStateBinomial.q ∧
    (numeraireProb twoStateBond twoStatePsi_pos twoStatePsi_price).prob false
        = 1 - twoStateBinomial.q := by
  obtain ⟨h1, h2⟩ := twoState_bondProb
  rw [h1, h2]
  simp [OnePeriodBinomial.q, twoStateBinomial]
  constructor <;> norm_num

/-- 同じことを、第8章の `Binomial.riskNeutral` との一致として述べる。状態の順序（`true` が
上がる状態）は、第8章と同じである。 -/
theorem twoState_bondProb_eq_riskNeutral (ω : Bool) :
    (numeraireProb twoStateBond twoStatePsi_pos twoStatePsi_price).prob ω
      = (Binomial.riskNeutral twoStateBinomial).prob ω := by
  obtain ⟨h1, h2⟩ := twoState_bondProb_eq_q
  cases ω
  · rw [h2]; simp [Binomial.riskNeutral]
  · rw [h1]; simp [Binomial.riskNeutral]

/-! ## ニューメレールにならない資産 -/

/-- 第10章の 2 状態の市場に、行使価格 100 のコール（資産 `2`）を加えた合成の例。資産 `0` が債券、
`1` が株。コールの価格 `29/3` は、状態価格 `twoStatePsi` で表せる値にした。 -/
noncomputable def twoStateCall : FiniteMarket (Fin 3) Bool where
  price := ![19 / 20, 100, 29 / 3]
  pay := ![fun _ => 1, fun ω => if ω then 120 else 90, fun ω => if ω then 20 else 0]

/-- コールは、下がる状態で支払いが 0 なので、ニューメレールにならない。 -/
theorem twoStateCall_not_numeraire (N : Numeraire twoStateCall) : N.n ≠ 2 := by
  intro h
  have := N.pay_pos false
  rw [h] at this
  simp [twoStateCall] at this

end LagrangeAcademy.Ch11

end
