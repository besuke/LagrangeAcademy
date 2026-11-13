module

public import LagrangeAcademy.PartI.Ch07RealsFloats
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# 第10章 有限市場における無裁定と価格の一意性

1 期間で、満期の状態も取引できる資産も有限個の市場を考える。摩擦はなく、どの資産も任意の実数
単位で売買（空売りを含む）できる。状態はすべて経済的に可能な状態とみなす（裁定の定義で、
すべての状態の支払いを数える）。

- 定義：`FiniteMarket`、`cost`、`payoff`、`IsArbitrage`、`NoArbitrage`、`Replicates`、
  `IsComplete`、1 つの資産を 1 単位持つポートフォリオ `unit`。
- 線形性：`cost_combo`、`payoff_combo` など。
- 無裁定からの帰結：一物一価（`law_of_one_price`）、複製の費用の一意性
  （`replication_price_unique`）、支配関係（`cost_le_of_payoff_le`、
  `cost_lt_of_payoff_le_of_lt`）、価格の上下限（`price_between_of_dominated`）。
- 具体的な契約：プット・コール・パリティ（`put_call_parity`）、コールの価格の行使価格についての
  単調性と差の上限（`call_price_antitone`、`call_spread_price_le`）、凸性（`call_price_convex`）。
- 状態価格（正の重み）があれば無裁定（`noArbitrage_of_statePrice`）。逆向きは扱わない。
- 一意性と完備性の区別：2 状態の市場は完備（`twoState_complete`）、3 状態の例は無裁定だが
  不完備（`threeState_noArbitrage`、`threeState_not_complete`）。

ニューメレール、割引、確率測度はこの章では使わない。債券は「満期にどの状態でも 1 を払う資産」
で、今日の価格は市場の 1 つのデータである。
-/

@[expose] public section

namespace LagrangeAcademy.Ch10

/-! ## 市場とポートフォリオ -/

/-- 1 期間の有限市場：資産 `i` の今日の価格 `price i` と、満期の状態 `ω` での支払い `pay i ω`。 -/
structure FiniteMarket (I Ω : Type*) [Fintype I] [Fintype Ω] where
  price : I → ℝ
  pay : I → Ω → ℝ

namespace FiniteMarket

variable {I Ω : Type*} [Fintype I] [Fintype Ω] (M : FiniteMarket I Ω)

/-- ポートフォリオ `θ`（資産 `i` を `θ i` 単位持つ）の初期費用。 -/
def cost (θ : I → ℝ) : ℝ := ∑ i, θ i * M.price i

/-- ポートフォリオ `θ` の、状態 `ω` での満期の支払い。 -/
def payoff (θ : I → ℝ) (ω : Ω) : ℝ := ∑ i, θ i * M.pay i ω

/-- 裁定：費用が 0 以下で、どの状態でも支払いが非負で、費用が負か、ある状態で支払いが正。
第2章の `IsArbitrage` と同じ形の条件を、実数の費用と支払いについて述べる。 -/
def IsArbitrage (θ : I → ℝ) : Prop :=
  M.cost θ ≤ 0 ∧ (∀ ω, 0 ≤ M.payoff θ ω) ∧ (M.cost θ < 0 ∨ ∃ ω, 0 < M.payoff θ ω)

/-- 無裁定：裁定になるポートフォリオがない。定理では仮定として置く。 -/
def NoArbitrage : Prop := ∀ θ, ¬ M.IsArbitrage θ

/-- ポートフォリオ `θ` が支払い `C` を複製する：どの状態でも支払いが `C` に等しい。 -/
def Replicates (θ : I → ℝ) (C : Ω → ℝ) : Prop := ∀ ω, M.payoff θ ω = C ω

/-- 市場が完備である：どの支払いも、あるポートフォリオで複製できる。 -/
def IsComplete : Prop := ∀ C : Ω → ℝ, ∃ θ, M.Replicates θ C

/-! ## 線形性 -/

/-- 費用は、ポートフォリオの線形結合を保つ。 -/
theorem cost_combo (a b : ℝ) (θ θ' : I → ℝ) :
    M.cost (fun i => a * θ i + b * θ' i) = a * M.cost θ + b * M.cost θ' := by
  unfold cost
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- 支払いは、ポートフォリオの線形結合を保つ。 -/
theorem payoff_combo (a b : ℝ) (θ θ' : I → ℝ) (ω : Ω) :
    M.payoff (fun i => a * θ i + b * θ' i) ω = a * M.payoff θ ω + b * M.payoff θ' ω := by
  unfold payoff
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- 差の費用は、費用の差である。 -/
theorem cost_sub (θ θ' : I → ℝ) : M.cost (fun i => θ i - θ' i) = M.cost θ - M.cost θ' := by
  have h := M.cost_combo 1 (-1) θ θ'
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at h
  exact h

/-- 差の支払いは、支払いの差である。 -/
theorem payoff_sub (θ θ' : I → ℝ) (ω : Ω) :
    M.payoff (fun i => θ i - θ' i) ω = M.payoff θ ω - M.payoff θ' ω := by
  have h := M.payoff_combo 1 (-1) θ θ' ω
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at h
  exact h

/-! ## 無裁定からの帰結 -/

variable {M}

/-- 一物一価：無裁定なら、どの状態でも支払いが等しい 2 つのポートフォリオは、費用も等しい。 -/
theorem law_of_one_price (hna : M.NoArbitrage) {θ θ' : I → ℝ}
    (h : ∀ ω, M.payoff θ ω = M.payoff θ' ω) : M.cost θ = M.cost θ' := by
  rcases lt_trichotomy (M.cost θ) (M.cost θ') with hlt | heq | hgt
  · -- θ を買って θ' を売ると、今日お金を受け取り、満期の支払いは 0
    refine absurd ⟨?_, ?_, Or.inl ?_⟩ (hna fun i => θ i - θ' i)
    · rw [M.cost_sub]; linarith
    · intro ω; rw [M.payoff_sub, h ω, sub_self]
    · rw [M.cost_sub]; linarith
  · exact heq
  · refine absurd ⟨?_, ?_, Or.inl ?_⟩ (hna fun i => θ' i - θ i)
    · rw [M.cost_sub]; linarith
    · intro ω; rw [M.payoff_sub, h ω, sub_self]
    · rw [M.cost_sub]; linarith

/-- 価格の一意性：無裁定なら、同じ支払い `C` を複製する 2 つのポートフォリオの費用は等しい。
複製できる支払いの価格は 1 つに決まる。どの支払いも複製できること（完備性）は述べていない。 -/
theorem replication_price_unique (hna : M.NoArbitrage) {θ θ' : I → ℝ} {C : Ω → ℝ}
    (h : M.Replicates θ C) (h' : M.Replicates θ' C) : M.cost θ = M.cost θ' :=
  law_of_one_price hna fun ω => (h ω).trans (h' ω).symm

/-- 弱い支配：無裁定なら、どの状態でも支払いが小さくないポートフォリオは、費用も小さくない。 -/
theorem cost_le_of_payoff_le (hna : M.NoArbitrage) {θ θ' : I → ℝ}
    (h : ∀ ω, M.payoff θ ω ≤ M.payoff θ' ω) : M.cost θ ≤ M.cost θ' := by
  by_contra hlt
  replace hlt := lt_of_not_ge hlt
  refine hna (fun i => θ' i - θ i) ⟨?_, ?_, Or.inl ?_⟩
  · rw [M.cost_sub]; linarith
  · intro ω; rw [M.payoff_sub]; linarith [h ω]
  · rw [M.cost_sub]; linarith

/-- 強い支配：無裁定なら、どの状態でも支払いが小さくなく、ある状態で真に大きいポートフォリオは、
費用も真に大きい。 -/
theorem cost_lt_of_payoff_le_of_lt (hna : M.NoArbitrage) {θ θ' : I → ℝ}
    (h : ∀ ω, M.payoff θ ω ≤ M.payoff θ' ω) (hlt : ∃ ω, M.payoff θ ω < M.payoff θ' ω) :
    M.cost θ < M.cost θ' := by
  by_contra hge
  replace hge := le_of_not_gt hge
  obtain ⟨ω₀, hω₀⟩ := hlt
  refine hna (fun i => θ' i - θ i) ⟨?_, ?_, Or.inr ⟨ω₀, ?_⟩⟩
  · rw [M.cost_sub]; linarith
  · intro ω; rw [M.payoff_sub]; linarith [h ω]
  · rw [M.payoff_sub]; linarith

/-! ## 1 つの資産を 1 単位持つポートフォリオ -/

/-- 資産 `j` を 1 単位だけ持つポートフォリオ。資産が等しいかを判定するために `DecidableEq I` を使う。
以下の定理は、証明の中で `classical` によってこの判定を用意するので、命題には現れない。 -/
def unit [DecidableEq I] (j : I) : I → ℝ := fun i => if i = j then 1 else 0

variable (M) in
/-- 資産 `j` を 1 単位持つ費用は、資産 `j` の価格である。 -/
theorem cost_unit [DecidableEq I] (j : I) : M.cost (unit j) = M.price j := by
  simp [cost, unit]

variable (M) in
/-- 資産 `j` を 1 単位持つ支払いは、資産 `j` の支払いである。 -/
theorem payoff_unit [DecidableEq I] (j : I) (ω : Ω) : M.payoff (unit j) ω = M.pay j ω := by
  simp [payoff, unit]

/-- 価格の上下限：無裁定なら、資産 `j` の支払いが 2 つのポートフォリオの支払いに挟まれるとき、
資産 `j` の価格は 2 つの費用の間にある。`j` は市場で取引されている資産である。 -/
theorem price_between_of_dominated (hna : M.NoArbitrage) {θlo θhi : I → ℝ} {j : I}
    (hlo : ∀ ω, M.payoff θlo ω ≤ M.pay j ω) (hhi : ∀ ω, M.pay j ω ≤ M.payoff θhi ω) :
    M.cost θlo ≤ M.price j ∧ M.price j ≤ M.cost θhi := by
  classical
  constructor
  · rw [← M.cost_unit j]
    exact cost_le_of_payoff_le hna fun ω => by rw [M.payoff_unit]; exact hlo ω
  · rw [← M.cost_unit j]
    exact cost_le_of_payoff_le hna fun ω => by rw [M.payoff_unit]; exact hhi ω

/-! ## プット・コール・パリティとコールの価格 -/

/-- プット・コール・パリティ：債券 `b`（どの状態でも 1 を払う）、株 `s`、行使価格 `K` のコール `c`
とプット `p` が取引される無裁定の市場では、`price c - price p = price s - K * price b`。 -/
theorem put_call_parity (hna : M.NoArbitrage) {b s c p : I} {K : ℝ}
    (hb : ∀ ω, M.pay b ω = 1) (hc : ∀ ω, M.pay c ω = max (M.pay s ω - K) 0)
    (hp : ∀ ω, M.pay p ω = max (K - M.pay s ω) 0) :
    M.price c - M.price p = M.price s - K * M.price b := by
  classical
  have h := law_of_one_price hna (θ := fun i => 1 * unit c i + (-1) * unit p i)
    (θ' := fun i => 1 * unit s i + (-K) * unit b i) fun ω => by
      simp only [M.payoff_combo, M.payoff_unit, hb, hc, hp]
      have := LagrangeAcademy.Ch07.call_sub_put_payoff_real (M.pay s ω) K
      linarith
  simp only [M.cost_combo, M.cost_unit] at h
  linarith

/-- 実数のコールのペイオフは、行使価格について減少する。 -/
theorem call_payoff_antitone {s K₁ K₂ : ℝ} (hK : K₁ ≤ K₂) : max (s - K₂) 0 ≤ max (s - K₁) 0 :=
  max_le_max (by linarith) le_rfl

/-- 実数のコールのペイオフの差は、行使価格の差以下である。 -/
theorem call_payoff_sub_le {s K₁ K₂ : ℝ} (hK : K₁ ≤ K₂) :
    max (s - K₁) 0 ≤ max (s - K₂) 0 + (K₂ - K₁) := by
  rcases le_total s K₂ with h | h
  · rw [max_eq_right (by linarith : s - K₂ ≤ 0)]
    exact max_le (by linarith) (by linarith)
  · rw [max_eq_left (by linarith : 0 ≤ s - K₂)]
    exact max_le (by linarith) (by linarith)

/-- コールの価格は、行使価格について減少する：`K₁ ≤ K₂` なら `price c₂ ≤ price c₁`。 -/
theorem call_price_antitone (hna : M.NoArbitrage) {s c₁ c₂ : I} {K₁ K₂ : ℝ} (hK : K₁ ≤ K₂)
    (hc₁ : ∀ ω, M.pay c₁ ω = max (M.pay s ω - K₁) 0)
    (hc₂ : ∀ ω, M.pay c₂ ω = max (M.pay s ω - K₂) 0) : M.price c₂ ≤ M.price c₁ := by
  classical
  rw [← M.cost_unit c₁, ← M.cost_unit c₂]
  exact cost_le_of_payoff_le hna fun ω => by
    rw [M.payoff_unit, M.payoff_unit, hc₁, hc₂]
    exact call_payoff_antitone hK

/-- コール・スプレッドの価格の上限：`K₁ ≤ K₂` なら `price c₁ ≤ price c₂ + (K₂ - K₁) * price b`。 -/
theorem call_spread_price_le (hna : M.NoArbitrage) {b s c₁ c₂ : I} {K₁ K₂ : ℝ} (hK : K₁ ≤ K₂)
    (hb : ∀ ω, M.pay b ω = 1) (hc₁ : ∀ ω, M.pay c₁ ω = max (M.pay s ω - K₁) 0)
    (hc₂ : ∀ ω, M.pay c₂ ω = max (M.pay s ω - K₂) 0) :
    M.price c₁ ≤ M.price c₂ + (K₂ - K₁) * M.price b := by
  classical
  have h := cost_le_of_payoff_le hna (θ := fun i => 1 * unit c₁ i + 0 * unit b i)
    (θ' := fun i => 1 * unit c₂ i + (K₂ - K₁) * unit b i) fun ω => by
      simp only [M.payoff_combo, M.payoff_unit, hb, hc₁, hc₂]
      have := call_payoff_sub_le (s := M.pay s ω) hK
      linarith
  simp only [M.cost_combo, M.cost_unit] at h
  linarith

/-- 実数のコールのペイオフは、行使価格について凸である（一般の 3 つの行使価格
`K₁ ≤ K₂ ≤ K₃`、分母を払った形）。 -/
theorem call_payoff_convex {s K₁ K₂ K₃ : ℝ} (h₁₂ : K₁ ≤ K₂) (h₂₃ : K₂ ≤ K₃) :
    (K₃ - K₁) * max (s - K₂) 0 ≤ (K₃ - K₂) * max (s - K₁) 0 + (K₂ - K₁) * max (s - K₃) 0 := by
  rcases le_total s K₁ with hs₁ | hs₁
  · rw [max_eq_right (by linarith : s - K₂ ≤ 0), max_eq_right (by linarith : s - K₁ ≤ 0),
      max_eq_right (by linarith : s - K₃ ≤ 0)]
    linarith
  rcases le_total s K₂ with hs₂ | hs₂
  · rw [max_eq_right (by linarith : s - K₂ ≤ 0), max_eq_left (by linarith : 0 ≤ s - K₁),
      max_eq_right (by linarith : s - K₃ ≤ 0)]
    nlinarith
  rcases le_total s K₃ with hs₃ | hs₃
  · rw [max_eq_left (by linarith : 0 ≤ s - K₂), max_eq_left (by linarith : 0 ≤ s - K₁),
      max_eq_right (by linarith : s - K₃ ≤ 0)]
    nlinarith
  · rw [max_eq_left (by linarith : 0 ≤ s - K₂), max_eq_left (by linarith : 0 ≤ s - K₁),
      max_eq_left (by linarith : 0 ≤ s - K₃)]
    nlinarith

/-- コールの価格は、行使価格について凸である：`K₁ ≤ K₂ ≤ K₃` なら
`(K₃ - K₁) * price c₂ ≤ (K₃ - K₂) * price c₁ + (K₂ - K₁) * price c₃`。行使価格は等間隔でなくてよい。
`K₁ < K₃` のとき両辺を `K₃ - K₁` で割ると、`λ = (K₃ - K₂) / (K₃ - K₁)` での凸性になる。 -/
theorem call_price_convex (hna : M.NoArbitrage) {s c₁ c₂ c₃ : I} {K₁ K₂ K₃ : ℝ}
    (h₁₂ : K₁ ≤ K₂) (h₂₃ : K₂ ≤ K₃)
    (hc₁ : ∀ ω, M.pay c₁ ω = max (M.pay s ω - K₁) 0)
    (hc₂ : ∀ ω, M.pay c₂ ω = max (M.pay s ω - K₂) 0)
    (hc₃ : ∀ ω, M.pay c₃ ω = max (M.pay s ω - K₃) 0) :
    (K₃ - K₁) * M.price c₂ ≤ (K₃ - K₂) * M.price c₁ + (K₂ - K₁) * M.price c₃ := by
  classical
  have h := cost_le_of_payoff_le hna (θ := fun i => (K₃ - K₁) * unit c₂ i + 0 * unit c₁ i)
    (θ' := fun i => (K₃ - K₂) * unit c₁ i + (K₂ - K₁) * unit c₃ i) fun ω => by
      simp only [M.payoff_combo, M.payoff_unit, hc₁, hc₂, hc₃]
      have := call_payoff_convex (s := M.pay s ω) h₁₂ h₂₃
      linarith
  simp only [M.cost_combo, M.cost_unit] at h
  linarith

/-! ## 状態価格 -/

variable (M) in
/-- 状態価格による費用の表し方：すべての資産の価格が `price i = ∑ ω, ψ ω * pay i ω` と書けるなら、
どのポートフォリオの費用も `∑ ω, ψ ω * payoff θ ω` である。 -/
theorem cost_eq_statePrice {ψ : Ω → ℝ} (hp : ∀ i, M.price i = ∑ ω, ψ ω * M.pay i ω)
    (θ : I → ℝ) : M.cost θ = ∑ ω, ψ ω * M.payoff θ ω := by
  unfold cost payoff
  simp_rw [hp, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun i _ => by ring

/-- 状態価格からの無裁定（資産価格の基本定理の易しい向き）：各状態に正の重み `ψ ω` があり、
すべての資産の価格が `∑ ω, ψ ω * pay i ω` と書けるなら、市場は無裁定である。重みの和を 1 に
正規化することや、ニューメレールは使わない。 -/
theorem noArbitrage_of_statePrice {ψ : Ω → ℝ} (hψ : ∀ ω, 0 < ψ ω)
    (hp : ∀ i, M.price i = ∑ ω, ψ ω * M.pay i ω) : M.NoArbitrage := by
  intro θ ⟨hc, hnn, hpos⟩
  rw [cost_eq_statePrice M hp] at hc hpos
  have hge : 0 ≤ ∑ ω, ψ ω * M.payoff θ ω :=
    Finset.sum_nonneg fun ω _ => mul_nonneg (hψ ω).le (hnn ω)
  rcases hpos with hneg | ⟨ω₀, hω₀⟩
  · linarith
  · have : 0 < ∑ ω, ψ ω * M.payoff θ ω :=
      Finset.sum_pos' (fun ω _ => mul_nonneg (hψ ω).le (hnn ω))
        ⟨ω₀, Finset.mem_univ _, mul_pos (hψ ω₀) hω₀⟩
    linarith

end FiniteMarket

/-! ## 2 状態の完備な市場 -/

open FiniteMarket

/-- 2 状態（`true` が上がる状態、`false` が下がる状態）で、資産が債券（`false`）と株（`true`）の
市場。債券がどの状態でも 1 を払い、株の 2 つの状態の支払いが異なれば、市場は完備である。 -/
theorem twoState_complete (M : FiniteMarket Bool Bool) (hb : ∀ ω, M.pay false ω = 1)
    (hs : M.pay true true ≠ M.pay true false) : M.IsComplete := by
  intro C
  have hd : M.pay true true - M.pay true false ≠ 0 := sub_ne_zero.mpr hs
  -- 株を Δ 単位、債券を C(下) - Δ * 株(下) 単位持つ
  set Δ := (C true - C false) / (M.pay true true - M.pay true false) with hΔ
  refine ⟨fun i => if i then Δ else C false - Δ * M.pay true false, ?_⟩
  intro ω
  simp only [payoff, Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false, hb]
  cases ω
  · ring
  · rw [hΔ]
    field_simp
    ring

/-- 2 状態の市場の合成の値の例：債券の価格 `19/20`、株の価格 `100`、株の支払いは上がれば `120`、
下がれば `90`。 -/
noncomputable def twoState : FiniteMarket Bool Bool where
  price i := if i then 100 else 19 / 20
  pay i ω := if i then (if ω then 120 else 90) else 1

/-- 例の市場は無裁定である。状態価格 `ψ(上) = 29/60`、`ψ(下) = 7/15` で価格が表せる。 -/
theorem twoState_noArbitrage : twoState.NoArbitrage := by
  refine noArbitrage_of_statePrice (ψ := fun ω => if ω then 29 / 60 else 7 / 15) ?_ ?_
  · intro ω; cases ω <;> norm_num
  · intro i; cases i <;> simp [twoState] <;> norm_num

/-- 例の市場は完備である。 -/
theorem twoState_isComplete : twoState.IsComplete :=
  twoState_complete twoState (fun ω => by simp [twoState]) (by simp [twoState])

/-! ## 3 状態の不完備な市場 -/

/-- 3 状態の市場の合成の値の例：債券の価格 `19/20`、株の価格 `100`、株の支払いは 3 つの状態で
`120`、`100`、`90`。 -/
noncomputable def threeState : FiniteMarket Bool (Fin 3) where
  price i := if i then 100 else 19 / 20
  pay i ω := if i then ![120, 100, 90] ω else 1

/-- 例の市場は無裁定である。状態価格 `2/5`、`1/4`、`3/10` で価格が表せる。 -/
theorem threeState_noArbitrage : threeState.NoArbitrage := by
  refine noArbitrage_of_statePrice (ψ := ![2 / 5, 1 / 4, 3 / 10]) ?_ ?_
  · intro ω; fin_cases ω <;> norm_num
  · intro i; cases i <;> simp [threeState, Fin.sum_univ_three] <;> norm_num

/-- 例の市場は完備でない：中央の状態だけで 1 を払う支払いは、債券と株では複製できない。 -/
theorem threeState_not_complete : ¬ threeState.IsComplete := by
  intro h
  obtain ⟨θ, hθ⟩ := h ![0, 1, 0]
  have h0 := hθ 0
  have h1 := hθ 1
  have h2 := hθ 2
  simp [threeState, payoff] at h0 h1 h2
  linarith

/-! ## 複製できない支払いの価格は 1 つに決まらない -/

/-- 3 状態の市場に、中央の状態（状態 1）だけで 1 を払う請求権を、価格 `p` の資産として加えた
拡大市場。資産 `0` が債券、`1` が株、`2` が加えた請求権。 -/
noncomputable def threeStateExt (p : ℝ) : FiniteMarket (Fin 3) (Fin 3) where
  price := ![19 / 20, 100, p]
  pay := ![fun _ => 1, ![120, 100, 90], ![0, 1, 0]]

/-- 請求権の価格を `1/4` とした拡大市場は無裁定である。状態価格 `(2/5, 1/4, 3/10)`
（`ψ(t) = (2/5 + 10t, 1/4 - 30t, 3/10 + 20t)` の `t = 0`）で、3 つの資産の価格が表せる。 -/
theorem threeStateExt_noArbitrage_quarter : (threeStateExt (1 / 4)).NoArbitrage := by
  refine noArbitrage_of_statePrice (ψ := ![2 / 5, 1 / 4, 3 / 10]) ?_ ?_
  · intro ω; fin_cases ω <;> norm_num
  · intro i; fin_cases i <;> simp [threeStateExt, Fin.sum_univ_three] <;> norm_num

/-- 請求権の価格を `11/50` とした拡大市場も無裁定である。状態価格 `(41/100, 11/50, 8/25)`
（`ψ(t)` の `t = 1/1000`）で、3 つの資産の価格が表せる。同じ請求権に、無裁定と両立する
2 つの異なる価格がある。 -/
theorem threeStateExt_noArbitrage_alt : (threeStateExt (11 / 50)).NoArbitrage := by
  refine noArbitrage_of_statePrice (ψ := ![41 / 100, 11 / 50, 8 / 25]) ?_ ?_
  · intro ω; fin_cases ω <;> norm_num
  · intro i; fin_cases i <;> simp [threeStateExt, Fin.sum_univ_three] <;> norm_num

end LagrangeAcademy.Ch10

end
