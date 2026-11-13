module

public import LagrangeAcademy.PartII.Ch11Numeraire
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# 第12章 有限市場の資産価格の基本定理

第10章の 1 期間の有限市場で、無裁定と正の状態価格の存在が同値であることを示す。第10章で示した
易しい向き（`noArbitrage_of_statePrice`）に、逆向き（`exists_statePrice_of_noArbitrage`）を加える。

- 利得ベクトル：ポートフォリオ `θ` に、`(-cost θ, payoff θ ω)` を対応させる（`gainVector`）。
  座標の添字は `Option Ω` で、`none` が `-cost` の座標、`some ω` が状態 `ω` の支払いの座標。
  その像は線形部分空間である（`gainSubspace`）。
- 無裁定 ⟺ 利得部分空間と標準単体が交わらない（`noArbitrage_iff_disjoint`）。
- 逆向き：Mathlib の強い分離定理 `geometric_hahn_banach_compact_closed` で、単体と利得部分空間を
  分離する線形汎関数を得る。それは部分空間の上で 0、単体の上で負なので、符号を変えるとすべての
  座標が正の線形汎関数になり、その比が正の状態価格になる。
- 資産価格の基本定理（`noArbitrage_iff_exists_statePrice`）と、第11章のニューメレールの形
  （`noArbitrage_iff_exists_numeraireProb`）。
- 完備性と状態価格の一意性：完備なら状態価格は 1 つ（`statePrice_unique_of_complete`）。
  無裁定で正の状態価格が 1 つなら完備（`complete_of_statePrice_unique`）。
- 第10章の 3 状態の拡大市場：請求権の価格 `π` について、`π ≤ 0` と `π ≥ 7/10` では裁定を直接
  構成し、`0 < π < 7/10` では正の状態価格を構成する（`threeStateExt_noArbitrage_iff`）。
-/

@[expose] public section

namespace LagrangeAcademy.Ch12

open LagrangeAcademy.Ch10 LagrangeAcademy.Ch10.FiniteMarket
open LagrangeAcademy.Ch11 LagrangeAcademy.Ch08

variable {I Ω : Type*} [Fintype I] [Fintype Ω]

/-! ## 利得ベクトルと利得部分空間 -/

/-- ポートフォリオ `θ` の利得ベクトル：座標 `none` が `-cost θ`、座標 `some ω` が状態 `ω` の支払い。 -/
def gainVector (M : FiniteMarket I Ω) (θ : I → ℝ) : Option Ω → ℝ
  | none => -M.cost θ
  | some ω => M.payoff θ ω

/-- 利得ベクトルは、ポートフォリオについて線形である。 -/
def gainMap (M : FiniteMarket I Ω) : (I → ℝ) →ₗ[ℝ] (Option Ω → ℝ) where
  toFun := gainVector M
  map_add' θ θ' := by
    funext o
    cases o
    · simp only [gainVector, cost, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      ring
    · simp only [gainVector, payoff, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c θ := by
    funext o
    cases o
    · simp only [gainVector, cost, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc,
        ← Finset.mul_sum]
      ring
    · simp only [gainVector, payoff, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc,
        ← Finset.mul_sum]

/-- 利得部分空間：すべてのポートフォリオの利得ベクトルの集まり。 -/
def gainSubspace (M : FiniteMarket I Ω) : Submodule ℝ (Option Ω → ℝ) :=
  LinearMap.range (gainMap M)

/-- 非負単体：座標がすべて非負で、和が 1 のベクトルの集まり。Mathlib の `stdSimplex` は
Lean 4.35.0 の Mathlib で非推奨になったので、同じ集合をここで定義する。 -/
def simplex (Ω : Type*) [Fintype Ω] : Set (Option Ω → ℝ) :=
  {x | (∀ k, 0 ≤ x k) ∧ ∑ k, x k = 1}

/-- 非負単体は凸である。 -/
theorem convex_simplex : Convex ℝ (simplex Ω) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun k => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 k)) (mul_nonneg hb (hy.1 k))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx.2, hy.2, mul_one, hab]

/-- 非負単体は閉集合である（座標の非負と、和が 1 という、連続な条件の共通部分）。 -/
theorem isClosed_simplex : IsClosed (simplex Ω) := by
  have h1 : IsClosed {x : Option Ω → ℝ | ∀ k, 0 ≤ x k} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun k => isClosed_le continuous_const (continuous_apply k)
  have h2 : IsClosed {x : Option Ω → ℝ | ∑ k, x k = 1} :=
    isClosed_eq (continuous_finsetSum _ fun k _ => continuous_apply k) continuous_const
  exact h1.inter h2

/-- 非負単体はコンパクトである（閉集合で、箱 `[0, 1]` に入る）。 -/
theorem isCompact_simplex : IsCompact (simplex Ω) := by
  refine IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : Option Ω → ℝ)) (b := 1))
    isClosed_simplex fun x hx => ⟨fun k => hx.1 k, fun k => ?_⟩
  change x k ≤ 1
  rw [← hx.2]
  exact Finset.single_le_sum (f := x) (fun j _ => hx.1 j) (Finset.mem_univ k)

/-! ## 無裁定と、単体との交わり -/

/-- 無裁定 ⟺ 利得部分空間と標準単体が交わらない。 -/
theorem noArbitrage_iff_disjoint (M : FiniteMarket I Ω) :
    M.NoArbitrage ↔ Disjoint (simplex Ω) (gainSubspace M : Set (Option Ω → ℝ)) := by
  rw [Set.disjoint_left]
  constructor
  · rintro hna x ⟨hx0, hx1⟩ ⟨θ, rfl⟩
    apply hna θ
    have hc : 0 ≤ -M.cost θ := hx0 none
    have hω : ∀ ω, 0 ≤ M.payoff θ ω := fun ω => hx0 (some ω)
    refine ⟨by linarith, hω, ?_⟩
    by_contra h
    simp only [not_or, not_lt, not_exists] at h
    obtain ⟨h1, h2⟩ := h
    rw [Fintype.sum_option] at hx1
    have : ∑ ω, gainMap M θ (some ω) = 0 :=
      Finset.sum_eq_zero fun ω _ => le_antisymm (h2 ω) (hω ω)
    have hn : gainMap M θ none = 0 := by
      change -M.cost θ = 0
      linarith
    rw [this, hn] at hx1
    norm_num at hx1
  · intro hdisj θ ⟨h1, h2, h3⟩
    set s := ∑ o, gainVector M θ o with hs
    have hnn : ∀ o, 0 ≤ gainVector M θ o := by
      intro o; cases o
      · change 0 ≤ -M.cost θ; linarith
      · exact h2 _
    have hpos : 0 < s := by
      rcases h3 with h | ⟨ω, h⟩
      · exact lt_of_lt_of_le (by change 0 < -M.cost θ; linarith)
          (Finset.single_le_sum (fun o _ => hnn o) (Finset.mem_univ none))
      · exact lt_of_lt_of_le h
          (Finset.single_le_sum (f := gainVector M θ) (fun o _ => hnn o)
            (Finset.mem_univ (some ω)))
    apply hdisj (a := s⁻¹ • gainVector M θ)
    · refine ⟨fun o => mul_nonneg (inv_nonneg.mpr hpos.le) (hnn o), ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, ← hs]
      exact inv_mul_cancel₀ (ne_of_gt hpos)
    · exact Submodule.smul_mem _ _ ⟨θ, rfl⟩

/-! ## 逆向き：無裁定なら正の状態価格がある -/

/-- 座標 `k` だけが 1 の単位ベクトル（`LinearMap.pi_apply_eq_sum_univ` の形に合わせる）。 -/
def basisVec [DecidableEq Ω] (k : Option Ω) : Option Ω → ℝ := fun j => if k = j then 1 else 0

theorem basisVec_mem_simplex [DecidableEq Ω] (k : Option Ω) :
    basisVec k ∈ simplex Ω := by
  refine ⟨fun j => ?_, ?_⟩
  · unfold basisVec; split_ifs <;> norm_num
  · simp [basisVec]

/-- **資産価格の基本定理の逆向き**：無裁定なら、正の状態価格 `ψ` が存在し、すべての資産の価格が
`price i = ∑ ω, ψ ω * pay i ω` と表せる。 -/
theorem exists_statePrice_of_noArbitrage (M : FiniteMarket I Ω) (hna : M.NoArbitrage) :
    ∃ ψ : Ω → ℝ, (∀ ω, 0 < ψ ω) ∧ ∀ i, M.price i = ∑ ω, ψ ω * M.pay i ω := by
  classical
  -- 1. 単体と利得部分空間を強く分離する
  obtain ⟨f, u, v, hfu, huv, hfv⟩ :=
    geometric_hahn_banach_compact_closed convex_simplex isCompact_simplex
      (Submodule.convex (gainSubspace M)) (Submodule.closed_of_finiteDimensional (gainSubspace M))
      ((noArbitrage_iff_disjoint M).mp hna)
  -- 2. f は部分空間の上で 0
  have hzero : ∀ b ∈ gainSubspace M, f b = 0 := by
    intro b hb
    by_contra hne
    have h := hfv (((v - 1) / f b) • b) (Submodule.smul_mem _ _ hb)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at h
    linarith
  have hv : v < 0 := by
    have h := hfv 0 (Submodule.zero_mem _)
    rwa [map_zero] at h
  -- 3. f は単体の各頂点で負
  have hneg : ∀ k, f (basisVec k) < 0 := fun k =>
    (hfu _ (basisVec_mem_simplex k)).trans (huv.trans hv)
  -- 4. 正の状態価格
  refine ⟨fun ω => (-f (basisVec (some ω))) / (-f (basisVec none)),
    fun ω => div_pos (neg_pos.mpr (hneg _)) (neg_pos.mpr (hneg _)), fun i => ?_⟩
  have hb : gainMap M (unit i) ∈ gainSubspace M := ⟨unit i, rfl⟩
  have h0 := hzero _ hb
  have hexp := LinearMap.pi_apply_eq_sum_univ (f : (Option Ω → ℝ) →ₗ[ℝ] ℝ) (gainMap M (unit i))
  rw [ContinuousLinearMap.coe_coe, h0, Fintype.sum_option] at hexp
  have hnone : gainMap M (unit i) none = -M.price i := by
    change -M.cost (unit i) = -M.price i
    rw [M.cost_unit]
  have hsome : ∀ ω, gainMap M (unit i) (some ω) = M.pay i ω := by
    intro ω
    change M.payoff (unit i) ω = M.pay i ω
    exact M.payoff_unit i ω
  simp only [hnone, hsome, smul_eq_mul] at hexp
  have hF0 := ne_of_lt (hneg none)
  have hsum : ∑ ω, M.pay i ω * f (basisVec (some ω)) = M.price i * f (basisVec none) := by
    change ∑ ω, M.pay i ω * f (fun j => if some ω = j then 1 else 0)
      = M.price i * f (fun j => if none = j then 1 else 0)
    linarith
  simp_rw [neg_div_neg_eq]
  calc M.price i = M.price i * f (basisVec none) / f (basisVec none) := by field_simp
    _ = (∑ ω, M.pay i ω * f (basisVec (some ω))) / f (basisVec none) := by rw [hsum]
    _ = ∑ ω, f (basisVec (some ω)) / f (basisVec none) * M.pay i ω := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun ω _ => by ring

/-! ## 資産価格の基本定理 -/

/-- **資産価格の基本定理**（有限・1 期間）：無裁定 ⟺ 正の状態価格が存在する。 -/
theorem noArbitrage_iff_exists_statePrice (M : FiniteMarket I Ω) :
    M.NoArbitrage ↔ ∃ ψ : Ω → ℝ, (∀ ω, 0 < ψ ω) ∧ ∀ i, M.price i = ∑ ω, ψ ω * M.pay i ω :=
  ⟨exists_statePrice_of_noArbitrage M, fun ⟨_, hψ, hp⟩ => noArbitrage_of_statePrice hψ hp⟩

/-- ニューメレールの形（第11章）：ニューメレール `N` を 1 つ固定すると、無裁定 ⟺ ニューメレールで
測った価格が期待値になる、どの状態でも正の確率 `Q` が存在する。 -/
theorem noArbitrage_iff_exists_numeraireProb (M : FiniteMarket I Ω) (N : Numeraire M) :
    M.NoArbitrage ↔ ∃ Q : FinProb Ω, (∀ ω, 0 < Q.prob ω) ∧
      ∀ i, M.price i / M.price N.n = Q.expect (fun ω => M.pay i ω / M.pay N.n ω) := by
  constructor
  · intro hna
    obtain ⟨ψ, hψ, hp⟩ := exists_statePrice_of_noArbitrage M hna
    exact ⟨numeraireProb N hψ hp, numeraireProb_pos N hψ hp, price_div_eq_expect N hψ hp⟩
  · rintro ⟨Q, hQ, h⟩
    exact noArbitrage_of_numeraireProb N Q hQ h

/-! ## 完備性と状態価格の一意性 -/

/-- 完備なら、価格を表す状態価格は 1 つに決まる。状態 `ω₀` だけで 1 を払う支払いを複製する
ポートフォリオの費用が、どの状態価格でも `ψ ω₀` になるからである。正であることも無裁定も使わない。 -/
theorem statePrice_unique_of_complete (M : FiniteMarket I Ω) (hc : M.IsComplete) {ψ ψ' : Ω → ℝ}
    (hp : ∀ i, M.price i = ∑ ω, ψ ω * M.pay i ω) (hp' : ∀ i, M.price i = ∑ ω, ψ' ω * M.pay i ω) :
    ψ = ψ' := by
  classical
  funext ω₀
  obtain ⟨θ, hθ⟩ := hc (fun ω => if ω = ω₀ then 1 else 0)
  have hθ' : ∀ ω, M.payoff θ ω = if ω = ω₀ then 1 else 0 := hθ
  have h := cost_eq_statePrice M hp θ
  have h' := cost_eq_statePrice M hp' θ
  simp only [hθ', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    at h h'
  rw [← h, ← h']

/-- 支払いの線形写像（像が複製できる支払いの集まり）。 -/
def payoffMap (M : FiniteMarket I Ω) : (I → ℝ) →ₗ[ℝ] (Ω → ℝ) where
  toFun θ := M.payoff θ
  map_add' θ θ' := by
    funext ω
    simp only [payoff, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c θ := by
    funext ω
    simp only [payoff, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum]

/-- 無裁定で、正の状態価格が 1 つしかないなら、市場は完備である。完備でなければ、複製できる
支払いの部分空間に直交する 0 でない `η` があり、正の状態価格 `ψ` を `ψ + ε η`（`ε` は小さい正の数）
にずらしても、正の状態価格のままである。 -/
theorem complete_of_statePrice_unique (M : FiniteMarket I Ω) (hna : M.NoArbitrage)
    (huniq : ∀ ψ ψ' : Ω → ℝ, (∀ ω, 0 < ψ ω) → (∀ i, M.price i = ∑ ω, ψ ω * M.pay i ω) →
      (∀ ω, 0 < ψ' ω) → (∀ i, M.price i = ∑ ω, ψ' ω * M.pay i ω) → ψ = ψ') :
    M.IsComplete := by
  classical
  by_contra hnc
  -- 1. 複製できる支払いの部分空間は全体ではない
  have hlt : LinearMap.range (payoffMap M) < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hnc fun C => ?_
    have hC : C ∈ LinearMap.range (payoffMap M) := by rw [htop]; trivial
    obtain ⟨θ, hθ⟩ := hC
    exact ⟨θ, fun ω => congrFun hθ ω⟩
  -- 2. その部分空間の上で 0 になる、0 でない線形汎関数 g
  obtain ⟨g, hg0, hle⟩ := (LinearMap.range (payoffMap M)).exists_le_ker_of_lt_top hlt
  set η : Ω → ℝ := fun ω => g (fun j => if ω = j then 1 else 0) with hη
  have hgexp : ∀ x, g x = ∑ ω, x ω * η ω := fun x => by
    rw [LinearMap.pi_apply_eq_sum_univ g x]
    rfl
  -- η は各資産の支払いに直交する
  have hηpay : ∀ i, ∑ ω, M.pay i ω * η ω = 0 := by
    intro i
    have hmem : M.pay i ∈ LinearMap.range (payoffMap M) :=
      ⟨unit i, funext fun ω => M.payoff_unit i ω⟩
    have := hle hmem
    rw [LinearMap.mem_ker, hgexp] at this
    exact this
  -- η は 0 でない
  obtain ⟨ω₁, hω₁⟩ : ∃ ω, η ω ≠ 0 := by
    by_contra h
    simp only [ne_eq, not_exists, not_not] at h
    apply hg0
    refine LinearMap.ext fun x => ?_
    rw [hgexp]
    simp [h]
  -- 3. 正の状態価格 ψ と、ずらした ψ'
  obtain ⟨ψ, hψ, hp⟩ := exists_statePrice_of_noArbitrage M hna
  set S := ∑ ω, |η ω| / ψ ω with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun ω _ => div_nonneg (abs_nonneg _) (hψ ω).le
  set ε := 1 / (1 + S) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hψ' : ∀ ω, 0 < ψ ω + ε * η ω := by
    intro ω
    have hle1 : |η ω| / ψ ω ≤ S :=
      Finset.single_le_sum (f := fun ω => |η ω| / ψ ω)
        (fun ω _ => div_nonneg (abs_nonneg _) (hψ ω).le) (Finset.mem_univ ω)
    have hlt1 : |η ω| < ψ ω * (1 + S) := by
      have := (div_le_iff₀ (hψ ω)).mp hle1
      nlinarith [hψ ω]
    have hlt2 : ε * |η ω| < ψ ω := by
      rw [hε, one_div, inv_mul_lt_iff₀ (by positivity)]
      linarith
    have := neg_abs_le (η ω)
    nlinarith [hεpos]
  have hp' : ∀ i, M.price i = ∑ ω, (ψ ω + ε * η ω) * M.pay i ω := by
    intro i
    have h1 : ∑ ω, (ψ ω + ε * η ω) * M.pay i ω
        = ∑ ω, ψ ω * M.pay i ω + ε * ∑ ω, M.pay i ω * η ω := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun ω _ => by ring
    rw [h1, hηpay i, mul_zero, add_zero, hp i]
  -- 4. 一意性に反する
  have heq := huniq ψ (fun ω => ψ ω + ε * η ω) hψ hp hψ' hp'
  have := congrFun heq ω₁
  have : ε * η ω₁ = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (ne_of_gt hεpos)
  · exact hω₁ h

/-! ## 第10章の 3 状態の拡大市場 -/

/-- `π ≤ 0` なら、請求権を 1 単位買うポートフォリオが裁定になる（費用 `π`、支払い `(0, 1, 0)`）。 -/
theorem threeStateExt_isArbitrage_buy {p : ℝ} (hp : p ≤ 0) :
    (threeStateExt p).IsArbitrage ![0, 0, 1] := by
  refine ⟨?_, ?_, Or.inr ⟨1, ?_⟩⟩
  · simpa [threeStateExt, cost, Fin.sum_univ_three] using hp
  · intro ω; fin_cases ω <;> simp [threeStateExt, payoff, Fin.sum_univ_three]
  · simp [threeStateExt, payoff, Fin.sum_univ_three]

/-- `π ≥ 7/10` なら、債券 6 単位、株 `-1/20` 単位、請求権 `-1` 単位のポートフォリオが裁定になる
（費用 `7/10 - π`、支払い `(0, 0, 3/2)`）。 -/
theorem threeStateExt_isArbitrage_sell {p : ℝ} (hp : 7 / 10 ≤ p) :
    (threeStateExt p).IsArbitrage ![6, -1 / 20, -1] := by
  refine ⟨?_, ?_, Or.inr ⟨2, ?_⟩⟩
  · simp [threeStateExt, cost, Fin.sum_univ_three]; linarith
  · intro ω; fin_cases ω <;> simp [threeStateExt, payoff, Fin.sum_univ_three] <;> norm_num
  · simp [threeStateExt, payoff, Fin.sum_univ_three]; norm_num

/-- 拡大市場が無裁定 ⟺ `0 < π < 7/10`。`0 < π < 7/10` では、正の状態価格
`(2/5 + (1/4 - π)/3, π, 3/10 + 2(1/4 - π)/3)` を構成する（第10章の `ψ(t)` で `t = (1/4 - π)/30`）。 -/
theorem threeStateExt_noArbitrage_iff (p : ℝ) :
    (threeStateExt p).NoArbitrage ↔ 0 < p ∧ p < 7 / 10 := by
  constructor
  · intro h
    constructor
    · by_contra hp
      exact h _ (threeStateExt_isArbitrage_buy (not_lt.mp hp))
    · by_contra hp
      exact h _ (threeStateExt_isArbitrage_sell (not_lt.mp hp))
  · rintro ⟨h0, h1⟩
    refine noArbitrage_of_statePrice
      (ψ := ![2 / 5 + (1 / 4 - p) / 3, p, 3 / 10 + 2 * (1 / 4 - p) / 3]) ?_ ?_
    · intro ω; fin_cases ω <;> simp <;> linarith
    · intro i; fin_cases i <;> simp [threeStateExt, Fin.sum_univ_three] <;> ring

end LagrangeAcademy.Ch12

end
