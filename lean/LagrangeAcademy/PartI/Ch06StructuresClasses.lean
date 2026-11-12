module

public import LagrangeAcademy.PartI.Ch05TheoremProving
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# 第6章 構造体・型クラス・数学的仮定

この章から Mathlib を使う。数学的な対象と仮定を、Lean の型でどう表すのか。

- 構造体：値と、その値が満たす性質（証明）を 1 つにまとめた型（`PosNat`）。
- 型クラスとインスタンス：第5章の `decide` が探した `Decidable` は型クラスである。
  `IsEven` に `Decidable` のインスタンスを与えると、`decide` が使えるようになる
  （`isEven_ten`、`not_isEven_seven`）。
- 自分で型クラスを定義し、公理を満たす型すべてについて 1 度だけ定理を証明する
  （`AddZeroClass'`、`zero_add_add_zero`）。
- Mathlib の代数の階層：可換環の定理を 1 度証明し、`ℤ` と `ℚ` に使う（`add_sq_ring`）。
- 金融数学への接続：1 期間の二項モデルの仮定 `d < 1 + r < u` を構造体の項に置き、
  リスク中立確率が `0` と `1` の間にあることを、順序体すべてについて示す
  （`OnePeriodBinomial`、`OnePeriodBinomial.q_pos`、`OnePeriodBinomial.q_lt_one`）。

Lean が受け付けない例は `scripts/ch06_checks.lean` に置く。
-/

@[expose] public section

namespace LagrangeAcademy.Ch06

open LagrangeAcademy.Ch05

/-! ## 構造体：値と性質をまとめる -/

/-- 正の自然数。値 `val` と、それが正であることの証明 `pos` を項に持つ。 -/
structure PosNat where
  val : Nat
  pos : 0 < val

/-- 正の自然数どうしの和。和が正であることの証明も、項として作る。 -/
def PosNat.add (a b : PosNat) : PosNat :=
  ⟨a.val + b.val, Nat.add_pos_left a.pos b.val⟩

/-- 和の値は、値の和である。 -/
theorem PosNat.add_val (a b : PosNat) : (a.add b).val = a.val + b.val := rfl

/-! ## 型クラス `Decidable` とインスタンス -/

/-- `IsEven n`（第5章、`∃ k, n = 2 * k`）は、`n % 2 = 0` と同値である。 -/
theorem isEven_iff_mod (n : Nat) : IsEven n ↔ n % 2 = 0 := by
  constructor
  · rintro ⟨k, rfl⟩
    omega
  · intro h
    exact ⟨n / 2, by omega⟩

/-- `IsEven` の `Decidable` のインスタンス。`n % 2 = 0` の判定（既存のインスタンス）を、
同値 `isEven_iff_mod` で移して作る。 -/
instance isEven_decidable (n : Nat) : Decidable (IsEven n) :=
  decidable_of_iff _ (isEven_iff_mod n).symm

/-- インスタンスがあるので、`decide` が使える。 -/
theorem isEven_ten : IsEven 10 := by decide

/-- 否定も `decide` で示せる。 -/
theorem not_isEven_seven : ¬ IsEven 7 := by decide

/-! ## 型クラスを定義する -/

/-- 足し算と零を持ち、零が左右の単位元になる型。Mathlib の `AddZeroClass` を簡単にしたもの。
項 `zero_add`、`add_zero` は、演算が満たすべき公理を証明として要求する。 -/
class AddZeroClass' (α : Type) where
  zero : α
  add : α → α → α
  zero_add : ∀ a, add zero a = a
  add_zero : ∀ a, add a zero = a

/-- 自然数のインスタンス。公理は、Lean 本体の定理で証明する。 -/
instance addZeroClassNat : AddZeroClass' Nat where
  zero := 0
  add := (· + ·)
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero

/-- 真理値の「または」のインスタンス。零は `false`。 -/
instance addZeroClassBool : AddZeroClass' Bool where
  zero := false
  add := (· || ·)
  zero_add := Bool.false_or
  add_zero := Bool.or_false

/-- `AddZeroClass'` のインスタンスを持つ型すべてについて、1 度だけ証明する。 -/
theorem zero_add_add_zero {α : Type} [AddZeroClass' α] (a : α) :
    AddZeroClass'.add (AddZeroClass'.add AddZeroClass'.zero a) AddZeroClass'.zero = a := by
  rw [AddZeroClass'.add_zero, AddZeroClass'.zero_add]

/-- 同じ定理を、自然数に使う。 -/
theorem zero_add_add_zero_nat (n : Nat) : AddZeroClass'.add (AddZeroClass'.add 0 n) 0 = n :=
  zero_add_add_zero n

/-! ## Mathlib の代数の階層 -/

/-- 可換環の上の展開公式。`[CommRing R]` は、`R` が可換環であるという仮定である。 -/
theorem add_sq_ring {R : Type*} [CommRing R] (a b : R) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

/-- 整数に使う。`ℤ` の `CommRing` のインスタンスは Mathlib にある。 -/
theorem add_sq_ring_int : ((3 : ℤ) + 4) ^ 2 = 3 ^ 2 + 2 * 3 * 4 + 4 ^ 2 := add_sq_ring 3 4

/-- 有理数に使う。 -/
theorem add_sq_ring_rat (a b : ℚ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := add_sq_ring a b

/-! ## 金融数学への接続：1 期間の二項モデルの仮定 -/

/-- 1 期間の二項モデル。安全資産の 1 期間の利子率 `r`、危険資産の価格が上がる場合の倍率 `u`、
下がる場合の倍率 `d` と、それらが満たす仮定 `0 < d < 1 + r < u` を項に持つ。係数の型 `K` は、
任意の順序体である。 -/
structure OnePeriodBinomial (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] where
  r : K
  u : K
  d : K
  d_pos : 0 < d
  d_lt : d < 1 + r
  lt_u : 1 + r < u

namespace OnePeriodBinomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- リスク中立確率 `q = (1 + r - d) / (u - d)`。 -/
def q (m : OnePeriodBinomial K) : K := (1 + m.r - m.d) / (m.u - m.d)

/-- `d < u`。構造体の項の 2 つの仮定から出る。 -/
theorem d_lt_u (m : OnePeriodBinomial K) : m.d < m.u :=
  lt_trans m.d_lt m.lt_u

/-- リスク中立確率は正である。 -/
theorem q_pos (m : OnePeriodBinomial K) : 0 < m.q := by
  unfold q
  apply div_pos
  · linarith [m.d_lt]
  · linarith [m.d_lt_u]

/-- リスク中立確率は 1 より小さい。 -/
theorem q_lt_one (m : OnePeriodBinomial K) : m.q < 1 := by
  unfold q
  rw [div_lt_one (by linarith [m.d_lt_u])]
  linarith [m.lt_u]

end OnePeriodBinomial

/-- 合成の値の例（`ℚ`）：`r = 1/100`、`u = 11/10`、`d = 9/10`。仮定は `norm_num` で示す。 -/
def exampleModel : OnePeriodBinomial ℚ where
  r := 1 / 100
  u := 11 / 10
  d := 9 / 10
  d_pos := by norm_num
  d_lt := by norm_num
  lt_u := by norm_num

/-- 例のリスク中立確率は `11/20` である。 -/
theorem exampleModel_q : exampleModel.q = 11 / 20 := by
  norm_num [exampleModel, OnePeriodBinomial.q]

end LagrangeAcademy.Ch06

end
