module


/-!
# 第5章 Lean 4による定理証明

Lean 本体だけを使う（Mathlib は使わない）。数学者の証明を、Lean ではどのように組み立てるのか。

- タクティクは、ゴール（まだ証明していない命題）を変えていく命令である。出来上がるのは、
  第2章で見た証明項と同じ種類の項である（`and_swap_tac` と第2章の `and_swap`）。
- 論理の結合子ごとに、ゴールを分解するタクティクと、仮定を使うタクティクがある
  （`intro`・`exact`・`constructor`・`obtain`・`cases`・`refine`）。
- 存在の証明は、証人を示して残りを示す（`exists_even_gt_ten`、`IsEven.add`）。
- 等式と不等式の連鎖は `calc` で書く（`two_mul_le_add`）。
- 帰納法は `induction` で書く（`sumOdd_eq`）。
- 自動化（`omega`・`simp`・`decide`）は、証明の一部を任せる道具である。どれを使っても、
  カーネルが検査するのは出来上がった項である（`call_spread_bounds` と `call_spread_bounds'`）。
- 金融数学への接続：整数の価格で、コール・スプレッドのペイオフの上下限を、場合分けによる
  数学者の証明と、`omega` による証明の 2 通りで示す。

Lean が受け付けない例と、途中のゴールの表示は `scripts/ch05_checks.lean` に置く。
-/

@[expose] public section

namespace LagrangeAcademy.Ch05

/-! ## タクティクで組み立てる証明項 -/

/-- 連言の入れ替えを、タクティクで証明する。`intro` で仮定に名前をつけ、`obtain` で組を分解し、
`exact` で組を作る。 -/
theorem and_swap_tac (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  obtain ⟨hp, hq⟩ := h
  exact ⟨hq, hp⟩

/-- 同じ命題を、ゴールを分けて証明する。`constructor` は連言のゴールを 2 つに分ける。 -/
theorem and_swap_split (p q : Prop) (h : p ∧ q) : q ∧ p := by
  constructor
  · exact h.2
  · exact h.1

/-- 選言の仮定は、`cases` で場合ごとに分ける。 -/
theorem or_swap_tac (p q : Prop) (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

/-! ## 存在の証明 -/

/-- 存在の証明は、証人（ここでは `12`）を示し、残りの命題を示す。 -/
theorem exists_even_gt_ten : ∃ n : Nat, 10 < n ∧ n % 2 = 0 := by
  refine ⟨12, ?_, ?_⟩
  · decide
  · decide

/-- 偶数であること：ある `k` について `n = 2 * k`。 -/
def IsEven (n : Nat) : Prop := ∃ k, n = 2 * k

/-- 偶数と偶数の和は偶数である。仮定の 2 つの存在から証人 `a`、`b` を取り出し、
新しい証人 `a + b` を示す。 -/
theorem IsEven.add {m n : Nat} (hm : IsEven m) (hn : IsEven n) : IsEven (m + n) := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  refine ⟨a + b, ?_⟩
  rw [ha, hb, Nat.mul_add]

/-! ## 等式と不等式の連鎖 -/

/-- `a ≤ b` なら `2 * a ≤ a + b`。紙の上の式の変形を、`calc` でそのまま書く。各行の理由は、
`:=` の後に書く。 -/
theorem two_mul_le_add {a b : Nat} (h : a ≤ b) : 2 * a ≤ a + b :=
  calc 2 * a = a + a := Nat.two_mul a
    _ ≤ a + b := Nat.add_le_add_left h a

/-! ## 帰納法 -/

/-- 最初の `n` 個の奇数の和：`1 + 3 + ⋯ + (2n - 1)`。 -/
def sumOdd : Nat → Nat
  | 0 => 0
  | n + 1 => sumOdd n + (2 * n + 1)

/-- 最初の `n` 個の奇数の和は `n * n` である。`induction` は、`n = 0` の場合と、`n` で成り立つ
という仮定 `ih` のもとで `n + 1` の場合の 2 つのゴールを作る。 -/
theorem sumOdd_eq (n : Nat) : sumOdd n = n * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumOdd, ih, Nat.add_mul, Nat.mul_add]
    omega

/-! ## 金融数学への接続：コール・スプレッドの上下限 -/

/-- 行使価格 `k` のコールの、満期のペイオフ（整数の価格）。 -/
def callPayoff (k s : Int) : Int := max (s - k) 0

/-- 行使価格 `k₁ ≤ k₂` のコール・スプレッド（`k₁` のコールを買い、`k₂` のコールを売る）の
満期のペイオフは、`0` 以上 `k₂ - k₁` 以下である。原資産価格 `s` が `k₁` 以下、`k₁` と `k₂` の間、
`k₂` 以上の 3 つの場合に分けて示す。 -/
theorem call_spread_bounds {k₁ k₂ : Int} (hk : k₁ ≤ k₂) (s : Int) :
    0 ≤ callPayoff k₁ s - callPayoff k₂ s ∧ callPayoff k₁ s - callPayoff k₂ s ≤ k₂ - k₁ := by
  unfold callPayoff
  by_cases h₁ : s ≤ k₁
  · -- s ≤ k₁ ≤ k₂：どちらのコールも行使されない
    have e₁ : max (s - k₁) 0 = 0 := Int.max_eq_right (by omega)
    have e₂ : max (s - k₂) 0 = 0 := Int.max_eq_right (by omega)
    rw [e₁, e₂]
    omega
  · by_cases h₂ : s ≤ k₂
    · -- k₁ < s ≤ k₂：k₁ のコールだけが行使される
      have e₁ : max (s - k₁) 0 = s - k₁ := Int.max_eq_left (by omega)
      have e₂ : max (s - k₂) 0 = 0 := Int.max_eq_right (by omega)
      rw [e₁, e₂]
      omega
    · -- k₂ < s：どちらのコールも行使される
      have e₁ : max (s - k₁) 0 = s - k₁ := Int.max_eq_left (by omega)
      have e₂ : max (s - k₂) 0 = s - k₂ := Int.max_eq_left (by omega)
      rw [e₁, e₂]
      omega

/-- 同じ命題を、`omega` に任せて証明する。`omega` は `max` を含む整数の線形の式を扱える。 -/
theorem call_spread_bounds' {k₁ k₂ : Int} (hk : k₁ ≤ k₂) (s : Int) :
    0 ≤ callPayoff k₁ s - callPayoff k₂ s ∧ callPayoff k₁ s - callPayoff k₂ s ≤ k₂ - k₁ := by
  unfold callPayoff
  omega

end LagrangeAcademy.Ch05

end
