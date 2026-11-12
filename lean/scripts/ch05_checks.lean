/-
  第5章の確認用スクリプト。ライブラリには入れない（lake build の対象ではない）。
  `lean/` で次を実行すると、各行の結果が表示される。
    lake env lean scripts/ch05_checks.lean
  いくつかの定理は、途中で止めた証明や、Lean が受け付けない証明である。実行するとエラーが出る。
-/
import LagrangeAcademy

open LagrangeAcademy.Ch05

-- 1. タクティクで書いた証明も、出来上がるのは項である
#print and_swap_tac

-- 2. 途中で止めた証明：残ったゴールが表示される（⊢ の左が仮定、右が示す命題）
theorem stopped_and_swap (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  obtain ⟨hp, hq⟩ := h

-- 3. induction が作る 2 つのゴール
theorem stopped_sumOdd (n : Nat) : sumOdd n = n * n := by
  induction n with
  | zero => skip
  | succ n ih => skip

-- 4. 型が合わない：q を示すべきところに p の証明を渡す
theorem rejected_exact (p q : Prop) (hp : p) (hq : q) : q ∧ p := by
  constructor
  · exact hp
  · exact hp

-- 5. omega は変数どうしの掛け算を扱えない（n * n を 1 つの未知数とみなす）
theorem rejected_sumOdd_omega (n : Nat) : sumOdd n = n * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumOdd, ih]
    omega

-- 6. この命題の Decidable のインスタンスが構成できないので、decide は使えない
theorem rejected_decide : ∀ n : Nat, n + 0 = n := by decide

-- 7. exact? は、使える定理を探して提案する（発見）。提案を使った証明は、カーネルが検査する（検証）
example (a : Nat) : 2 * a = a + a := by exact?
