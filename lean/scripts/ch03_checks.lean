/-
  第3章の確認用スクリプト。ライブラリには入れない（lake build の対象ではない）。
  `lean/` で次を実行すると、各行の結果が表示される。
    lake env lean scripts/ch03_checks.lean
  後半の定義と定理の多くは、Lean が受け付けない例である。実行するとエラーが出る。
-/
import LagrangeAcademy

open LagrangeAcademy.Ch03

-- 1. 宇宙：型の型
#check Prop
#check Type
#check (∀ α : Type, α → α)
#check (∀ p : Prop, p → p)

-- 2. 帰納型を定義すると、Lean は再帰子（帰納法の原理）を自動で作る
#check @MyNat.rec

-- 3. Prop の ∃ から、証人をデータとして取り出すことはできない
def rejected_witness (h : ∃ n : Nat, 0 < n) : Nat :=
  match h with
  | ⟨n, _⟩ => n

-- 4. 引数が減らない再帰は、停止することを示せない
def rejected_loop (n : Nat) : Nat := rejected_loop n

-- 5. partial は、返す型が空でないことを要求する（False を返す関数は作れない）
partial def rejected_partial_false (n : Nat) : False := rejected_partial_false n

-- 6. 自分自身を否定の位置に含む帰納型は、カーネルが拒否する
inductive RejectedNegative where
  | mk : (RejectedNegative → False) → RejectedNegative

-- 7. partial な定義は実行できるが、その性質を証明には使えない
partial def collatzSteps (n : Nat) : Nat :=
  if n ≤ 1 then 0
  else if n % 2 = 0 then collatzSteps (n / 2) + 1
  else collatzSteps (3 * n + 1) + 1

#eval collatzSteps 27

theorem rejected_collatz_one : collatzSteps 1 = 0 := rfl

-- 8. 整礎再帰の定義は、rfl や decide では展開されない（ライブラリでは simp で示した）
theorem rejected_numDigits_rfl : numDigits 12345 = 5 := rfl

-- 9. Type は Type の要素ではない
#check (Type : Type)
