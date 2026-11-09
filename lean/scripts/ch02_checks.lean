/-
  第2章の確認用スクリプト。ライブラリには入れない（lake build の対象ではない）。
  `lean/` で次を実行すると、各行の結果が表示される。
    lake env lean scripts/ch02_checks.lean
  最後の 3 つは、Lean が受け付けない例である。実行するとエラーが出る。
-/
import LagrangeAcademy

open LagrangeAcademy.Ch02

-- 1. プログラムとしての swapPair を実行する
#eval swapPair Nat String (1, "a")

-- 2. 証明 and_swap とプログラム swapPair の項を表示する
#print and_swap
#print swapPair

-- 3. 古典論理なしで排中律を示そうとしても、項が作れない（`P` の証明も `¬P` の証明も手元にない）
theorem rejected_em (P : Prop) : P ∨ ¬P :=
  Or.inl _

-- 4. 排中律を decide で示そうとしても、`P` の真偽を計算するインスタンスがない
theorem rejected_em_decide (P : Prop) : P ∨ ¬P := by
  decide

-- 5. 要素の存在を仮定しないと、「すべて」から「ある」は出ない（証人を書けない）
theorem rejected_exists_of_forall (α : Type) (p : α → Prop) (h : ∀ x, p x) : ∃ x, p x :=
  ⟨_, h _⟩
