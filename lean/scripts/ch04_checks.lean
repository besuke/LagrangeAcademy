/-
  第4章の確認用スクリプト。ライブラリには入れない（lake build の対象ではない）。
  `lean/` で次を実行すると、各行の結果が表示される。
    lake env lean scripts/ch04_checks.lean
  いくつかの定義と定理は、Lean が受け付けない例である。実行するとエラーが出る。
  最後の節は、axiom を置くと何が起きるかを示すためだけのもので、ライブラリには置かない。
-/
import LagrangeAcademy

open LagrangeAcademy.Ch02 LagrangeAcademy.Ch03 LagrangeAcademy.Ch04

-- 1. タクティクで書いた証明も、カーネルが見るのは項である（第3章の MyNat.zero_add）
#print MyNat.zero_add

-- 2. 命題としての等式は、rfl では閉じない
theorem rejected_zero_add_rfl (n : Nat) : 0 + n = n := rfl

-- 3. 公理への依存：funext は Quot.sound から、排中律は 3 つの公理から導かれている
#print axioms funext
#print axioms Classical.em

-- 4. 整礎再帰の定義は @[irreducible] で、WellFounded.Nat.fix を使っている
#print numDigits

-- 5. Vec.get_zero の propext はどこから来るか
#print axioms Vec.head
set_option linter.auxLemma false in
#print axioms Vec.head.match_1
#print axioms Nat.Internal.elimOffset

-- 6. 選択公理を使う定義は、noncomputable をつけないと受け付けられない
def rejected_pick (h : Nonempty Nat) : Nat := Classical.choice h

-- 7. noncomputable な定義は実行できない
#eval someWitness ⟨1, Nat.one_pos⟩

-- 8. Prop は非可述的：すべての命題についての命題も Prop に入る。Type についての同じ形は 1 つ上の宇宙に入る
#check (∀ p : Prop, p → p)
#check (∀ α : Type, α → α)

-- 9. native_decide は、計算の結果を新しい公理として受け入れる。decide と比べる
theorem sum_range_ten_native : (List.range 10).foldl (· + ·) 0 = 45 := by native_decide
#print axioms sum_range_ten_decide
#print axioms sum_range_ten_native

-- 10. axiom を置くと、その名前が #print axioms に現れる。偽の axiom からは False が導ける
axiom bogusNoArbitrage : NoArbitrage Unit Unit (fun _ => -1) (fun _ _ => 0)

theorem false_from_bogus : False :=
  no_free_lunch Unit Unit (fun _ => -1) (fun _ _ => 0) bogusNoArbitrage () (by decide)
    (fun _ => by decide)

#print axioms false_from_bogus
