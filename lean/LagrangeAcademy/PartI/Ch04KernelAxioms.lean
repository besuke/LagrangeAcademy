module

public import LagrangeAcademy.PartI.Ch02LogicCurryHoward
public import LagrangeAcademy.PartI.Ch03DependentInductive

/-!
# 第4章 Leanのカーネルと公理

Lean 本体だけを使う（Mathlib は使わない）。「Lean が証明した」というとき、何を信頼しているのか。

- 定義上の等式：`rfl` で閉じるのは、両辺が計算（β・δ・ι 簡約など）や η で一致する場合である。
  `n + 0 = n` は定義上の等式で、`0 + n = n` は命題としての等式（帰納法が要る）である。
- 3 つの公理：
  - `propext`：同値な命題は等しい（`and_true_eq`）。
  - `Quot.sound`：商型で、関係する要素は等しい（`Parity`）。関数の外延性 `funext` はこれから導かれる。
  - `Classical.choice`：空でない型から要素を 1 つ選ぶ。計算できない定義になる（`someWitness`）。
- 第3章の残りの問い：整礎再帰の定義は既定で展開されない（`numDigits_12345_rfl` は `unseal` で展開を許す）。
  `Vec.get_zero` の `propext` は、`Vec.head` の場合分けを翻訳した補助の定義から来る。
- 金融数学への接続：市場の仮定は `axiom` ではなく、定理の仮定として置く（`no_free_lunch`）。

Lean が受け付けない例と、`axiom` を置いた場合の表示は `scripts/ch04_checks.lean` に置く。
-/

@[expose] public section

namespace LagrangeAcademy.Ch04

open LagrangeAcademy.Ch02 LagrangeAcademy.Ch03

/-! ## 定義上の等式と命題としての等式 -/

/-- β 簡約（関数の適用）、δ 簡約（定義の展開）、ι 簡約（場合分けの計算）で、左辺は `3` になる。 -/
theorem beta_delta_iota : (fun x : Nat => x + 1) 2 = 3 := rfl

/-- η：`fun x => f x` と `f` は定義上等しい。 -/
theorem fun_eta (f : Nat → Nat) : (fun x => f x) = f := rfl

/-- `n + 0 = n` は、`Nat` の足し算の定義（2 つ目の引数についての再帰）の計算で閉じる。 -/
theorem nat_add_zero (n : Nat) : n + 0 = n := rfl

/-- `0 + n = n` は、`n` が変数のままでは計算が進まない。Lean 本体の定理 `Nat.zero_add`
（帰納法による証明）を使う。 -/
theorem nat_zero_add (n : Nat) : 0 + n = n := Nat.zero_add n

/-! ## 3 つの公理 -/

/-- `propext`：同値な命題は等しい。`p ∧ True` と `p` は同値なので、命題として等しい。 -/
theorem and_true_eq (p : Prop) : (p ∧ True) = p :=
  propext ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

/-- 関数の外延性：すべての入力で値が等しい関数は等しい。Lean 本体では `funext` は公理ではなく、
`Quot.sound` から導かれた定理である。 -/
theorem zero_add_fun : (fun n : Nat => 0 + n) = (fun n => n) :=
  funext Nat.zero_add

/-- 自然数を偶奇で同一視した商型。`a` と `b` は、`2` で割った余りが等しいとき同じ要素になる。 -/
def Parity : Type := Quot (fun a b : Nat => a % 2 = b % 2)

/-- `Quot.sound`：関係する 2 つの自然数（0 と 2）は、商型では等しい。 -/
theorem parity_zero_eq_two : (Quot.mk _ 0 : Parity) = Quot.mk _ 2 :=
  Quot.sound rfl

/-- 商型の上の関数は、同一視される要素に同じ値を返すことを示して作る（`Quot.lift`）。 -/
def Parity.isEven : Parity → Bool :=
  Quot.lift (fun n => n % 2 == 0) (fun a b (h : a % 2 = b % 2) => by simp [h])

/-- 商型の上の関数も計算できる。 -/
theorem Parity.isEven_four : Parity.isEven (Quot.mk _ 4) = true := rfl

/-- `Classical.choice`（を使う `Classical.choose`）：存在の証明から証人を「選ぶ」。
第3章で見たとおり、`∃` の証明からは計算で証人を取り出せない。選択公理を使えばデータとして
扱えるが、計算できない定義（`noncomputable`）になる。 -/
noncomputable def someWitness (h : ∃ n : Nat, 0 < n) : Nat := Classical.choose h

/-- 選んだ証人は、存在の証明が述べる性質を満たす。 -/
theorem someWitness_pos (h : ∃ n : Nat, 0 < n) : 0 < someWitness h := Classical.choose_spec h

/-! ## 第3章の残りの問い -/

unseal numDigits in
/-- 整礎再帰の定義 `numDigits` は、既定では展開されない（`@[irreducible]`）。`unseal` で展開を
許すと、`rfl` で計算できる。 -/
theorem numDigits_12345_rfl : numDigits 12345 = 5 := rfl

/-- `Vec.head` を使わずに、添字 0 での取り出しが先頭の要素であることを示す。どの公理にも
依存しない。第3章の `Vec.get_zero` は命題の中で `Vec.head` を使うので、`Vec.head` の
`propext` への依存を引き継いでいた。 -/
theorem vec_get_cons_zero {α : Type} {n : Nat} (a : α) (v : Vec α n) :
    (Vec.cons a v).get ⟨0, Nat.succ_pos n⟩ = a := rfl

/-! ## 金融数学への接続：仮定を定理の引数として置く -/

/-- 無裁定の市場では、今日お金を受け取れて（費用が負）、満期にどの状態でも支払いが非負になる
戦略は存在しない。無裁定は `axiom` ではなく、定理の仮定 `hna` として置く。 -/
theorem no_free_lunch (Θ Ω : Type) (cost : Θ → Int) (payoff : Θ → Ω → Int)
    (hna : NoArbitrage Θ Ω cost payoff) (θ : Θ) (hc : cost θ < 0)
    (hp : ∀ ω, 0 ≤ payoff θ ω) : False :=
  hna ⟨θ, Int.le_of_lt hc, hp, Or.inl hc⟩

end LagrangeAcademy.Ch04

end
