module

/-!
# 第3章 依存型・帰納型・停止性

Lean 本体だけを使う（Mathlib は使わない）。

- 帰納型：自然数を自分で定義し（`MyNat`）、構造的再帰で足し算を書く。`a + zero = a` は定義から
  計算で閉じ、`zero + a = a` は帰納法が要る。
- 依存型：長さを型に持つベクトル（`Vec α n`）。空でないベクトルの先頭（`Vec.head`）や、
  範囲内の添字での取り出し（`Vec.get`）は、型が範囲外を許さない。
- `Prop` と `Type`：同じ命題の 2 つの証明は等しい（`proof_irrel`）。証人をデータとして使うときは、
  `Prop` の `∃` ではなく部分型を使う（`positiveWitness`）。
- 停止性：構造的再帰ではない再帰は、引数が減ることを示して書く（`numDigits`）。
- 金融数学への接続：満期の支払いの二分木（`PayoffTree`）。「どの状態でも支払いが非負」を
  帰納的に定義し、最小の支払いの計算と同値であることを示す。木が有限なので判定できる。

Lean が受け付けない例は `scripts/ch03_checks.lean` に置く。
-/

@[expose] public section

namespace LagrangeAcademy.Ch03

/-! ## 帰納型と構造的再帰 -/

/-- 自然数：`zero` から始めて `succ` を有限回つけたもの。 -/
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

/-- 足し算：2 つ目の引数についての構造的再帰。 -/
def MyNat.add : MyNat → MyNat → MyNat
  | a, .zero => a
  | a, .succ b => .succ (MyNat.add a b)

/-- `a + zero = a` は定義の 1 行目そのもので、計算すれば両辺が一致する。 -/
theorem MyNat.add_zero (a : MyNat) : MyNat.add a .zero = a := rfl

/-- `zero + a = a` は定義から直接は出ない。`a` についての帰納法が要る。 -/
theorem MyNat.zero_add (a : MyNat) : MyNat.add .zero a = a := by
  induction a with
  | zero => rfl
  | succ a ih => exact congrArg MyNat.succ ih

/-! ## 依存型：長さを型に持つベクトル -/

/-- 長さ `n` のベクトル。長さが型の一部になっている。 -/
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons {n : Nat} : α → Vec α n → Vec α (n + 1)

/-- 空でないベクトルの先頭。型が `Vec α (n + 1)` なので、`nil` の場合を書く必要がない。 -/
def Vec.head {α : Type} {n : Nat} : Vec α (n + 1) → α
  | .cons a _ => a

/-- 添字 `i : Fin n`（`i < n` の証明つきの自然数）での取り出し。範囲外の添字は渡せない。 -/
def Vec.get {α : Type} : {n : Nat} → Vec α n → Fin n → α
  | _, .cons a _, ⟨0, _⟩ => a
  | _, .cons _ v, ⟨i + 1, h⟩ => v.get ⟨i, Nat.lt_of_succ_lt_succ h⟩

/-- 先頭の取り出しは、添字 0 での取り出しと同じである。 -/
theorem Vec.get_zero {α : Type} {n : Nat} (a : α) (v : Vec α n) :
    (Vec.cons a v).get ⟨0, Nat.succ_pos n⟩ = (Vec.cons a v).head := rfl

/-! ## `Prop` と `Type` -/

/-- 証明の無関係性：同じ命題の 2 つの証明は、定義から等しい。 -/
theorem proof_irrel (p : Prop) (h₁ h₂ : p) : h₁ = h₂ := rfl

/-- 部分型 `{n : Nat // 0 < n}` の値は、自然数と、それが正であることの証明の組である。
自然数の部分は、データとして取り出して計算に使える。 -/
def positiveWitness (x : {n : Nat // 0 < n}) : Nat := x.val

/-- 取り出した値が正であることは、組の 2 つ目の成分が証明している。 -/
theorem positiveWitness_pos (x : {n : Nat // 0 < n}) : 0 < positiveWitness x := x.property

/-! ## 停止性：構造的再帰でない再帰 -/

/-- 10 進法の桁数。`n / 10` は `n` の部分項ではないので構造的再帰にならない。`n ≥ 10` なら
`n / 10 < n` であることを示して、再帰が止まることを Lean に納得させる。 -/
def numDigits (n : Nat) : Nat :=
  if n < 10 then 1 else numDigits (n / 10) + 1
termination_by n
decreasing_by omega

/-- 桁数の計算例。整礎再帰の定義は `rfl` では展開されないので、定義の等式で書き換える。 -/
theorem numDigits_12345 : numDigits 12345 = 5 := by
  simp [numDigits]

/-! ## 金融数学への接続：満期の支払いの木 -/

/-- 満期の支払いの二分木。各分岐は、上がる場合と下がる場合の 2 つの状態を表す。葉が満期の
状態で、そこでの支払いを持つ。 -/
inductive PayoffTree where
  | leaf (payoff : Int) : PayoffTree
  | branch (up down : PayoffTree) : PayoffTree

/-- すべての満期の状態での支払いの最小値（構造的再帰）。 -/
def PayoffTree.minPayoff : PayoffTree → Int
  | .leaf p => p
  | .branch u d => min u.minPayoff d.minPayoff

/-- 「どの満期の状態でも支払いが非負」を、木の形に沿って帰納的に定義した命題。 -/
def PayoffTree.AllNonneg : PayoffTree → Prop
  | .leaf p => 0 ≤ p
  | .branch u d => u.AllNonneg ∧ d.AllNonneg

/-- 「どの状態でも支払いが非負」と「最小の支払いが非負」は同値である。 -/
theorem PayoffTree.allNonneg_iff (t : PayoffTree) : t.AllNonneg ↔ 0 ≤ t.minPayoff := by
  induction t with
  | leaf p => exact Iff.rfl
  | branch u d ihu ihd =>
    simp only [AllNonneg, minPayoff]
    rw [ihu, ihd]
    omega

/-- 木は有限なので、`AllNonneg` は最小の支払いを計算して判定できる。 -/
instance (t : PayoffTree) : Decidable t.AllNonneg :=
  decidable_of_iff _ (PayoffTree.allNonneg_iff t).symm

/-- 具体的な木では、`decide` が計算して確かめる。 -/
theorem PayoffTree.example_allNonneg :
    (PayoffTree.branch (.leaf 3) (.branch (.leaf 0) (.leaf 5))).AllNonneg := by
  decide

/-- 負の支払いがある木では、`AllNonneg` は成り立たない。 -/
theorem PayoffTree.example_not_allNonneg :
    ¬(PayoffTree.branch (.leaf 3) (.leaf (-1))).AllNonneg := by
  decide

end LagrangeAcademy.Ch03

end
