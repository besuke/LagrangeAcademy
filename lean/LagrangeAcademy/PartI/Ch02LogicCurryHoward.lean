module

/-!
# 第2章 論理学とCurry–Howard対応

Lean 本体だけを使う（Mathlib は使わない）。命題は型であり、証明はその型の項である。

- 命題論理：含意は関数、連言は組、選言は「どちらか」の印がついた値、偽は値を持たない型。
- プログラムとの対応：`and_swap`（証明）と `swapPair`（プログラム）は同じ形の項である。
- 構成的論理と古典論理：`not_not_em` は古典論理なしで証明できる。`em` と
  `of_not_not` は `Classical` を使う。
- 述語論理：全称は依存関数、存在は「証人と証明の組」。空の型では
  「すべての `x` で成り立つなら、ある `x` で成り立つ」が偽になる（`not_forall_imp_exists_empty`）。
- 金融数学への接続：裁定と無裁定を論理式として書く。「無裁定でない」から
  「裁定がある」を導くには古典論理が要る（`exists_arbitrage_of_not_noArbitrage`）。

Lean が受け付けない例は `scripts/ch02_checks.lean` に置く。
-/

@[expose] public section

namespace LagrangeAcademy.Ch02

/-! ## 命題論理 -/

/-- 含意の導入：`P` の証明を受け取って、そのまま返す関数が `P → P` の証明である。 -/
theorem imp_self (P : Prop) : P → P :=
  fun hp => hp

/-- 含意の推移律：2 つの関数の合成が証明になる。 -/
theorem imp_trans (P Q R : Prop) (hpq : P → Q) (hqr : Q → R) : P → R :=
  fun hp => hqr (hpq hp)

/-- 連言の交換：組 `⟨hp, hq⟩` を受け取り、順序を入れ替えた組を返す。 -/
theorem and_swap (P Q : Prop) : P ∧ Q → Q ∧ P :=
  fun ⟨hp, hq⟩ => ⟨hq, hp⟩

/-- `and_swap` と同じ形のプログラム：2 つの値の組の順序を入れ替える。 -/
def swapPair (α β : Type) : α × β → β × α :=
  fun ⟨a, b⟩ => ⟨b, a⟩

/-- 選言の交換：どちらの側の証明かで場合を分ける。 -/
theorem or_swap (P Q : Prop) : P ∨ Q → Q ∨ P :=
  fun h =>
    match h with
    | Or.inl hp => Or.inr hp
    | Or.inr hq => Or.inl hq

/-- カリー化：「`P` かつ `Q` なら `R`」と「`P` なら、`Q` なら `R`」は同値である。 -/
theorem and_imp_iff (P Q R : Prop) : (P ∧ Q → R) ↔ (P → Q → R) :=
  ⟨fun h hp hq => h ⟨hp, hq⟩, fun h ⟨hp, hq⟩ => h hp hq⟩

/-- 偽からは何でも導ける：`False` には値がないので、場合分けの枝が 1 つもない。 -/
theorem false_elim (P : Prop) : False → P :=
  fun h => nomatch h

/-- 否定 `¬P` は `P → False` である。`P` が成り立てば、`¬P` は成り立たない。 -/
theorem not_not_intro (P : Prop) : P → ¬¬P :=
  fun hp hnp => hnp hp

/-! ## 構成的論理と古典論理 -/

/-- 排中律の二重否定は、古典論理なしで証明できる。 -/
theorem not_not_em (P : Prop) : ¬¬(P ∨ ¬P) :=
  fun h => h (Or.inr (fun hp => h (Or.inl hp)))

/-- 排中律：Lean では `Classical.em` から得る（古典論理）。 -/
theorem em (P : Prop) : P ∨ ¬P :=
  Classical.em P

/-- 二重否定の除去：排中律で場合を分ける（古典論理）。 -/
theorem of_not_not (P : Prop) : ¬¬P → P :=
  fun h =>
    match Classical.em P with
    | Or.inl hp => hp
    | Or.inr hnp => False.elim (h hnp)

/-! ## 述語論理 -/

/-- 全称と連言：「すべての `x` で `p x` かつ `q x`」なら、「すべての `x` で `p x`」かつ
「すべての `x` で `q x`」。 -/
theorem forall_and_split (α : Type) (p q : α → Prop) :
    (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x) :=
  fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩

/-- 存在の除去：証人 `x` とその証明を取り出して使う。 -/
theorem exists_imp (α : Type) (p q : α → Prop) (hpq : ∀ x, p x → q x) :
    (∃ x, p x) → ∃ x, q x :=
  fun ⟨x, hx⟩ => ⟨x, hpq x hx⟩

/-- 存在しないことは、すべての `x` で成り立たないことと同値である（古典論理は要らない）。 -/
theorem not_exists_iff (α : Type) (p : α → Prop) : (¬∃ x, p x) ↔ ∀ x, ¬p x :=
  ⟨fun h x hx => h ⟨x, hx⟩, fun h ⟨x, hx⟩ => h x hx⟩

/-- 要素 `a` が 1 つあれば、「すべての `x` で成り立つ」から「ある `x` で成り立つ」が出る。 -/
theorem exists_of_forall (α : Type) (a : α) (p : α → Prop) : (∀ x, p x) → ∃ x, p x :=
  fun h => ⟨a, h a⟩

/-- 要素のない型 `Empty` では、同じ含意が偽になる。 -/
theorem not_forall_imp_exists_empty : ¬((∀ _ : Empty, False) → ∃ _ : Empty, False) :=
  fun h =>
    match h (fun x => x.elim) with
    | ⟨x, _⟩ => x.elim

/-! ## 金融数学への接続：裁定を論理式で書く -/

/-- 1 期間の市場での裁定（価格は整数）。`cost θ` は戦略 `θ` の今日の費用、`payoff θ ω` は
状態 `ω` での満期の支払い。費用が 0 以下で、どの状態でも支払いが非負で、さらに費用が負か、
ある状態で支払いが正である。 -/
def IsArbitrage (Θ Ω : Type) (cost : Θ → Int) (payoff : Θ → Ω → Int) (θ : Θ) : Prop :=
  cost θ ≤ 0 ∧ (∀ ω, 0 ≤ payoff θ ω) ∧ (cost θ < 0 ∨ ∃ ω, 0 < payoff θ ω)

/-- 無裁定：裁定になる戦略が存在しない。 -/
def NoArbitrage (Θ Ω : Type) (cost : Θ → Int) (payoff : Θ → Ω → Int) : Prop :=
  ¬∃ θ, IsArbitrage Θ Ω cost payoff θ

/-- 無裁定は「どの戦略も裁定ではない」と同値である（古典論理は要らない）。 -/
theorem noArbitrage_iff_forall (Θ Ω : Type) (cost : Θ → Int) (payoff : Θ → Ω → Int) :
    NoArbitrage Θ Ω cost payoff ↔ ∀ θ, ¬IsArbitrage Θ Ω cost payoff θ :=
  not_exists_iff Θ (IsArbitrage Θ Ω cost payoff)

/-- 裁定になる戦略を 1 つ示せば、無裁定ではない（古典論理は要らない）。 -/
theorem not_noArbitrage_of_exists (Θ Ω : Type) (cost : Θ → Int) (payoff : Θ → Ω → Int)
    (h : ∃ θ, IsArbitrage Θ Ω cost payoff θ) : ¬NoArbitrage Θ Ω cost payoff :=
  fun hna => hna h

/-- 「無裁定でない」から「裁定になる戦略が存在する」を導く。二重否定の除去を使う（古典論理）。
この証明は、どの戦略が裁定になるかを示さない。 -/
theorem exists_arbitrage_of_not_noArbitrage (Θ Ω : Type) (cost : Θ → Int)
    (payoff : Θ → Ω → Int) (h : ¬NoArbitrage Θ Ω cost payoff) :
    ∃ θ, IsArbitrage Θ Ω cost payoff θ :=
  of_not_not _ h

end LagrangeAcademy.Ch02

end
