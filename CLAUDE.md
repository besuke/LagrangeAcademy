# LagrangeAcademy

LagrangeFinance を受け継ぐ金融計算の教材。ユーザーとのやり取りは日本語。構想は `docs/concept.md`。

## 決定事項（2026-11-07）

- 新しいリポジトリとして作る。LagrangeFinance・GaussQuant・Curie・Riemann は、この教材の作業では変更しない。
- 中心の問いは「AI にできないこと」。「AI に任せても保証が残らないこと」として扱う（`docs/concept.md` 2 章）。
- 結果には保証の段（証明・照合・統計的検証・仮定）を付ける（同 3 章）。
- Lean を使い、計算が拠り所にする恒等式・不等式を証明する（同 4 章）。
- 最初は構想の文書から始める。
- 役割の分担：Rust（RiemannFinMath）で書き、Lean で証明し、R（Quarto）で描画する（同 7 章）。
- Lean は `lean/`（Lean 4.35.0、Mathlib v4.35.0、モジュール方式）。証明の合格は `lake build` が警告なし、かつ `lake env lean scripts/print_axioms.lean` で標準の 3 公理だけ。`sorry`・`axiom`・`partial`・弱い命題へのすり替えは不可（同 3.2 節）。

## 作業のきまり

- 確かめていないことを断定しない。推定は「未確認の推定」と書く。
- 「AI にできないこと」の実例は、実際の作業記録に基づくものだけを書く。
- 市場の気配値（Bloomberg のデータ）は表や出力に出さない。
- コミットと push は、ユーザーに頼まれたときだけ行う。
