# LagrangeAcademy

LagrangeFinance を受け継ぐ金融計算の教材。ユーザーとのやり取りは日本語。構想は `docs/concept.md`。

## 決定事項（2026-11-07）

- 新しいリポジトリとして作る。LagrangeFinance・GaussQuant・Curie・Riemann は、この教材の作業では変更しない。
- 中心の問いは「AI にできないこと」。「AI に任せても保証が残らないこと」として扱う（`docs/concept.md` 2 章）。
- 結果には保証の段（証明・照合・統計的検証・仮定）を付ける（同 3 章）。
- Lean を使い、計算が拠り所にする恒等式・不等式を証明する（同 4 章）。
- 最初は構想の文書から始める。
- GitHub：https://github.com/besuke/LagrangeAcademy（公開。ユーザーの判断で当面このまま、2026-11-07）。Lean の CI（`lean/.github/workflows/`、直下にないので動かない）は、まだ動かさない。
- 役割の分担：Rust（RiemannFinMath）で書き、Lean で証明し、R（Quarto）で描画する（同 7 章）。
- Lean は `lean/`（Lean 4.35.0、Mathlib v4.35.0、モジュール方式）。証明の合格は `lake build` が警告なし、かつ `lake env lean scripts/print_axioms.lean` で標準の 3 公理だけ。`sorry`・`axiom`・`partial`・弱い命題へのすり替えは不可（同 3.2 節）。

## 作業のきまり

- **QMD の役割**（2026-11-08 のユーザーの指示）：
  - Rust と Lean のソースコードを教材として示すのは、第1章（Rust）と第3〜5章（Lean）だけ。
  - それ以外の金融計算は、インストール済みの R パッケージ RiemannFinMath を使う。各章の QMD は `R/utility_LAD.R` を読み込み、そこを共通の入口として RiemannFinMath の公開関数を呼ぶ。QMD から RiemannFinMath を直接呼ばない。
  - 描画時に Rust をビルドしない。価格式を R で書き直さない。R の役割は、入力の準備、関数の呼び出し、結果の表・図への整形に限る。
  - 例の入力は `create_prdc_example_LAD()` のように `utility_LAD.R` の 1 か所にまとめる。

- 確かめていないことを断定しない。推定は「未確認の推定」と書く。
- 「AI にできないこと」の実例は、実際の作業記録に基づくものだけを書く。
- 市場の気配値（Bloomberg のデータ）は表や出力に出さない。
- コミットと push は、ユーザーに頼まれたときだけ行う。
