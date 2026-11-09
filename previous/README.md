# 旧原稿（2026-11-10 に退避）

『Leanから見た金融数学』の新しい構成に移る前の原稿である。内容は変更していない（`git mv` で移動）。

| ファイル | 旧構成での位置 |
|---|---|
| `intro/ch00_guarantee_ladder.qmd` | 序章 保証の階段と、AI にできないこと |
| `chapters/ch01_rust_finance.qmd` | 第1章 Rustの基礎と金融計算 |
| `chapters/ch02_r_calls_rust.qmd` | 第2章 RustとRのインターフェース |
| `chapters/ch03_lean_models.qmd` | 第3章 Leanの基礎と金融モデルの形式化 |
| `chapters/ch04_lean_proofs.qmd` | 第4章 Leanによる等式と不等式の証明 |
| `chapters/ch05_assumptions_and_scope.qmd` | 第5章 証明の前提と保証の範囲 |
| `chapters/ch06_no_arbitrage.qmd` | 第6章 無裁定 |
| `chapters/ch07_numeraire.qmd` | 第7章 ニューメレール |
| `chapters/ch08_martingale_measure.qmd` | 第8章 マーチンゲール測度 |
| `chapters/ch09_applications.qmd` | 第9章 金融商品への応用 |
| `quarto_previous.yml` | 旧構成の `_quarto.yml`（写し） |

- 本文の「第N章」は旧構成の章番号のままである。
- 旧原稿は `R/utility_LAD.R` と `lean/LagrangeAcademy/*.lean` を参照する。この 2 つはリポジトリの元の場所に残してある。
- 新しい本の描画（`_quarto.yml` の `render`）には含めていない。
