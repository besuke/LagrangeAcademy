# LagrangeAcademy

『Leanから見た金融数学』（LagrangeFinance を受け継ぐ金融数学・金融計算の教材）。ユーザーとのやり取りは日本語。本の出発点は `index.qmd`（はじめに、ユーザーの文章）。構想は `docs/concept.md`（2026-11-07 の初版。新しい構成は、論点が固まってから反映する）。

## 決定事項

- **題名と構成**（2026-11-10）：題名は『Leanから見た金融数学』、副題は「型理論・形式的証明から金融モデルの数値実装へ」。金融数学を理論の中心に置き、金融工学はその応用として扱う。3 部構成で、分量の目安は第I部（Lean の論理・型理論・形式的証明）約 30%、第II部（無裁定を中心とした金融数学）約 30%、第III部（Lean・Rust・R による数値実装と検証）約 40%。第II部と第III部の章立ては、まだ確定しない。
- **想定読者と動機**（2026-11-10）：情報科学を大学院レベルまで学んだ人。Lean の知識は前提にしない。執筆の動機（AI がプログラムを書く時代に、情報科学を学んだ人間は何を考えるべきか）は「はじめに」で述べ、各章では繰り返さない。
- **本の軸**（2026-11-08）：「この価格は、どの市場の仮定のもとで、無裁定条件を満たすのか」。何に投資し、何を物差し（ニューメレール）とし、どの仮定のもとで価格が無裁定となるかに、モデルを作るたびに立ち返る。
- **第I部**（2026-11-10）：「なぜLeanは数学の定理を証明できるのか」。全 9 章で、独立した日本語の Lean 入門としても読めるようにする。
  1. 計算と証明
  2. 論理学とCurry–Howard対応
  3. 依存型・帰納型・停止性
  4. Leanのカーネルと公理
  5. Lean 4による定理証明
  6. 構造体・型クラス・数学的仮定
  7. 実数と数値計算
  8. Mathlibの数学構造と確率論
  9. AIと形式的証明

  第5章までは Lean 本体を中心にし、Mathlib は第6章から本格的に使う。AI の話題は第9章を中心に扱う。
- **第II部の範囲**（2026-11-10）：連続時間の金融数学も Lean による形式的証明の対象として扱う。とくに伊藤の公式、Girsanov の定理、無裁定価格理論、ニューメレールの変更を重要な参照対象とする（formal-mathfin、brownian-motion）。参照先の README の記述と、実際に確かめた定理は区別して書く。
- **第I部での外部の形式化**（2026-11-10）：例題や参考文献として使うが、Lean 自体の解説を優先する。第1章では、formal-mathfin の CRR から Black–Scholes への収束定理（`binomialPrice_call_tendsto_bs_closed`）を研究例として簡単に紹介するだけにし、証明の詳しい説明は第II部に回す。
- **旧原稿**（2026-11-10）：旧構成の序章と第1〜9章は `previous/` に、内容を変えずに退避した（`previous/README.md`）。旧原稿の「第N章」は旧構成の番号のまま直さない。新しい本の描画には含めない。
- **QuantLib は使わない**（2026-11-08）：LagrangeAcademy には QuantLib への言及・照合表・参照リンクを置かない。保証の階段の段 2 は「数値の確認」（RiemannFinMath の数値が、無裁定から導いた関係・閉じた式を満たすか）。
- 新しいリポジトリとして作る。LagrangeFinance・GaussQuant・Curie・Riemann は、この教材の作業では変更しない。
- 役割の分担：Rust（RiemannFinMath）で書き、Lean で証明し、R（Quarto）で描画する（`docs/concept.md` 7 章）。
- Lean は `lean/`（Lean 4.35.0、Mathlib v4.35.0、モジュール方式）。証明の合格は `lake build` が警告なし、かつ `lake env lean scripts/print_axioms.lean` で標準の 3 公理だけ。`sorry`・`axiom`・`partial`・弱い命題へのすり替えは不可（同 3.2 節）。
- GitHub：https://github.com/besuke/LagrangeAcademy（公開。ユーザーの判断で当面このまま、2026-11-07）。Lean の CI（`lean/.github/workflows/`、直下にないので動かない）は、まだ動かさない。

## 作業のきまり

- **章の書き方**（2026-11-10 のユーザーの指示）：
  - 第I部の各章は「問題提起 → 数学的背景 → Lean による説明 → 検証 → 金融数学への接続」を基本の順にする。金融の例は章末に置き、金融の例のために Lean の説明を薄くしない。
  - 第II部以降の章の構成規約は、後で決める。
- **QMD の役割**（2026-11-08 のユーザーの指示。2026-11-10 に第I部について改めた）：
  - 第I部では Lean のコードを積極的に載せる。載せるコードは、`lean/LagrangeAcademy/` の検査済みのファイルから読み込む（`show_lean_source_LAD()`、`show_lean_theorem_LAD()`）。QMD に手で写したコードを、検査済みとして示さない。
  - 金融計算は、インストール済みの R パッケージ RiemannFinMath を使う。各章の QMD は `R/utility_LAD.R` を読み込み、そこを共通の入口として RiemannFinMath の公開関数を呼ぶ。QMD から RiemannFinMath を直接呼ばない。
  - 描画時に Rust をビルドしない。価格式を R で書き直さない。R の役割は、入力の準備、関数の呼び出し、結果の表・図への整形、無裁定の関係の数値による確認に限る。
  - 例の入力は `create_prdc_example_LAD()` のように `utility_LAD.R` の 1 か所にまとめる。
- **既存の形式化を参照する**（2026-11-10 のユーザーの指示）：
  - 各章の例題は、既存の Lean の数学ライブラリと形式化研究を積極的に参照する。主な参照先は formal-mathfin（https://github.com/formal-applied-math/formal-mathfin）、brownian-motion（https://github.com/RemyDegenne/brownian-motion）、Mathlib（https://github.com/leanprover-community/mathlib4）。
  - 第1〜5章は Lean 本体による論理・型理論・証明の基礎を優先し、Mathlib の数学構造は第6章から本格的に使う。第8章は有限確率空間を中心にし、brownian-motion への橋渡しをする。第9章は formal-mathfin などの実際の金融数学の形式化を題材に、AI が生成した証明をカーネルが検証する意味を説明する。
  - 例題を作るときは、参照元の定理名・ファイルパス・使う仮定を確かめ、参照元（リポジトリ、コミット、ファイル）を明記する。丸写しせず、読者が理解できる最小限の例題に段階的に組み立て直す。
  - 外部ライブラリは参照・調査にとどめ、`lean/` の依存関係（`lakefile.toml`、`lake-manifest.json`）を無断で変えない。調べるときは作業用のフォルダーに clone し、ビルドしない。
  - 参照した版（2026-11-10 に確認）：formal-mathfin `406ddbb`（2026-11-09、Lean 4.35.0、Mathlib の上に BrownianMotion）、brownian-motion `8fd8dc5`（2026-11-05、Lean 4.36.0-rc2）。README の記述は各リポジトリの自己申告で、こちらでビルドして確かめたものではない。
- 公理、定理の仮定、証明済みの結果を区別して書く。仮定として置いた結果を、Lean が証明した定理と呼ばない。`sorry`、`axiom`、明示的な仮定、実際に証明した定理を厳密に区別する。
- 確かめていないことを断定しない。推定は「未確認の推定」と書く。数値例の確認は「この例で成り立つ」ことだけで、命題の証明ではないと書く。
- 「AI にできないこと」の実例は、実際の作業記録に基づくものだけを書く。実行していない結果や作業記録を創作しない。
- 市場の気配値（Bloomberg のデータ）は表や出力に出さない。例の入力は合成の値と明記する。
- コミットと push は、ユーザーに頼まれたときだけ行う。

## 現在の状態と次の作業（引継ぎ、2026-11-10）

**進め方**（ユーザーの指示）：第I部を 1 章ずつ、Claude が執筆（本文・Lean のコード・演習）→ ChatGPT が内容をレビュー（ユーザーが読んだ『Lean Programming for AI Agents』と照らす）→ Claude が指摘を反映し、Lean の検証と描画を確かめる → 章ごとに commit と push、の順に進める。

**状態**：

- 目次：はじめに、第I部の第1〜9章。第II部・第III部はまだない。章番号は `_quarto.yml` の `number-sections: true` で自動採番。描画の対象は `index.qmd` とルートの `ch*.qmd`。
- 第I部の章ファイル（ルート）：`ch01_computation_and_proof.qmd` 〜 `ch09_ai_and_formal_proof.qmd`。
- Lean：旧構成の `PrdcTerms.lean`、`PrdcCoupon.lean`、`PrdcContract.lean` の 7 定理（警告なし、公理は標準の 3 つだけ。2026-11-08 に確認）。旧原稿と、のちの章が使う。
- `R/utility_LAD.R`：パッケージの確認、ソースの表示、PRDC の例の入力、RiemannFinMath の呼び出し、無裁定の関係の数値による確認、整形。読み込むと RiemannFinMath が入っているかを確かめる。
- PRDC の発展の計画（5 段階、段 A〜C、発行体コールと Longstaff–Schwartz）と、未証明の命題は、旧原稿 `previous/chapters/ch09_applications.qmd` の「この節の発展の計画」「この節に残る命題」にある。第III部の検討で使う。

**人の確認待ち**（ユーザーの作業）：旧原稿 `previous/chapters/ch05_assumptions_and_scope.qmd` の「命題と実装を照らす」の表と、確認の記録の「人の確認待ち」。すべて「未」。

**手順**：

- 描画：このリポジトリで `quarto render --to html`。RiemannFinMath は事前に `R CMD INSTALL`（Riemann のリポジトリ）で入れておく。描画では Rust をビルドしない。
- 描画が途中で `WARN: Error encountered when rendering files` だけを出して止まることがある（2026-11-08 に 1 回）。その章だけを `quarto render <章>.qmd --to html --log-level debug` で描画して確かめ、全体をもう一度描画すると通った。原因は未確認。
- Lean：`lean/` で `lake build` と `lake env lean scripts/print_axioms.lean`。新しい定理は `scripts/print_axioms.lean` に加える。
- bash のヒアドキュメントでは `\\` が `\` になる。バックスラッシュを含む編集スクリプトは Write でファイルに書いて実行する。
