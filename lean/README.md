# LagrangeAcademy の Lean プロジェクト

Lean 4.35.0 と Mathlib v4.35.0。金融計算が拠り所にする恒等式・不等式を証明する。

```
lake exe cache get                         # Mathlib のビルド済みファイルを取得
lake build                                 # すべての証明を検査
lake env lean scripts/print_axioms.lean    # 各定理が依存する公理を表示
```

合格の条件は 2 つ。

- `lake build` が警告なしで通る。
- 各定理が `propext`、`Classical.choice`、`Quot.sound` 以外の公理に依存しない（`sorryAx` も独自の `axiom` も使わない）。

| ファイル | 内容 |
|---|---|
| `LagrangeAcademy/PrdcCoupon.lean` | 実数の恒等式：クーポンの分解（有限のキャップ、キャップなし）（第4章） |
| `LagrangeAcademy/PrdcTerms.lean` | PRDC の条件と仮定、キャップの有無 `Cap`、契約のクーポン `couponRate`（第3章） |
| `LagrangeAcademy/PrdcContract.lean` | 契約のクーポンの 2 つの式（RiemannFinMath の静的複製の拠り所）（第5章） |
