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
| `LagrangeAcademy/PrdcCoupon.lean` | PRDC のクーポンの分解（RiemannFinMath の静的複製の拠り所） |
