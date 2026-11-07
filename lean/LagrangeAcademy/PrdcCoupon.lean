module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# PRDC のクーポンの分解

  クーポン `clamp(a S - b, f, c)` は、フロア `f` と、FX の水準 `K₁ = (b + f) / a`、
  `K₂ = (b + c) / a` のコールスプレッドの `a` 倍の和に等しい。RiemannFinMath の
  `compute_prdc_smile_value`（静的複製）は、この恒等式を拠り所にしている。

  左辺は Riemann の実装 `(a S - b).max(floor).min(cap)` と同じ形
  `min (max (a S - b) f) c` で書く。

  この証明が保証するのは実数の上の恒等式であり、次のことは保証しない。
  - Rust の浮動小数点の計算が正しいこと
  - この式が契約の条項を正しく表していること（人が確かめる）
-/

@[expose] public section

namespace LagrangeAcademy

/-- 区間 `[f, c]` への切り詰めは、`f` に、行使価格 `f` と `c` のコールスプレッドを
足したものに等しい。 -/
theorem clamp_eq_floor_add_call_spread (y f c : ℝ) (hfc : f ≤ c) :
    min (max y f) c = f + (max (y - f) 0 - max (y - c) 0) := by
  rcases le_total y f with h | h
  · -- フロアの下
    rw [max_eq_right h, min_eq_left hfc, max_eq_right (by linarith : y - f ≤ 0),
      max_eq_right (by linarith : y - c ≤ 0)]
    ring
  · rcases le_total y c with h' | h'
    · -- フロアとキャップの間
      rw [max_eq_left h, min_eq_left h', max_eq_left (by linarith : (0 : ℝ) ≤ y - f),
        max_eq_right (by linarith : y - c ≤ 0)]
      ring
    · -- キャップの上
      rw [max_eq_left h, min_eq_right h', max_eq_left (by linarith : (0 : ℝ) ≤ y - f),
        max_eq_left (by linarith : (0 : ℝ) ≤ y - c)]
      ring

/-- PRDC のクーポンの分解：`a > 0`、`f ≤ c` のとき、
`min (max (a S - b) f) c = f + a ((S - K₁)⁺ - (S - K₂)⁺)`。 -/
theorem prdc_coupon_eq_floor_add_call_spread (a b f c S : ℝ) (ha : 0 < a) (hfc : f ≤ c) :
    min (max (a * S - b) f) c
      = f + a * (max (S - (b + f) / a) 0 - max (S - (b + c) / a) 0) := by
  have ha' : a ≠ 0 := ha.ne'
  have scale : ∀ k : ℝ, a * max (S - (b + k) / a) 0 = max (a * S - b - k) 0 := by
    intro k
    rw [mul_max_of_nonneg _ _ ha.le, mul_zero]
    congr 1
    field_simp
    ring
  rw [mul_sub, scale f, scale c]
  exact clamp_eq_floor_add_call_spread (a * S - b) f c hfc

end LagrangeAcademy

end
