module

public import LagrangeAcademy.PrdcTerms
public import LagrangeAcademy.PrdcCoupon

/-!
# 契約のクーポンと静的複製

第3章で定義した契約のクーポン `PrdcTerms.couponRate` が、キャップの有無のそれぞれで、
フロアとコールの和に等しいことを示す（第5章）。

- 有限のキャップ `c`：`couponRate S = floor + a ((S - K₁)⁺ - (S - K₂)⁺)`（コールスプレッド）
- キャップなし：`couponRate S = floor + a (S - K₁)⁺`（コール 1 本）

ここで `a = leverage / fxBase`、`K₁ = floorStrike`、`K₂ = capStrike c`。RiemannFinMath の
`compute_prdc_smile_value` は、有限のキャップでは 2 本のコールを、`cap = f64::INFINITY`
（キャップなし）では 1 本のコールを評価する。
-/

@[expose] public section

namespace LagrangeAcademy

namespace PrdcTerms

/-- 有限のキャップのクーポンは、フロアとコールスプレッドの和に等しい。 -/
theorem couponRate_eq_floor_add_call_spread (t : PrdcTerms) (c : ℝ) (h : t.cap = Cap.finite c)
    (S : ℝ) :
    t.couponRate S
      = t.floor + t.slope * (max (S - t.floorStrike) 0 - max (S - t.capStrike c) 0) := by
  simp only [couponRate, h, floorStrike, capStrike]
  exact prdc_coupon_eq_floor_add_call_spread t.slope t.subtraction t.floor c S t.slope_pos
    (t.floor_le_cap c h)

/-- キャップなしのクーポンは、フロアとコール 1 本の和に等しい。 -/
theorem couponRate_eq_floor_add_call (t : PrdcTerms) (h : t.cap = Cap.none) (S : ℝ) :
    t.couponRate S = t.floor + t.slope * max (S - t.floorStrike) 0 := by
  simp only [couponRate, h, floorStrike]
  exact prdc_coupon_without_cap_eq_floor_add_call t.slope t.subtraction t.floor S t.slope_pos

end PrdcTerms

end LagrangeAcademy

end
