/-
  Prints the axioms each theorem depends on. Run from `lean/`:
    lake env lean scripts/print_axioms.lean
  A theorem passes only if it depends on nothing beyond propext, Classical.choice and Quot.sound
  (no sorryAx, no axiom of our own).
-/
import LagrangeAcademy

-- PrdcCoupon.lean (chapter 4)
#print axioms LagrangeAcademy.clamp_eq_floor_add_call_spread
#print axioms LagrangeAcademy.prdc_coupon_eq_floor_add_call_spread
#print axioms LagrangeAcademy.floor_eq_floor_add_call
#print axioms LagrangeAcademy.prdc_coupon_without_cap_eq_floor_add_call

-- PrdcTerms.lean (chapter 3)
#print axioms LagrangeAcademy.PrdcTerms.slope_pos

-- PrdcContract.lean (chapter 5)
#print axioms LagrangeAcademy.PrdcTerms.couponRate_eq_floor_add_call_spread
#print axioms LagrangeAcademy.PrdcTerms.couponRate_eq_floor_add_call

-- PartI/Ch01ComputationProof.lean (Part I, chapter 1)
#print axioms LagrangeAcademy.Ch01.sumTo_ten
#print axioms LagrangeAcademy.Ch01.two_mul_sumTo_of_lt_100
#print axioms LagrangeAcademy.Ch01.two_mul_sumTo
#print axioms LagrangeAcademy.Ch01.two_mul_sumTo'
#print axioms LagrangeAcademy.Ch01.call_sub_put_payoff
