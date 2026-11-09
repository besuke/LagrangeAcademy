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

-- PartI/Ch02LogicCurryHoward.lean (Part I, chapter 2)
#print axioms LagrangeAcademy.Ch02.imp_self
#print axioms LagrangeAcademy.Ch02.imp_trans
#print axioms LagrangeAcademy.Ch02.and_swap
#print axioms LagrangeAcademy.Ch02.or_swap
#print axioms LagrangeAcademy.Ch02.and_imp_iff
#print axioms LagrangeAcademy.Ch02.false_elim
#print axioms LagrangeAcademy.Ch02.not_not_intro
#print axioms LagrangeAcademy.Ch02.not_not_em
#print axioms LagrangeAcademy.Ch02.em
#print axioms LagrangeAcademy.Ch02.of_not_not
#print axioms LagrangeAcademy.Ch02.forall_and_split
#print axioms LagrangeAcademy.Ch02.exists_imp
#print axioms LagrangeAcademy.Ch02.not_exists_iff
#print axioms LagrangeAcademy.Ch02.exists_of_forall
#print axioms LagrangeAcademy.Ch02.not_forall_imp_exists_empty
#print axioms LagrangeAcademy.Ch02.noArbitrage_iff_forall
#print axioms LagrangeAcademy.Ch02.not_noArbitrage_of_exists
#print axioms LagrangeAcademy.Ch02.exists_arbitrage_of_not_noArbitrage

-- PartI/Ch03DependentInductive.lean (Part I, chapter 3)
#print axioms LagrangeAcademy.Ch03.MyNat.add_zero
#print axioms LagrangeAcademy.Ch03.MyNat.zero_add
#print axioms LagrangeAcademy.Ch03.Vec.get_zero
#print axioms LagrangeAcademy.Ch03.proof_irrel
#print axioms LagrangeAcademy.Ch03.positiveWitness_pos
#print axioms LagrangeAcademy.Ch03.numDigits_12345
#print axioms LagrangeAcademy.Ch03.PayoffTree.allNonneg_iff
#print axioms LagrangeAcademy.Ch03.PayoffTree.example_allNonneg
#print axioms LagrangeAcademy.Ch03.PayoffTree.example_not_allNonneg
