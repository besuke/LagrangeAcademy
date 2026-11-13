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

-- PartI/Ch04KernelAxioms.lean (Part I, chapter 4)
#print axioms LagrangeAcademy.Ch04.beta_delta_iota
#print axioms LagrangeAcademy.Ch04.fun_eta
#print axioms LagrangeAcademy.Ch04.proof_irrel_rfl
#print axioms LagrangeAcademy.Ch04.subtype_eq_rfl
#print axioms LagrangeAcademy.Ch04.sum_range_ten_decide
#print axioms LagrangeAcademy.Ch04.nat_add_zero
#print axioms LagrangeAcademy.Ch04.nat_zero_add
#print axioms LagrangeAcademy.Ch04.and_true_eq
#print axioms LagrangeAcademy.Ch04.zero_add_fun
#print axioms LagrangeAcademy.Ch04.parity_zero_eq_two
#print axioms LagrangeAcademy.Ch04.Parity.isEven_four
#print axioms LagrangeAcademy.Ch04.someWitness_pos
#print axioms LagrangeAcademy.Ch04.numDigits_12345_rfl
#print axioms LagrangeAcademy.Ch04.vec_get_cons_zero
#print axioms LagrangeAcademy.Ch04.no_free_lunch

-- PartI/Ch05TheoremProving.lean (Part I, chapter 5)
#print axioms LagrangeAcademy.Ch05.and_swap_tac
#print axioms LagrangeAcademy.Ch05.and_swap_split
#print axioms LagrangeAcademy.Ch05.or_swap_tac
#print axioms LagrangeAcademy.Ch05.exists_even_gt_ten
#print axioms LagrangeAcademy.Ch05.IsEven.add
#print axioms LagrangeAcademy.Ch05.two_mul_le_add
#print axioms LagrangeAcademy.Ch05.sumOdd_eq
#print axioms LagrangeAcademy.Ch05.call_spread_bounds
#print axioms LagrangeAcademy.Ch05.call_spread_bounds'

-- PartI/Ch06StructuresClasses.lean (Part I, chapter 6)
#print axioms LagrangeAcademy.Ch06.PosNat.add_val
#print axioms LagrangeAcademy.Ch06.isEven_iff_mod
#print axioms LagrangeAcademy.Ch06.isEven_ten
#print axioms LagrangeAcademy.Ch06.not_isEven_seven
#print axioms LagrangeAcademy.Ch06.zero_add_add_zero
#print axioms LagrangeAcademy.Ch06.zero_add_add_zero_nat
#print axioms LagrangeAcademy.Ch06.add_sq_ring
#print axioms LagrangeAcademy.Ch06.add_sq_ring_int
#print axioms LagrangeAcademy.Ch06.add_sq_ring_rat
#print axioms LagrangeAcademy.Ch06.OnePeriodBinomial.d_lt_u
#print axioms LagrangeAcademy.Ch06.OnePeriodBinomial.q_pos
#print axioms LagrangeAcademy.Ch06.OnePeriodBinomial.q_lt_one
#print axioms LagrangeAcademy.Ch06.exampleModel_q

-- PartI/Ch07RealsFloats.lean (Part I, chapter 7)
#print axioms LagrangeAcademy.Ch07.rat_add
#print axioms LagrangeAcademy.Ch07.real_add
#print axioms LagrangeAcademy.Ch07.float_add_ne
#print axioms LagrangeAcademy.Ch07.float_add_not_assoc
#print axioms LagrangeAcademy.Ch07.float_absorb
#print axioms LagrangeAcademy.Ch07.float_zero_ne_neg_zero
#print axioms LagrangeAcademy.Ch07.call_sub_put_payoff_real
#print axioms LagrangeAcademy.Ch07.discount_pos
#print axioms LagrangeAcademy.Ch07.discount_le_one
#print axioms LagrangeAcademy.Ch07.exp_one_bounds

-- PartI/Ch08Probability.lean (Part I, chapter 8)
#print axioms LagrangeAcademy.Ch08.FinProb.expect_const
#print axioms LagrangeAcademy.Ch08.FinProb.expect_add
#print axioms LagrangeAcademy.Ch08.FinProb.expect_smul
#print axioms LagrangeAcademy.Ch08.FinProb.expect_nonneg
#print axioms LagrangeAcademy.Ch08.FinProb.expect_mono
#print axioms LagrangeAcademy.Ch08.integral_eq_sum
#print axioms LagrangeAcademy.Ch08.Binomial.expect_stock
#print axioms LagrangeAcademy.Ch08.Binomial.discounted_expect_nonneg

-- PartI/Ch09AIProof.lean (Part I, chapter 9)
#print axioms LagrangeAcademy.Ch09.expect_stock_of_spec
#print axioms LagrangeAcademy.Ch09.stockMartingaleSpec_holds
#print axioms LagrangeAcademy.Ch09.BadBinomial.anything
#print axioms LagrangeAcademy.Ch09.badBinomial_isEmpty
#print axioms LagrangeAcademy.Ch09.onePeriodBinomial_nonempty
#print axioms LagrangeAcademy.Ch09.exists_prob_weak

-- PartII/Ch10FiniteMarket.lean (Part II, chapter 10)
#print axioms LagrangeAcademy.Ch10.FiniteMarket.cost_combo
#print axioms LagrangeAcademy.Ch10.FiniteMarket.payoff_combo
#print axioms LagrangeAcademy.Ch10.FiniteMarket.cost_sub
#print axioms LagrangeAcademy.Ch10.FiniteMarket.payoff_sub
#print axioms LagrangeAcademy.Ch10.FiniteMarket.law_of_one_price
#print axioms LagrangeAcademy.Ch10.FiniteMarket.replication_price_unique
#print axioms LagrangeAcademy.Ch10.FiniteMarket.cost_le_of_payoff_le
#print axioms LagrangeAcademy.Ch10.FiniteMarket.cost_lt_of_payoff_le_of_lt
#print axioms LagrangeAcademy.Ch10.FiniteMarket.cost_unit
#print axioms LagrangeAcademy.Ch10.FiniteMarket.payoff_unit
#print axioms LagrangeAcademy.Ch10.FiniteMarket.price_between_of_dominated
#print axioms LagrangeAcademy.Ch10.FiniteMarket.put_call_parity
#print axioms LagrangeAcademy.Ch10.FiniteMarket.call_payoff_antitone
#print axioms LagrangeAcademy.Ch10.FiniteMarket.call_payoff_sub_le
#print axioms LagrangeAcademy.Ch10.FiniteMarket.call_price_antitone
#print axioms LagrangeAcademy.Ch10.FiniteMarket.call_spread_price_le
#print axioms LagrangeAcademy.Ch10.FiniteMarket.call_payoff_convex
#print axioms LagrangeAcademy.Ch10.FiniteMarket.call_price_convex
#print axioms LagrangeAcademy.Ch10.FiniteMarket.cost_eq_statePrice
#print axioms LagrangeAcademy.Ch10.FiniteMarket.noArbitrage_of_statePrice
#print axioms LagrangeAcademy.Ch10.twoState_complete
#print axioms LagrangeAcademy.Ch10.twoState_noArbitrage
#print axioms LagrangeAcademy.Ch10.twoState_isComplete
#print axioms LagrangeAcademy.Ch10.threeState_noArbitrage
#print axioms LagrangeAcademy.Ch10.threeState_not_complete
#print axioms LagrangeAcademy.Ch10.threeStateExt_noArbitrage_quarter
#print axioms LagrangeAcademy.Ch10.threeStateExt_noArbitrage_alt
