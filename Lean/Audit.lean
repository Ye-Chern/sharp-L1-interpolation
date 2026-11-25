import SharpL1

#print axioms SharpL1.scaledNodeEval_spec
#print axioms SharpL1.natDegree_nodePolynomial
#print axioms SharpL1.nodePolynomial_ne_zero
#print axioms SharpL1.scaledNodeEval_sign_change
#print axioms SharpL1.roots_of_ordered_sign_change
#print axioms SharpL1.certified_node_roots
#print axioms SharpL1.Certificate.lowerUpdate_sound
#print axioms SharpL1.Certificate.upperUpdate_sound

/- Kernel-computation probe of the four sign checks on line 1 of
certificates/brackets.csv at 7b6380e (order 3, T = 2^31, scale 2^55). -/
open SharpL1 in
private theorem firstRowSigns :
    scaledNodeEval (2 ^ 55) 2147483648 29147909371969472 2 *
      scaledNodeEval (2 ^ 55) 2147483648 29147909372035008 2 < 0 ∧
    scaledNodeEval (2 ^ 55) 2147483648 11133511342679434 2 *
      scaledNodeEval (2 ^ 55) 2147483648 11133511342744970 2 < 0 ∧
    scaledNodeEval (2 ^ 55) 2147483648 (-11133509788811204) 2 *
      scaledNodeEval (2 ^ 55) 2147483648 (-11133509788745668) 2 < 0 ∧
    scaledNodeEval (2 ^ 55) 2147483648 (-29147908778485120) 2 *
      scaledNodeEval (2 ^ 55) 2147483648 (-29147908778419584) 2 < 0 := by decide

#print axioms firstRowSigns

#print axioms SharpL1.Certificate.cdfLower_sound
#print axioms SharpL1.Certificate.cdfUpper_sound
#print axioms SharpL1.Certificate.cdfToSign_encloses
#print axioms SharpL1.Certificate.checkRootRow_sound
#print axioms SharpL1.Certificate.checkOrder_sound
#print axioms SharpL1.Certificate.checkOrder_derivative_pos
#print axioms SharpL1.Certificate.origin_derivative_pos
#print axioms SharpL1.jacobi_charpoly
#print axioms SharpL1.jacobi_eigenspace_finrank_le_one
#print axioms SharpL1.nodePolynomial_roots_nodup
#print axioms SharpL1.jacobi_pencil_affine

#print axioms SharpL1.nodePolynomial_zero
#print axioms SharpL1.nodePolynomial_one
#print axioms SharpL1.nodePolynomial_neg_one
#print axioms SharpL1.nodePolynomial_roots_reflect
#print axioms SharpL1.Probability.exp_difference_product_tail
#print axioms SharpL1.Probability.prod_add_mul_exp_level_set_null
#print axioms SharpL1.Probability.exp_difference_law
#print axioms SharpL1.Probability.exp_difference_conv_cdf_zero
#print axioms SharpL1.Probability.expMeasure_one_map_mul
#print axioms SharpL1.Probability.measure_sum_mul_le_antitone_of_expMeasure
#print axioms SharpL1.Analysis.traceRatio_nat_ineq
#print axioms SharpL1.Analysis.gbound_sqrt_lt
#print axioms SharpL1.Analysis.exteriorWeight_alternating_nonneg
#print axioms SharpL1.Analysis.exterior_derivative_neg
#print axioms SharpL1.Analysis.center_min_of_deriv_and_outer

#print axioms SharpL1.Probability.lawSignMean_eq_cdf
#print axioms SharpL1.Analysis.center_min_of_checked_order
