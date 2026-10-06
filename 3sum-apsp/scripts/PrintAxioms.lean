/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Written by scripts/generate.py.  Prints the axioms behind every theorem that Comparator compares:
    lake build Solution && lake env lean scripts/PrintAxioms.lean
No line of the output names an axiom other than propext, Classical.choice and Quot.sound.
This is a convenience for a reader, and not a check of files that one does not trust, because the command runs
inside Lean with the library imported.  Comparator does not depend on that.
-/
import Solution.EndStatement
import Solution.PaperStatements

-- EndStatement
#print axioms ThreeSumApsp.endStatement_theorem_19
#print axioms ThreeSumApsp.endStatement_theorem_22_3SUM
#print axioms ThreeSumApsp.endStatement_theorem_22_MinPlus
#print axioms ThreeSumApsp.endStatement_theorem_22_APSP
#print axioms ThreeSumApsp.endStatement_corollary_39_zeroWeight

-- PaperStatements
#print axioms PaperStatements.eq_1
#print axioms PaperStatements.lemma_6
#print axioms PaperStatements.figure_3
#print axioms PaperStatements.lemma_7
#print axioms PaperStatements.lemma_8
#print axioms PaperStatements.figure_4
#print axioms PaperStatements.lemma_9
#print axioms PaperStatements.lemma_10
#print axioms PaperStatements.sec2_card_contributing_of_order
#print axioms PaperStatements.sec2_card_outStr_of_leaf
#print axioms PaperStatements.eq_5_ratio
#print axioms PaperStatements.eq_5_bound
#print axioms PaperStatements.eq_5
#print axioms PaperStatements.figure_6
#print axioms PaperStatements.lemma_11
#print axioms PaperStatements.eq_6
#print axioms PaperStatements.theorem_17_hashing_sum_sq_le
#print axioms PaperStatements.theorem_17_write_cost
#print axioms PaperStatements.theorem_17_scanOrder_exists
#print axioms PaperStatements.theorem_17
#print axioms PaperStatements.remark_18_block
#print axioms PaperStatements.remark_20_balance
#print axioms PaperStatements.remark_20_brute_force
#print axioms PaperStatements.theorem_21b_repeated_squaring
#print axioms PaperStatements.theorem_21b_entries_bounded
#print axioms PaperStatements.theorem_21b_log_factors
#print axioms PaperStatements.theorem_21b_negative_to_exact
#print axioms PaperStatements.theorem_21a_convolution_to_exact
#print axioms PaperStatements.theorem_21a_compose
#print axioms PaperStatements.theorem_21a_threeSum_to_convolution
#print axioms PaperStatements.theorem_21a_threeSum_to_exact
#print axioms PaperStatements.lemma_27
#print axioms PaperStatements.lemma_28_leaves
#print axioms PaperStatements.lemma_28_unique
#print axioms PaperStatements.lemma_28
#print axioms PaperStatements.lemma_28_counts
#print axioms PaperStatements.lemma_28_boxes
#print axioms PaperStatements.figure_10_counts
#print axioms PaperStatements.figure_10_rows
#print axioms PaperStatements.figure_10_Vof
#print axioms PaperStatements.lemma_29_count
#print axioms PaperStatements.lemma_29_values
#print axioms PaperStatements.lemma_29_split
#print axioms PaperStatements.sec4_rho_lt_one
#print axioms PaperStatements.eq_7_ratio
#print axioms PaperStatements.eq_7
#print axioms PaperStatements.eq_10_corollary_26
#print axioms PaperStatements.eq_10
#print axioms PaperStatements.eq_11_iff
#print axioms PaperStatements.corollary_31_gamma_pos
#print axioms PaperStatements.sec4_Rc_strictAntiOn
#print axioms PaperStatements.sec4_Rc_zero_tendsto
#print axioms PaperStatements.sec4_epsStar_numeric
#print axioms PaperStatements.sec4_Rc_lt_epsStar
#print axioms PaperStatements.corollary_32_saving
#print axioms PaperStatements.table_2_query_valid
#print axioms PaperStatements.table_2_ninth_valid
#print axioms PaperStatements.table_2_density_valid
#print axioms PaperStatements.table_2_c40
#print axioms PaperStatements.table_2_c21
#print axioms PaperStatements.table_2_c19
#print axioms PaperStatements.table_2_c15
#print axioms PaperStatements.table_2_c12
#print axioms PaperStatements.table_2_c10_5
#print axioms PaperStatements.table_2_larger_c
#print axioms PaperStatements.table_1_section_2_column
#print axioms PaperStatements.corollary_26_W
#print axioms PaperStatements.theorem_34_blocks
#print axioms PaperStatements.theorem_34_entries
#print axioms PaperStatements.theorem_34_total
#print axioms PaperStatements.theorem_34_absorb
#print axioms PaperStatements.lemma_36a_exact_triangle
#print axioms PaperStatements.lemma_36a_min_plus_below
#print axioms PaperStatements.lemma_36a_min_plus_successor
#print axioms PaperStatements.lemma_36a_min_plus_blocks
#print axioms PaperStatements.lemma_36a_count
#print axioms PaperStatements.lemma_36a_valid
#print axioms PaperStatements.lemma_36a_colors
#print axioms PaperStatements.lemma_36a_pairs
#print axioms PaperStatements.lemma_36a_subtractions
#print axioms PaperStatements.lemma_36b_count
#print axioms PaperStatements.lemma_36b_lists
#print axioms PaperStatements.lemma_36b_subtractions
#print axioms PaperStatements.lemma_37_order_exists
#print axioms PaperStatements.lemma_37_index_exists
#print axioms PaperStatements.lemma_37
#print axioms PaperStatements.lemma_37_enumerated
#print axioms PaperStatements.corollary_38_bound
#print axioms PaperStatements.corollary_38_correct
#print axioms PaperStatements.theorem_35_d
#print axioms PaperStatements.theorem_35_counting_call
#print axioms PaperStatements.theorem_35_forming_lists
#print axioms PaperStatements.theorem_35_min_plus_total
#print axioms PaperStatements.theorem_35_further_time
#print axioms PaperStatements.theorem_35_three_sum_count
#print axioms PaperStatements.theorem_35_three_sum_total
#print axioms PaperStatements.theorem_35_one_run
#print axioms PaperStatements.theorem_35_restarts
#print axioms PaperStatements.agreement_exactTriangle
#print axioms PaperStatements.agreement_minPlusProduct
#print axioms PaperStatements.agreement_apsp_noNegativeCycle
#print axioms PaperStatements.agreement_apsp_output
#print axioms PaperStatements.agreement_rowByRow
#print axioms PaperStatements.agreement_cliqueWeight
#print axioms PaperStatements.agreement_solves
#print axioms PaperStatements.agreement_bigO
#print axioms PaperStatements.agreement_solvedInTime
#print axioms ThreeSumApsp.wordRam_theorem_5
#print axioms ThreeSumApsp.wordRam_corollary_15
#print axioms ThreeSumApsp.wordRam_corollary_16
#print axioms ThreeSumApsp.wordRam_theorem_19
#print axioms ThreeSumApsp.wordRam_theorem_22_first
#print axioms ThreeSumApsp.wordRam_theorem_22_second
#print axioms ThreeSumApsp.wordRam_theorem_22_threeSum
#print axioms ThreeSumApsp.wordRam_theorem_24
#print axioms ThreeSumApsp.wordRam_theorem_25
#print axioms ThreeSumApsp.wordRam_corollary_26
#print axioms ThreeSumApsp.wordRam_corollary_26_wanted
#print axioms ThreeSumApsp.wordRam_theorem_30
#print axioms ThreeSumApsp.wordRam_theorem_30_wanted
#print axioms ThreeSumApsp.wordRam_corollary_31
#print axioms ThreeSumApsp.wordRam_corollary_32
#print axioms ThreeSumApsp.wordRam_corollary_39_zero
#print axioms ThreeSumApsp.wordRam_corollary_39_min_max
#print axioms ThreeSumApsp.wordRam_corollary_40_times
#print axioms ThreeSumApsp.wordRam_corollary_40_general_times
#print axioms ThreeSumApsp.wordRam_corollary_40_fail
#print axioms ThreeSumApsp.wordRam_theorem_1
#print axioms ThreeSumApsp.wordRam_theorem_2
#print axioms ThreeSumApsp.wordRam_theorem_2_graphs
#print axioms ThreeSumApsp.wordRam_theorem_3
#print axioms ThreeSumApsp.wordRam_theorem_4
