/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec2
public import ThreeSumApsp.Sec3
public import ThreeSumApsp.Sec4
public import ThreeSumApsp.Sec5
public import ThreeSumApsp.Statements.Agreement
public import ThreeSumApsp.RunningTimes

/-!
# The propositions of `PaperStatements.lean` hold

Each theorem of this file says that a proposition of the namespace `PaperStatements` holds; the file
`PaperStatements.lean` beside `EndStatement.lean` defines these propositions. Its proof is the
theorem of the same name in the namespace `ThreeSumApsp`, which has the same statement written out.
The theorems on running times, `ThreeSumApsp.wordRam_theorem_5` and the others, are imported.
-/

public section

namespace PaperStatements

/-! ## Section 2: statements -/

theorem eq_1 : Eq_1 := @ThreeSumApsp.eq_1
theorem lemma_6 : Lemma_6 := @ThreeSumApsp.lemma_6
theorem figure_3 : Figure_3 := @ThreeSumApsp.figure_3
theorem lemma_7 : Lemma_7 := @ThreeSumApsp.lemma_7
theorem lemma_8 : Lemma_8 := @ThreeSumApsp.lemma_8
theorem figure_4 : Figure_4 := @ThreeSumApsp.figure_4
theorem lemma_9 : Lemma_9 := @ThreeSumApsp.lemma_9
theorem lemma_10 : Lemma_10 := @ThreeSumApsp.lemma_10
theorem sec2_card_contributing_of_order : Sec2_card_contributing_of_order :=
  @ThreeSumApsp.sec2_card_contributing_of_order
theorem sec2_card_outStr_of_leaf : Sec2_card_outStr_of_leaf :=
  @ThreeSumApsp.sec2_card_outStr_of_leaf
theorem eq_5_ratio : Eq_5_ratio := @ThreeSumApsp.eq_5_ratio
theorem eq_5_bound : Eq_5_bound := @ThreeSumApsp.eq_5_bound
theorem eq_5 : Eq_5 := @ThreeSumApsp.eq_5
theorem figure_6 : Figure_6 := @ThreeSumApsp.figure_6
theorem lemma_11 : Lemma_11 := @ThreeSumApsp.lemma_11
theorem eq_6 : Eq_6 := @ThreeSumApsp.eq_6

/-! ## Section 3: statements -/

theorem theorem_17_hashing_sum_sq_le : Theorem_17_hashing_sum_sq_le :=
  @ThreeSumApsp.theorem_17_hashing_sum_sq_le
theorem theorem_17_write_cost : Theorem_17_write_cost := @ThreeSumApsp.theorem_17_write_cost
theorem theorem_17_scanOrder_exists : Theorem_17_scanOrder_exists :=
  @ThreeSumApsp.theorem_17_scanOrder_exists
theorem theorem_17 : Theorem_17 := @ThreeSumApsp.theorem_17
theorem remark_18_block : Remark_18_block := @ThreeSumApsp.remark_18_block
theorem remark_20_balance : Remark_20_balance := @ThreeSumApsp.remark_20_balance
theorem remark_20_brute_force : Remark_20_brute_force := @ThreeSumApsp.remark_20_brute_force
theorem theorem_21b_repeated_squaring : Theorem_21b_repeated_squaring :=
  @ThreeSumApsp.theorem_21b_repeated_squaring
theorem theorem_21b_entries_bounded : Theorem_21b_entries_bounded :=
  @ThreeSumApsp.theorem_21b_entries_bounded
theorem theorem_21b_log_factors : Theorem_21b_log_factors := @ThreeSumApsp.theorem_21b_log_factors
theorem theorem_21b_negative_to_exact : Theorem_21b_negative_to_exact :=
  @ThreeSumApsp.theorem_21b_negative_to_exact
theorem theorem_21a_convolution_to_exact : Theorem_21a_convolution_to_exact :=
  @ThreeSumApsp.theorem_21a_convolution_to_exact
theorem theorem_21a_compose : Theorem_21a_compose := @ThreeSumApsp.theorem_21a_compose
theorem theorem_21a_threeSum_to_convolution : Theorem_21a_threeSum_to_convolution :=
  @ThreeSumApsp.theorem_21a_threeSum_to_convolution
theorem theorem_21a_threeSum_to_exact : Theorem_21a_threeSum_to_exact :=
  @ThreeSumApsp.theorem_21a_threeSum_to_exact

/-! ## Section 4: statements -/

theorem lemma_27 : Lemma_27 := @ThreeSumApsp.lemma_27
theorem lemma_28_leaves : Lemma_28_leaves := @ThreeSumApsp.lemma_28_leaves
theorem lemma_28_unique : Lemma_28_unique := @ThreeSumApsp.lemma_28_unique
theorem lemma_28 : Lemma_28 := @ThreeSumApsp.lemma_28
theorem lemma_28_counts : Lemma_28_counts := @ThreeSumApsp.lemma_28_counts
theorem lemma_28_boxes : Lemma_28_boxes := @ThreeSumApsp.lemma_28_boxes
theorem figure_10_counts : Figure_10_counts := @ThreeSumApsp.figure_10_counts
theorem figure_10_rows : Figure_10_rows := @ThreeSumApsp.figure_10_rows
theorem figure_10_Vof : Figure_10_Vof := @ThreeSumApsp.figure_10_Vof
theorem lemma_29_count : Lemma_29_count := @ThreeSumApsp.lemma_29_count
theorem lemma_29_values : Lemma_29_values := @ThreeSumApsp.lemma_29_values
theorem lemma_29_split : Lemma_29_split := @ThreeSumApsp.lemma_29_split
theorem sec4_rho_lt_one : Sec4_rho_lt_one := @ThreeSumApsp.sec4_rho_lt_one
theorem eq_7_ratio : Eq_7_ratio := @ThreeSumApsp.eq_7_ratio
theorem eq_7 : Eq_7 := @ThreeSumApsp.eq_7
theorem eq_10_corollary_26 : Eq_10_corollary_26 := @ThreeSumApsp.eq_10_corollary_26
theorem eq_10 : Eq_10 := @ThreeSumApsp.eq_10
theorem eq_11_iff : Eq_11_iff := @ThreeSumApsp.eq_11_iff
theorem corollary_31_gamma_pos : Corollary_31_gamma_pos := @ThreeSumApsp.corollary_31_gamma_pos
theorem sec4_Rc_strictAntiOn : Sec4_Rc_strictAntiOn := @ThreeSumApsp.sec4_Rc_strictAntiOn
theorem sec4_Rc_zero_tendsto : Sec4_Rc_zero_tendsto := @ThreeSumApsp.sec4_Rc_zero_tendsto
theorem sec4_epsStar_numeric : Sec4_epsStar_numeric := @ThreeSumApsp.sec4_epsStar_numeric
theorem sec4_Rc_lt_epsStar : Sec4_Rc_lt_epsStar := @ThreeSumApsp.sec4_Rc_lt_epsStar
theorem corollary_32_saving : Corollary_32_saving := @ThreeSumApsp.corollary_32_saving
theorem table_2_query_valid : Table_2_query_valid := @ThreeSumApsp.table_2_query_valid
theorem table_2_ninth_valid : Table_2_ninth_valid := @ThreeSumApsp.table_2_ninth_valid
theorem table_2_density_valid : Table_2_density_valid := @ThreeSumApsp.table_2_density_valid
theorem table_2_c40 : Table_2_c40 := @ThreeSumApsp.table_2_c40
theorem table_2_c21 : Table_2_c21 := @ThreeSumApsp.table_2_c21
theorem table_2_c19 : Table_2_c19 := @ThreeSumApsp.table_2_c19
theorem table_2_c15 : Table_2_c15 := @ThreeSumApsp.table_2_c15
theorem table_2_c12 : Table_2_c12 := @ThreeSumApsp.table_2_c12
theorem table_2_c10_5 : Table_2_c10_5 := @ThreeSumApsp.table_2_c10_5
theorem table_2_larger_c : Table_2_larger_c := @ThreeSumApsp.table_2_larger_c
theorem table_1_section_2_column : Table_1_section_2_column :=
  @ThreeSumApsp.table_1_section_2_column
theorem corollary_26_W : Corollary_26_W := @ThreeSumApsp.corollary_26_W

/-! ## Section 5: statements -/

theorem theorem_34_blocks : Theorem_34_blocks := @ThreeSumApsp.theorem_34_blocks
theorem theorem_34_entries : Theorem_34_entries := @ThreeSumApsp.theorem_34_entries
theorem theorem_34_total : Theorem_34_total := @ThreeSumApsp.theorem_34_total
theorem theorem_34_absorb : Theorem_34_absorb := @ThreeSumApsp.theorem_34_absorb
theorem lemma_36a_exact_triangle : Lemma_36a_exact_triangle :=
  @ThreeSumApsp.lemma_36a_exact_triangle
theorem lemma_36a_min_plus_below : Lemma_36a_min_plus_below :=
  @ThreeSumApsp.lemma_36a_min_plus_below
theorem lemma_36a_min_plus_successor : Lemma_36a_min_plus_successor :=
  @ThreeSumApsp.lemma_36a_min_plus_successor
theorem lemma_36a_min_plus_blocks : Lemma_36a_min_plus_blocks :=
  @ThreeSumApsp.lemma_36a_min_plus_blocks
theorem lemma_36a_count : Lemma_36a_count := @ThreeSumApsp.lemma_36a_count
theorem lemma_36a_valid : Lemma_36a_valid := @ThreeSumApsp.lemma_36a_valid
theorem lemma_36a_colors : Lemma_36a_colors := @ThreeSumApsp.lemma_36a_colors
theorem lemma_36a_pairs : Lemma_36a_pairs := @ThreeSumApsp.lemma_36a_pairs
theorem lemma_36a_subtractions : Lemma_36a_subtractions := @ThreeSumApsp.lemma_36a_subtractions
theorem lemma_36b_count : Lemma_36b_count := @ThreeSumApsp.lemma_36b_count
theorem lemma_36b_lists : Lemma_36b_lists := @ThreeSumApsp.lemma_36b_lists
theorem lemma_36b_subtractions : Lemma_36b_subtractions := @ThreeSumApsp.lemma_36b_subtractions
theorem lemma_37_order_exists : Lemma_37_order_exists := @ThreeSumApsp.lemma_37_order_exists
theorem lemma_37_index_exists : Lemma_37_index_exists := @ThreeSumApsp.lemma_37_index_exists
theorem lemma_37 : Lemma_37 := @ThreeSumApsp.lemma_37
theorem lemma_37_enumerated : Lemma_37_enumerated := @ThreeSumApsp.lemma_37_enumerated
theorem corollary_38_bound : Corollary_38_bound := @ThreeSumApsp.corollary_38_bound
theorem corollary_38_correct : Corollary_38_correct := @ThreeSumApsp.corollary_38_correct
theorem theorem_35_d : Theorem_35_d := @ThreeSumApsp.theorem_35_d
theorem theorem_35_counting_call : Theorem_35_counting_call :=
  @ThreeSumApsp.theorem_35_counting_call
theorem theorem_35_forming_lists : Theorem_35_forming_lists :=
  @ThreeSumApsp.theorem_35_forming_lists
theorem theorem_35_min_plus_total : Theorem_35_min_plus_total :=
  @ThreeSumApsp.theorem_35_min_plus_total
theorem theorem_35_further_time : Theorem_35_further_time := @ThreeSumApsp.theorem_35_further_time
theorem theorem_35_three_sum_count : Theorem_35_three_sum_count :=
  @ThreeSumApsp.theorem_35_three_sum_count
theorem theorem_35_three_sum_total : Theorem_35_three_sum_total :=
  @ThreeSumApsp.theorem_35_three_sum_total
theorem theorem_35_one_run : Theorem_35_one_run := @ThreeSumApsp.theorem_35_one_run
theorem theorem_35_restarts : Theorem_35_restarts := @ThreeSumApsp.theorem_35_restarts

/-! ## Agreement with the definitions of EndStatement.lean -/

theorem agreement_exactTriangle : Agreement_exactTriangle := @ThreeSumApsp.agreement_exactTriangle
theorem agreement_minPlusProduct : Agreement_minPlusProduct :=
  @ThreeSumApsp.agreement_minPlusProduct
theorem agreement_apsp_noNegativeCycle : Agreement_apsp_noNegativeCycle :=
  @ThreeSumApsp.agreement_apsp_noNegativeCycle
theorem agreement_apsp_output : Agreement_apsp_output := @ThreeSumApsp.agreement_apsp_output
theorem agreement_rowByRow : Agreement_rowByRow := @ThreeSumApsp.agreement_rowByRow
theorem agreement_cliqueWeight : Agreement_cliqueWeight := @ThreeSumApsp.agreement_cliqueWeight
theorem agreement_solves : Agreement_solves := @ThreeSumApsp.agreement_solves
theorem agreement_bigO : Agreement_bigO := @ThreeSumApsp.agreement_bigO
theorem agreement_solvedInTime : Agreement_solvedInTime := @ThreeSumApsp.agreement_solvedInTime

end PaperStatements
