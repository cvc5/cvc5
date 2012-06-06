(benchmark no_init_multi_delete14.smt
  :source {
The benchmarks come from Bounded Model Checking of software.
Contributed by Lorenzo Platania (c1009@unige.it).
}
  :status unknown
  :difficulty { unknown }
  :category { industrial }
  :logic QF_AUFBV
  :extrafuns ((main_0_head_0 BitVec[32]))
  :extrafuns ((main_0_head_1 BitVec[32]))
  :assumption
(= main_0_head_1 bv0[32])
  :extrafuns ((arr_val_0 Array[32:32]))
  :extrafuns ((arr_val_1 Array[32:32]))
  :assumption
(= arr_val_1 (store arr_val_0 main_0_head_1 bv0[32]))
  :extrafuns ((arr_next_0 Array[32:32]))
  :extrafuns ((arr_next_1 Array[32:32]))
  :assumption
(= arr_next_1 (store arr_next_0 main_0_head_1 (bvneg bv1[32])))
  :extrafuns ((main_0_curr_0 BitVec[32]))
  :extrafuns ((main_0_curr_1 BitVec[32]))
  :assumption
(= main_0_curr_1 main_0_head_1)
  :extrafuns ((main_0_i_0 BitVec[32]))
  :extrafuns ((main_0_i_1 BitVec[32]))
  :assumption
(= main_0_i_1 bv1[32])
  :extrafuns ((main_0_tmp_0 BitVec[32]))
  :extrafuns ((main_0_tmp_1 BitVec[32]))
  :assumption
(= main_0_tmp_1 (ite (bvult main_0_i_1 bv13[32]) bv1[32] main_0_tmp_0))
  :extrafuns ((arr_val_2 Array[32:32]))
  :assumption
(= arr_val_2 (ite (bvult main_0_i_1 bv13[32]) (store arr_val_1 main_0_tmp_1 main_0_i_1) arr_val_1))
  :extrafuns ((arr_next_2 Array[32:32]))
  :assumption
(= arr_next_2 (ite (bvult main_0_i_1 bv13[32]) (store arr_next_1 main_0_curr_1 main_0_tmp_1) arr_next_1))
  :extrafuns ((main_0_curr_2 BitVec[32]))
  :assumption
(= main_0_curr_2 (ite (bvult main_0_i_1 bv13[32]) (select arr_next_2 main_0_curr_1) main_0_curr_1))
  :extrafuns ((arr_next_3 Array[32:32]))
  :assumption
(= arr_next_3 (ite (bvult main_0_i_1 bv13[32]) (store arr_next_2 main_0_tmp_1 (bvneg bv1[32])) arr_next_2))
  :extrafuns ((main_0_temp_i_0 BitVec[32]))
  :extrafuns ((main_0_temp_i_1 BitVec[32]))
  :assumption
(= main_0_temp_i_1 (ite (bvult main_0_i_1 bv13[32]) main_0_i_1 main_0_temp_i_0))
  :extrafuns ((main_0_i_2 BitVec[32]))
  :assumption
(= main_0_i_2 (ite (bvult main_0_i_1 bv13[32]) (bvadd main_0_i_1 bv1[32]) main_0_i_1))
  :extrafuns ((main_0_tmp_2 BitVec[32]))
  :assumption
(= main_0_tmp_2 (ite (bvult main_0_i_2 bv13[32]) bv2[32] main_0_tmp_1))
  :extrafuns ((arr_val_3 Array[32:32]))
  :assumption
(= arr_val_3 (ite (bvult main_0_i_2 bv13[32]) (store arr_val_2 main_0_tmp_2 main_0_i_2) arr_val_2))
  :extrafuns ((arr_next_4 Array[32:32]))
  :assumption
(= arr_next_4 (ite (bvult main_0_i_2 bv13[32]) (store arr_next_3 main_0_curr_2 main_0_tmp_2) arr_next_3))
  :extrafuns ((main_0_curr_3 BitVec[32]))
  :assumption
(= main_0_curr_3 (ite (bvult main_0_i_2 bv13[32]) (select arr_next_4 main_0_curr_2) main_0_curr_2))
  :extrafuns ((arr_next_5 Array[32:32]))
  :assumption
(= arr_next_5 (ite (bvult main_0_i_2 bv13[32]) (store arr_next_4 main_0_tmp_2 (bvneg bv1[32])) arr_next_4))
  :extrafuns ((main_0_temp_i_2 BitVec[32]))
  :assumption
(= main_0_temp_i_2 (ite (bvult main_0_i_2 bv13[32]) main_0_i_2 main_0_temp_i_1))
  :extrafuns ((main_0_i_3 BitVec[32]))
  :assumption
(= main_0_i_3 (ite (bvult main_0_i_2 bv13[32]) (bvadd main_0_i_2 bv1[32]) main_0_i_2))
  :extrafuns ((main_0_tmp_3 BitVec[32]))
  :assumption
(= main_0_tmp_3 (ite (bvult main_0_i_3 bv13[32]) bv3[32] main_0_tmp_2))
  :extrafuns ((arr_val_4 Array[32:32]))
  :assumption
(= arr_val_4 (ite (bvult main_0_i_3 bv13[32]) (store arr_val_3 main_0_tmp_3 main_0_i_3) arr_val_3))
  :extrafuns ((arr_next_6 Array[32:32]))
  :assumption
(= arr_next_6 (ite (bvult main_0_i_3 bv13[32]) (store arr_next_5 main_0_curr_3 main_0_tmp_3) arr_next_5))
  :extrafuns ((main_0_curr_4 BitVec[32]))
  :assumption
(= main_0_curr_4 (ite (bvult main_0_i_3 bv13[32]) (select arr_next_6 main_0_curr_3) main_0_curr_3))
  :extrafuns ((arr_next_7 Array[32:32]))
  :assumption
(= arr_next_7 (ite (bvult main_0_i_3 bv13[32]) (store arr_next_6 main_0_tmp_3 (bvneg bv1[32])) arr_next_6))
  :extrafuns ((main_0_temp_i_3 BitVec[32]))
  :assumption
(= main_0_temp_i_3 (ite (bvult main_0_i_3 bv13[32]) main_0_i_3 main_0_temp_i_2))
  :extrafuns ((main_0_i_4 BitVec[32]))
  :assumption
(= main_0_i_4 (ite (bvult main_0_i_3 bv13[32]) (bvadd main_0_i_3 bv1[32]) main_0_i_3))
  :extrafuns ((main_0_tmp_4 BitVec[32]))
  :assumption
(= main_0_tmp_4 (ite (bvult main_0_i_4 bv13[32]) bv4[32] main_0_tmp_3))
  :extrafuns ((arr_val_5 Array[32:32]))
  :assumption
(= arr_val_5 (ite (bvult main_0_i_4 bv13[32]) (store arr_val_4 main_0_tmp_4 main_0_i_4) arr_val_4))
  :extrafuns ((arr_next_8 Array[32:32]))
  :assumption
(= arr_next_8 (ite (bvult main_0_i_4 bv13[32]) (store arr_next_7 main_0_curr_4 main_0_tmp_4) arr_next_7))
  :extrafuns ((main_0_curr_5 BitVec[32]))
  :assumption
(= main_0_curr_5 (ite (bvult main_0_i_4 bv13[32]) (select arr_next_8 main_0_curr_4) main_0_curr_4))
  :extrafuns ((arr_next_9 Array[32:32]))
  :assumption
(= arr_next_9 (ite (bvult main_0_i_4 bv13[32]) (store arr_next_8 main_0_tmp_4 (bvneg bv1[32])) arr_next_8))
  :extrafuns ((main_0_temp_i_4 BitVec[32]))
  :assumption
(= main_0_temp_i_4 (ite (bvult main_0_i_4 bv13[32]) main_0_i_4 main_0_temp_i_3))
  :extrafuns ((main_0_i_5 BitVec[32]))
  :assumption
(= main_0_i_5 (ite (bvult main_0_i_4 bv13[32]) (bvadd main_0_i_4 bv1[32]) main_0_i_4))
  :extrafuns ((main_0_tmp_5 BitVec[32]))
  :assumption
(= main_0_tmp_5 (ite (bvult main_0_i_5 bv13[32]) bv5[32] main_0_tmp_4))
  :extrafuns ((arr_val_6 Array[32:32]))
  :assumption
(= arr_val_6 (ite (bvult main_0_i_5 bv13[32]) (store arr_val_5 main_0_tmp_5 main_0_i_5) arr_val_5))
  :extrafuns ((arr_next_10 Array[32:32]))
  :assumption
(= arr_next_10 (ite (bvult main_0_i_5 bv13[32]) (store arr_next_9 main_0_curr_5 main_0_tmp_5) arr_next_9))
  :extrafuns ((main_0_curr_6 BitVec[32]))
  :assumption
(= main_0_curr_6 (ite (bvult main_0_i_5 bv13[32]) (select arr_next_10 main_0_curr_5) main_0_curr_5))
  :extrafuns ((arr_next_11 Array[32:32]))
  :assumption
(= arr_next_11 (ite (bvult main_0_i_5 bv13[32]) (store arr_next_10 main_0_tmp_5 (bvneg bv1[32])) arr_next_10))
  :extrafuns ((main_0_temp_i_5 BitVec[32]))
  :assumption
(= main_0_temp_i_5 (ite (bvult main_0_i_5 bv13[32]) main_0_i_5 main_0_temp_i_4))
  :extrafuns ((main_0_i_6 BitVec[32]))
  :assumption
(= main_0_i_6 (ite (bvult main_0_i_5 bv13[32]) (bvadd main_0_i_5 bv1[32]) main_0_i_5))
  :extrafuns ((main_0_tmp_6 BitVec[32]))
  :assumption
(= main_0_tmp_6 (ite (bvult main_0_i_6 bv13[32]) bv6[32] main_0_tmp_5))
  :extrafuns ((arr_val_7 Array[32:32]))
  :assumption
(= arr_val_7 (ite (bvult main_0_i_6 bv13[32]) (store arr_val_6 main_0_tmp_6 main_0_i_6) arr_val_6))
  :extrafuns ((arr_next_12 Array[32:32]))
  :assumption
(= arr_next_12 (ite (bvult main_0_i_6 bv13[32]) (store arr_next_11 main_0_curr_6 main_0_tmp_6) arr_next_11))
  :extrafuns ((main_0_curr_7 BitVec[32]))
  :assumption
(= main_0_curr_7 (ite (bvult main_0_i_6 bv13[32]) (select arr_next_12 main_0_curr_6) main_0_curr_6))
  :extrafuns ((arr_next_13 Array[32:32]))
  :assumption
(= arr_next_13 (ite (bvult main_0_i_6 bv13[32]) (store arr_next_12 main_0_tmp_6 (bvneg bv1[32])) arr_next_12))
  :extrafuns ((main_0_temp_i_6 BitVec[32]))
  :assumption
(= main_0_temp_i_6 (ite (bvult main_0_i_6 bv13[32]) main_0_i_6 main_0_temp_i_5))
  :extrafuns ((main_0_i_7 BitVec[32]))
  :assumption
(= main_0_i_7 (ite (bvult main_0_i_6 bv13[32]) (bvadd main_0_i_6 bv1[32]) main_0_i_6))
  :extrafuns ((main_0_tmp_7 BitVec[32]))
  :assumption
(= main_0_tmp_7 (ite (bvult main_0_i_7 bv13[32]) bv7[32] main_0_tmp_6))
  :extrafuns ((arr_val_8 Array[32:32]))
  :assumption
(= arr_val_8 (ite (bvult main_0_i_7 bv13[32]) (store arr_val_7 main_0_tmp_7 main_0_i_7) arr_val_7))
  :extrafuns ((arr_next_14 Array[32:32]))
  :assumption
(= arr_next_14 (ite (bvult main_0_i_7 bv13[32]) (store arr_next_13 main_0_curr_7 main_0_tmp_7) arr_next_13))
  :extrafuns ((main_0_curr_8 BitVec[32]))
  :assumption
(= main_0_curr_8 (ite (bvult main_0_i_7 bv13[32]) (select arr_next_14 main_0_curr_7) main_0_curr_7))
  :extrafuns ((arr_next_15 Array[32:32]))
  :assumption
(= arr_next_15 (ite (bvult main_0_i_7 bv13[32]) (store arr_next_14 main_0_tmp_7 (bvneg bv1[32])) arr_next_14))
  :extrafuns ((main_0_temp_i_7 BitVec[32]))
  :assumption
(= main_0_temp_i_7 (ite (bvult main_0_i_7 bv13[32]) main_0_i_7 main_0_temp_i_6))
  :extrafuns ((main_0_i_8 BitVec[32]))
  :assumption
(= main_0_i_8 (ite (bvult main_0_i_7 bv13[32]) (bvadd main_0_i_7 bv1[32]) main_0_i_7))
  :extrafuns ((main_0_tmp_8 BitVec[32]))
  :assumption
(= main_0_tmp_8 (ite (bvult main_0_i_8 bv13[32]) bv8[32] main_0_tmp_7))
  :extrafuns ((arr_val_9 Array[32:32]))
  :assumption
(= arr_val_9 (ite (bvult main_0_i_8 bv13[32]) (store arr_val_8 main_0_tmp_8 main_0_i_8) arr_val_8))
  :extrafuns ((arr_next_16 Array[32:32]))
  :assumption
(= arr_next_16 (ite (bvult main_0_i_8 bv13[32]) (store arr_next_15 main_0_curr_8 main_0_tmp_8) arr_next_15))
  :extrafuns ((main_0_curr_9 BitVec[32]))
  :assumption
(= main_0_curr_9 (ite (bvult main_0_i_8 bv13[32]) (select arr_next_16 main_0_curr_8) main_0_curr_8))
  :extrafuns ((arr_next_17 Array[32:32]))
  :assumption
(= arr_next_17 (ite (bvult main_0_i_8 bv13[32]) (store arr_next_16 main_0_tmp_8 (bvneg bv1[32])) arr_next_16))
  :extrafuns ((main_0_temp_i_8 BitVec[32]))
  :assumption
(= main_0_temp_i_8 (ite (bvult main_0_i_8 bv13[32]) main_0_i_8 main_0_temp_i_7))
  :extrafuns ((main_0_i_9 BitVec[32]))
  :assumption
(= main_0_i_9 (ite (bvult main_0_i_8 bv13[32]) (bvadd main_0_i_8 bv1[32]) main_0_i_8))
  :extrafuns ((main_0_tmp_9 BitVec[32]))
  :assumption
(= main_0_tmp_9 (ite (bvult main_0_i_9 bv13[32]) bv9[32] main_0_tmp_8))
  :extrafuns ((arr_val_10 Array[32:32]))
  :assumption
(= arr_val_10 (ite (bvult main_0_i_9 bv13[32]) (store arr_val_9 main_0_tmp_9 main_0_i_9) arr_val_9))
  :extrafuns ((arr_next_18 Array[32:32]))
  :assumption
(= arr_next_18 (ite (bvult main_0_i_9 bv13[32]) (store arr_next_17 main_0_curr_9 main_0_tmp_9) arr_next_17))
  :extrafuns ((main_0_curr_10 BitVec[32]))
  :assumption
(= main_0_curr_10 (ite (bvult main_0_i_9 bv13[32]) (select arr_next_18 main_0_curr_9) main_0_curr_9))
  :extrafuns ((arr_next_19 Array[32:32]))
  :assumption
(= arr_next_19 (ite (bvult main_0_i_9 bv13[32]) (store arr_next_18 main_0_tmp_9 (bvneg bv1[32])) arr_next_18))
  :extrafuns ((main_0_temp_i_9 BitVec[32]))
  :assumption
(= main_0_temp_i_9 (ite (bvult main_0_i_9 bv13[32]) main_0_i_9 main_0_temp_i_8))
  :extrafuns ((main_0_i_10 BitVec[32]))
  :assumption
(= main_0_i_10 (ite (bvult main_0_i_9 bv13[32]) (bvadd main_0_i_9 bv1[32]) main_0_i_9))
  :extrafuns ((main_0_tmp_10 BitVec[32]))
  :assumption
(= main_0_tmp_10 (ite (bvult main_0_i_10 bv13[32]) bv10[32] main_0_tmp_9))
  :extrafuns ((arr_val_11 Array[32:32]))
  :assumption
(= arr_val_11 (ite (bvult main_0_i_10 bv13[32]) (store arr_val_10 main_0_tmp_10 main_0_i_10) arr_val_10))
  :extrafuns ((arr_next_20 Array[32:32]))
  :assumption
(= arr_next_20 (ite (bvult main_0_i_10 bv13[32]) (store arr_next_19 main_0_curr_10 main_0_tmp_10) arr_next_19))
  :extrafuns ((main_0_curr_11 BitVec[32]))
  :assumption
(= main_0_curr_11 (ite (bvult main_0_i_10 bv13[32]) (select arr_next_20 main_0_curr_10) main_0_curr_10))
  :extrafuns ((arr_next_21 Array[32:32]))
  :assumption
(= arr_next_21 (ite (bvult main_0_i_10 bv13[32]) (store arr_next_20 main_0_tmp_10 (bvneg bv1[32])) arr_next_20))
  :extrafuns ((main_0_temp_i_10 BitVec[32]))
  :assumption
(= main_0_temp_i_10 (ite (bvult main_0_i_10 bv13[32]) main_0_i_10 main_0_temp_i_9))
  :extrafuns ((main_0_i_11 BitVec[32]))
  :assumption
(= main_0_i_11 (ite (bvult main_0_i_10 bv13[32]) (bvadd main_0_i_10 bv1[32]) main_0_i_10))
  :extrafuns ((main_0_tmp_11 BitVec[32]))
  :assumption
(= main_0_tmp_11 (ite (bvult main_0_i_11 bv13[32]) bv11[32] main_0_tmp_10))
  :extrafuns ((arr_val_12 Array[32:32]))
  :assumption
(= arr_val_12 (ite (bvult main_0_i_11 bv13[32]) (store arr_val_11 main_0_tmp_11 main_0_i_11) arr_val_11))
  :extrafuns ((arr_next_22 Array[32:32]))
  :assumption
(= arr_next_22 (ite (bvult main_0_i_11 bv13[32]) (store arr_next_21 main_0_curr_11 main_0_tmp_11) arr_next_21))
  :extrafuns ((main_0_curr_12 BitVec[32]))
  :assumption
(= main_0_curr_12 (ite (bvult main_0_i_11 bv13[32]) (select arr_next_22 main_0_curr_11) main_0_curr_11))
  :extrafuns ((arr_next_23 Array[32:32]))
  :assumption
(= arr_next_23 (ite (bvult main_0_i_11 bv13[32]) (store arr_next_22 main_0_tmp_11 (bvneg bv1[32])) arr_next_22))
  :extrafuns ((main_0_temp_i_11 BitVec[32]))
  :assumption
(= main_0_temp_i_11 (ite (bvult main_0_i_11 bv13[32]) main_0_i_11 main_0_temp_i_10))
  :extrafuns ((main_0_i_12 BitVec[32]))
  :assumption
(= main_0_i_12 (ite (bvult main_0_i_11 bv13[32]) (bvadd main_0_i_11 bv1[32]) main_0_i_11))
  :extrafuns ((main_0_tmp_12 BitVec[32]))
  :assumption
(= main_0_tmp_12 (ite (bvult main_0_i_12 bv13[32]) bv12[32] main_0_tmp_11))
  :extrafuns ((arr_val_13 Array[32:32]))
  :assumption
(= arr_val_13 (ite (bvult main_0_i_12 bv13[32]) (store arr_val_12 main_0_tmp_12 main_0_i_12) arr_val_12))
  :extrafuns ((arr_next_24 Array[32:32]))
  :assumption
(= arr_next_24 (ite (bvult main_0_i_12 bv13[32]) (store arr_next_23 main_0_curr_12 main_0_tmp_12) arr_next_23))
  :extrafuns ((main_0_curr_13 BitVec[32]))
  :assumption
(= main_0_curr_13 (ite (bvult main_0_i_12 bv13[32]) (select arr_next_24 main_0_curr_12) main_0_curr_12))
  :extrafuns ((arr_next_25 Array[32:32]))
  :assumption
(= arr_next_25 (ite (bvult main_0_i_12 bv13[32]) (store arr_next_24 main_0_tmp_12 (bvneg bv1[32])) arr_next_24))
  :extrafuns ((main_0_temp_i_12 BitVec[32]))
  :assumption
(= main_0_temp_i_12 (ite (bvult main_0_i_12 bv13[32]) main_0_i_12 main_0_temp_i_11))
  :extrafuns ((main_0_i_13 BitVec[32]))
  :assumption
(= main_0_i_13 (ite (bvult main_0_i_12 bv13[32]) (bvadd main_0_i_12 bv1[32]) main_0_i_12))
  :extrafuns ((main_0_tmp_13 BitVec[32]))
  :assumption
(= main_0_tmp_13 (ite (bvult main_0_i_13 bv13[32]) bv13[32] main_0_tmp_12))
  :extrafuns ((arr_val_14 Array[32:32]))
  :assumption
(= arr_val_14 (ite (bvult main_0_i_13 bv13[32]) (store arr_val_13 main_0_tmp_13 main_0_i_13) arr_val_13))
  :extrafuns ((arr_next_26 Array[32:32]))
  :assumption
(= arr_next_26 (ite (bvult main_0_i_13 bv13[32]) (store arr_next_25 main_0_curr_13 main_0_tmp_13) arr_next_25))
  :extrafuns ((main_0_curr_14 BitVec[32]))
  :assumption
(= main_0_curr_14 (ite (bvult main_0_i_13 bv13[32]) (select arr_next_26 main_0_curr_13) main_0_curr_13))
  :extrafuns ((arr_next_27 Array[32:32]))
  :assumption
(= arr_next_27 (ite (bvult main_0_i_13 bv13[32]) (store arr_next_26 main_0_tmp_13 (bvneg bv1[32])) arr_next_26))
  :extrafuns ((main_0_temp_i_13 BitVec[32]))
  :assumption
(= main_0_temp_i_13 (ite (bvult main_0_i_13 bv13[32]) main_0_i_13 main_0_temp_i_12))
  :extrafuns ((main_0_i_14 BitVec[32]))
  :assumption
(= main_0_i_14 (ite (bvult main_0_i_13 bv13[32]) (bvadd main_0_i_13 bv1[32]) main_0_i_13))
  :extrafuns ((main_0_tmp_14 BitVec[32]))
  :assumption
(= main_0_tmp_14 (ite (bvult main_0_i_14 bv13[32]) bv14[32] main_0_tmp_13))
  :extrafuns ((arr_val_15 Array[32:32]))
  :assumption
(= arr_val_15 (ite (bvult main_0_i_14 bv13[32]) (store arr_val_14 main_0_tmp_14 main_0_i_14) arr_val_14))
  :extrafuns ((arr_next_28 Array[32:32]))
  :assumption
(= arr_next_28 (ite (bvult main_0_i_14 bv13[32]) (store arr_next_27 main_0_curr_14 main_0_tmp_14) arr_next_27))
  :extrafuns ((main_0_curr_15 BitVec[32]))
  :assumption
(= main_0_curr_15 (ite (bvult main_0_i_14 bv13[32]) (select arr_next_28 main_0_curr_14) main_0_curr_14))
  :extrafuns ((arr_next_29 Array[32:32]))
  :assumption
(= arr_next_29 (ite (bvult main_0_i_14 bv13[32]) (store arr_next_28 main_0_tmp_14 (bvneg bv1[32])) arr_next_28))
  :extrafuns ((main_0_temp_i_14 BitVec[32]))
  :assumption
(= main_0_temp_i_14 (ite (bvult main_0_i_14 bv13[32]) main_0_i_14 main_0_temp_i_13))
  :extrafuns ((main_0_i_15 BitVec[32]))
  :assumption
(= main_0_i_15 (ite (bvult main_0_i_14 bv13[32]) (bvadd main_0_i_14 bv1[32]) main_0_i_14))
  :extrafuns ((undefInt_1 BitVec[32]))
  :extrafuns ((delete_0_val_0 BitVec[32]))
  :extrafuns ((delete_0_val_1 BitVec[32]))
  :assumption
(= delete_0_val_1 undefInt_1)
  :extrafuns ((delete_0_list_0 BitVec[32]))
  :extrafuns ((delete_0_list_1 BitVec[32]))
  :assumption
(= delete_0_list_1 main_0_head_1)
  :extrafuns ((delete_0_head_0 BitVec[32]))
  :extrafuns ((delete_0_head_1 BitVec[32]))
  :assumption
(= delete_0_head_1 delete_0_list_1)
  :extrafuns ((delete_0_head_2 BitVec[32]))
  :assumption
(let (?cvc_0 (select arr_next_29 delete_0_head_1)) (= delete_0_head_2 (ite (and (= (select arr_val_15 delete_0_head_1) delete_0_val_1) (not (= ?cvc_0 (bvneg bv1[32])))) ?cvc_0 delete_0_head_1)))
  :extrafuns ((delete_0_head_3 BitVec[32]))
  :assumption
(= delete_0_head_3 (ite (and (= (select arr_val_15 delete_0_head_2) delete_0_val_1) (not (= (select arr_next_29 delete_0_head_1) (bvneg bv1[32])))) (select arr_next_29 delete_0_head_2) delete_0_head_2))
  :extrafuns ((delete_0_head_4 BitVec[32]))
  :assumption
(= delete_0_head_4 (ite (and (= (select arr_val_15 delete_0_head_3) delete_0_val_1) (not (= (select arr_next_29 delete_0_head_1) (bvneg bv1[32])))) (select arr_next_29 delete_0_head_3) delete_0_head_3))
  :extrafuns ((delete_0_head_5 BitVec[32]))
  :assumption
(= delete_0_head_5 (ite (and (= (select arr_val_15 delete_0_head_4) delete_0_val_1) (not (= (select arr_next_29 delete_0_head_1) (bvneg bv1[32])))) (select arr_next_29 delete_0_head_4) delete_0_head_4))
  :extrafuns ((delete_0_head_6 BitVec[32]))
  :assumption
(= delete_0_head_6 (ite (and (= (select arr_val_15 delete_0_head_5) delete_0_val_1) (not (= (select arr_next_29 delete_0_head_1) (bvneg bv1[32])))) (select arr_next_29 delete_0_head_5) delete_0_head_5))
  :extrafuns ((delete_0_head_7 BitVec[32]))
  :assumption
(= delete_0_head_7 (ite (and (= (select arr_val_15 delete_0_head_6) delete_0_val_1) (not (= (select arr_next_29 delete_0_head_1) (bvneg bv1[32])))) (select arr_next_29 delete_0_head_6) delete_0_head_6))
  :extrafuns ((delete_0_head_8 BitVec[32]))
  :assumption
(= delete_0_head_8 (ite (and (= (select arr_val_15 delete_0_head_7) delete_0_val_1) (not (= (select arr_next_29 delete_0_head_1) (bvneg bv1[32])))) (select arr_next_29 delete_0_head_7) delete_0_head_7))
  :extrafuns ((delete_0_head_9 BitVec[32]))
  :assumption
(= delete_0_head_9 (ite (and (= (select arr_val_15 delete_0_head_8) delete_0_val_1) (not (= (select arr_next_29 delete_0_head_1) (bvneg bv1[32])))) (select arr_next_29 delete_0_head_8) delete_0_head_8))
  :extrafuns ((delete_0_head_10 BitVec[32]))
  :assumption
(= delete_0_head_10 (ite (and (= (select arr_val_15 delete_0_head_9) delete_0_val_1) (not (= (select arr_next_29 delete_0_head_1) (bvneg bv1[32])))) (select arr_next_29 delete_0_head_9) delete_0_head_9))
  :extrafuns ((delete_0_head_11 BitVec[32]))
  :assumption
(= delete_0_head_11 (ite (and (= (select arr_val_15 delete_0_head_10) delete_0_val_1) (not (= (select arr_next_29 delete_0_head_1) (bvneg bv1[32])))) (select arr_next_29 delete_0_head_10) delete_0_head_10))
  :extrafuns ((delete_0_head_12 BitVec[32]))
  :assumption
(= delete_0_head_12 (ite (and (= (select arr_val_15 delete_0_head_11) delete_0_val_1) (not (= (select arr_next_29 delete_0_head_1) (bvneg bv1[32])))) (select arr_next_29 delete_0_head_11) delete_0_head_11))
  :extrafuns ((delete_0_head_13 BitVec[32]))
  :assumption
(= delete_0_head_13 (ite (and (= (select arr_val_15 delete_0_head_12) delete_0_val_1) (not (= (select arr_next_29 delete_0_head_1) (bvneg bv1[32])))) (select arr_next_29 delete_0_head_12) delete_0_head_12))
  :extrafuns ((delete_0_head_14 BitVec[32]))
  :assumption
(= delete_0_head_14 (ite (and (= (select arr_val_15 delete_0_head_13) delete_0_val_1) (not (= (select arr_next_29 delete_0_head_1) (bvneg bv1[32])))) (select arr_next_29 delete_0_head_13) delete_0_head_13))
  :extrafuns ((delete_0_head_15 BitVec[32]))
  :assumption
(= delete_0_head_15 (ite (and (= (select arr_val_15 delete_0_head_14) delete_0_val_1) (not (= (select arr_next_29 delete_0_head_1) (bvneg bv1[32])))) (select arr_next_29 delete_0_head_14) delete_0_head_14))
  :extrafuns ((delete_0_prev_0 BitVec[32]))
  :extrafuns ((delete_0_prev_1 BitVec[32]))
  :assumption
(= delete_0_prev_1 (ite (not (= (select arr_next_29 delete_0_head_1) (bvneg bv1[32]))) delete_0_head_15 delete_0_prev_0))
  :extrafuns ((delete_0_curr_0 BitVec[32]))
  :extrafuns ((delete_0_curr_1 BitVec[32]))
  :assumption
(= delete_0_curr_1 (ite (not (= (select arr_next_29 delete_0_head_1) (bvneg bv1[32]))) (select arr_next_29 delete_0_head_15) delete_0_curr_0))
  :extrafuns ((arr_next_30 Array[32:32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= arr_next_30 (ite (and (and (not (= delete_0_curr_1 ?cvc_0)) (= (select arr_val_15 delete_0_curr_1) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (store arr_next_29 delete_0_prev_1 (select arr_next_29 delete_0_curr_1)) arr_next_29)))
  :extrafuns ((delete_0_curr_2 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_2 (ite (and (and (not (= delete_0_curr_1 ?cvc_0)) (= (select arr_val_15 delete_0_curr_1) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_30 delete_0_curr_1) delete_0_curr_1)))
  :extrafuns ((delete_0_prev_2 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_prev_2 (ite (and (and (not (= delete_0_curr_1 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_1) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) delete_0_curr_2 delete_0_prev_1)))
  :extrafuns ((delete_0_curr_3 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_3 (ite (and (and (not (= delete_0_curr_1 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_1) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_30 delete_0_curr_2) delete_0_curr_2)))
  :extrafuns ((arr_next_31 Array[32:32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= arr_next_31 (ite (and (and (not (= delete_0_curr_3 ?cvc_0)) (= (select arr_val_15 delete_0_curr_3) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (store arr_next_30 delete_0_prev_2 (select arr_next_30 delete_0_curr_3)) arr_next_30)))
  :extrafuns ((delete_0_curr_4 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_4 (ite (and (and (not (= delete_0_curr_3 ?cvc_0)) (= (select arr_val_15 delete_0_curr_3) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_31 delete_0_curr_3) delete_0_curr_3)))
  :extrafuns ((delete_0_prev_3 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_prev_3 (ite (and (and (not (= delete_0_curr_3 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_3) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) delete_0_curr_4 delete_0_prev_2)))
  :extrafuns ((delete_0_curr_5 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_5 (ite (and (and (not (= delete_0_curr_3 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_3) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_31 delete_0_curr_4) delete_0_curr_4)))
  :extrafuns ((arr_next_32 Array[32:32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= arr_next_32 (ite (and (and (not (= delete_0_curr_5 ?cvc_0)) (= (select arr_val_15 delete_0_curr_5) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (store arr_next_31 delete_0_prev_3 (select arr_next_31 delete_0_curr_5)) arr_next_31)))
  :extrafuns ((delete_0_curr_6 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_6 (ite (and (and (not (= delete_0_curr_5 ?cvc_0)) (= (select arr_val_15 delete_0_curr_5) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_32 delete_0_curr_5) delete_0_curr_5)))
  :extrafuns ((delete_0_prev_4 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_prev_4 (ite (and (and (not (= delete_0_curr_5 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_5) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) delete_0_curr_6 delete_0_prev_3)))
  :extrafuns ((delete_0_curr_7 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_7 (ite (and (and (not (= delete_0_curr_5 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_5) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_32 delete_0_curr_6) delete_0_curr_6)))
  :extrafuns ((arr_next_33 Array[32:32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= arr_next_33 (ite (and (and (not (= delete_0_curr_7 ?cvc_0)) (= (select arr_val_15 delete_0_curr_7) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (store arr_next_32 delete_0_prev_4 (select arr_next_32 delete_0_curr_7)) arr_next_32)))
  :extrafuns ((delete_0_curr_8 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_8 (ite (and (and (not (= delete_0_curr_7 ?cvc_0)) (= (select arr_val_15 delete_0_curr_7) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_33 delete_0_curr_7) delete_0_curr_7)))
  :extrafuns ((delete_0_prev_5 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_prev_5 (ite (and (and (not (= delete_0_curr_7 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_7) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) delete_0_curr_8 delete_0_prev_4)))
  :extrafuns ((delete_0_curr_9 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_9 (ite (and (and (not (= delete_0_curr_7 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_7) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_33 delete_0_curr_8) delete_0_curr_8)))
  :extrafuns ((arr_next_34 Array[32:32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= arr_next_34 (ite (and (and (not (= delete_0_curr_9 ?cvc_0)) (= (select arr_val_15 delete_0_curr_9) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (store arr_next_33 delete_0_prev_5 (select arr_next_33 delete_0_curr_9)) arr_next_33)))
  :extrafuns ((delete_0_curr_10 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_10 (ite (and (and (not (= delete_0_curr_9 ?cvc_0)) (= (select arr_val_15 delete_0_curr_9) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_34 delete_0_curr_9) delete_0_curr_9)))
  :extrafuns ((delete_0_prev_6 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_prev_6 (ite (and (and (not (= delete_0_curr_9 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_9) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) delete_0_curr_10 delete_0_prev_5)))
  :extrafuns ((delete_0_curr_11 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_11 (ite (and (and (not (= delete_0_curr_9 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_9) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_34 delete_0_curr_10) delete_0_curr_10)))
  :extrafuns ((arr_next_35 Array[32:32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= arr_next_35 (ite (and (and (not (= delete_0_curr_11 ?cvc_0)) (= (select arr_val_15 delete_0_curr_11) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (store arr_next_34 delete_0_prev_6 (select arr_next_34 delete_0_curr_11)) arr_next_34)))
  :extrafuns ((delete_0_curr_12 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_12 (ite (and (and (not (= delete_0_curr_11 ?cvc_0)) (= (select arr_val_15 delete_0_curr_11) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_35 delete_0_curr_11) delete_0_curr_11)))
  :extrafuns ((delete_0_prev_7 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_prev_7 (ite (and (and (not (= delete_0_curr_11 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_11) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) delete_0_curr_12 delete_0_prev_6)))
  :extrafuns ((delete_0_curr_13 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_13 (ite (and (and (not (= delete_0_curr_11 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_11) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_35 delete_0_curr_12) delete_0_curr_12)))
  :extrafuns ((arr_next_36 Array[32:32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= arr_next_36 (ite (and (and (not (= delete_0_curr_13 ?cvc_0)) (= (select arr_val_15 delete_0_curr_13) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (store arr_next_35 delete_0_prev_7 (select arr_next_35 delete_0_curr_13)) arr_next_35)))
  :extrafuns ((delete_0_curr_14 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_14 (ite (and (and (not (= delete_0_curr_13 ?cvc_0)) (= (select arr_val_15 delete_0_curr_13) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_36 delete_0_curr_13) delete_0_curr_13)))
  :extrafuns ((delete_0_prev_8 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_prev_8 (ite (and (and (not (= delete_0_curr_13 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_13) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) delete_0_curr_14 delete_0_prev_7)))
  :extrafuns ((delete_0_curr_15 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_15 (ite (and (and (not (= delete_0_curr_13 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_13) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_36 delete_0_curr_14) delete_0_curr_14)))
  :extrafuns ((arr_next_37 Array[32:32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= arr_next_37 (ite (and (and (not (= delete_0_curr_15 ?cvc_0)) (= (select arr_val_15 delete_0_curr_15) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (store arr_next_36 delete_0_prev_8 (select arr_next_36 delete_0_curr_15)) arr_next_36)))
  :extrafuns ((delete_0_curr_16 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_16 (ite (and (and (not (= delete_0_curr_15 ?cvc_0)) (= (select arr_val_15 delete_0_curr_15) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_37 delete_0_curr_15) delete_0_curr_15)))
  :extrafuns ((delete_0_prev_9 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_prev_9 (ite (and (and (not (= delete_0_curr_15 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_15) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) delete_0_curr_16 delete_0_prev_8)))
  :extrafuns ((delete_0_curr_17 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_17 (ite (and (and (not (= delete_0_curr_15 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_15) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_37 delete_0_curr_16) delete_0_curr_16)))
  :extrafuns ((arr_next_38 Array[32:32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= arr_next_38 (ite (and (and (not (= delete_0_curr_17 ?cvc_0)) (= (select arr_val_15 delete_0_curr_17) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (store arr_next_37 delete_0_prev_9 (select arr_next_37 delete_0_curr_17)) arr_next_37)))
  :extrafuns ((delete_0_curr_18 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_18 (ite (and (and (not (= delete_0_curr_17 ?cvc_0)) (= (select arr_val_15 delete_0_curr_17) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_38 delete_0_curr_17) delete_0_curr_17)))
  :extrafuns ((delete_0_prev_10 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_prev_10 (ite (and (and (not (= delete_0_curr_17 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_17) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) delete_0_curr_18 delete_0_prev_9)))
  :extrafuns ((delete_0_curr_19 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_19 (ite (and (and (not (= delete_0_curr_17 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_17) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_38 delete_0_curr_18) delete_0_curr_18)))
  :extrafuns ((arr_next_39 Array[32:32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= arr_next_39 (ite (and (and (not (= delete_0_curr_19 ?cvc_0)) (= (select arr_val_15 delete_0_curr_19) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (store arr_next_38 delete_0_prev_10 (select arr_next_38 delete_0_curr_19)) arr_next_38)))
  :extrafuns ((delete_0_curr_20 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_20 (ite (and (and (not (= delete_0_curr_19 ?cvc_0)) (= (select arr_val_15 delete_0_curr_19) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_39 delete_0_curr_19) delete_0_curr_19)))
  :extrafuns ((delete_0_prev_11 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_prev_11 (ite (and (and (not (= delete_0_curr_19 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_19) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) delete_0_curr_20 delete_0_prev_10)))
  :extrafuns ((delete_0_curr_21 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_21 (ite (and (and (not (= delete_0_curr_19 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_19) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_39 delete_0_curr_20) delete_0_curr_20)))
  :extrafuns ((arr_next_40 Array[32:32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= arr_next_40 (ite (and (and (not (= delete_0_curr_21 ?cvc_0)) (= (select arr_val_15 delete_0_curr_21) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (store arr_next_39 delete_0_prev_11 (select arr_next_39 delete_0_curr_21)) arr_next_39)))
  :extrafuns ((delete_0_curr_22 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_22 (ite (and (and (not (= delete_0_curr_21 ?cvc_0)) (= (select arr_val_15 delete_0_curr_21) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_40 delete_0_curr_21) delete_0_curr_21)))
  :extrafuns ((delete_0_prev_12 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_prev_12 (ite (and (and (not (= delete_0_curr_21 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_21) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) delete_0_curr_22 delete_0_prev_11)))
  :extrafuns ((delete_0_curr_23 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_23 (ite (and (and (not (= delete_0_curr_21 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_21) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_40 delete_0_curr_22) delete_0_curr_22)))
  :extrafuns ((arr_next_41 Array[32:32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= arr_next_41 (ite (and (and (not (= delete_0_curr_23 ?cvc_0)) (= (select arr_val_15 delete_0_curr_23) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (store arr_next_40 delete_0_prev_12 (select arr_next_40 delete_0_curr_23)) arr_next_40)))
  :extrafuns ((delete_0_curr_24 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_24 (ite (and (and (not (= delete_0_curr_23 ?cvc_0)) (= (select arr_val_15 delete_0_curr_23) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_41 delete_0_curr_23) delete_0_curr_23)))
  :extrafuns ((delete_0_prev_13 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_prev_13 (ite (and (and (not (= delete_0_curr_23 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_23) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) delete_0_curr_24 delete_0_prev_12)))
  :extrafuns ((delete_0_curr_25 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_25 (ite (and (and (not (= delete_0_curr_23 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_23) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_41 delete_0_curr_24) delete_0_curr_24)))
  :extrafuns ((arr_next_42 Array[32:32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= arr_next_42 (ite (and (and (not (= delete_0_curr_25 ?cvc_0)) (= (select arr_val_15 delete_0_curr_25) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (store arr_next_41 delete_0_prev_13 (select arr_next_41 delete_0_curr_25)) arr_next_41)))
  :extrafuns ((delete_0_curr_26 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_26 (ite (and (and (not (= delete_0_curr_25 ?cvc_0)) (= (select arr_val_15 delete_0_curr_25) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_42 delete_0_curr_25) delete_0_curr_25)))
  :extrafuns ((delete_0_prev_14 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_prev_14 (ite (and (and (not (= delete_0_curr_25 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_25) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) delete_0_curr_26 delete_0_prev_13)))
  :extrafuns ((delete_0_curr_27 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_27 (ite (and (and (not (= delete_0_curr_25 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_25) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_42 delete_0_curr_26) delete_0_curr_26)))
  :extrafuns ((arr_next_43 Array[32:32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= arr_next_43 (ite (and (and (not (= delete_0_curr_27 ?cvc_0)) (= (select arr_val_15 delete_0_curr_27) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (store arr_next_42 delete_0_prev_14 (select arr_next_42 delete_0_curr_27)) arr_next_42)))
  :extrafuns ((delete_0_curr_28 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_28 (ite (and (and (not (= delete_0_curr_27 ?cvc_0)) (= (select arr_val_15 delete_0_curr_27) delete_0_val_1)) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_43 delete_0_curr_27) delete_0_curr_27)))
  :extrafuns ((delete_0_prev_15 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_prev_15 (ite (and (and (not (= delete_0_curr_27 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_27) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) delete_0_curr_28 delete_0_prev_14)))
  :extrafuns ((delete_0_curr_29 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= delete_0_curr_29 (ite (and (and (not (= delete_0_curr_27 ?cvc_0)) (not (= (select arr_val_15 delete_0_curr_27) delete_0_val_1))) (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (select arr_next_43 delete_0_curr_28) delete_0_curr_28)))
  :extrafuns ((delete_return_0 BitVec[32]))
  :extrafuns ((delete_return_1 BitVec[32]))
  :assumption
(= delete_return_1 delete_0_head_15)
  :extrafuns ((main_0_head_2 BitVec[32]))
  :assumption
(= main_0_head_2 delete_return_1)
  :extrafuns ((main_0_x_0 BitVec[32]))
  :extrafuns ((member_0_val_0 BitVec[32]))
  :extrafuns ((member_0_val_1 BitVec[32]))
  :assumption
(= member_0_val_1 bv0[32])
  :extrafuns ((member_0_head_0 BitVec[32]))
  :extrafuns ((member_0_head_1 BitVec[32]))
  :assumption
(= member_0_head_1 main_0_head_2)
  :extrafuns ((member_0_curr_0 BitVec[32]))
  :extrafuns ((member_0_curr_1 BitVec[32]))
  :assumption
(= member_0_curr_1 member_0_head_1)
  :extrafuns ((member_0_result_0 BitVec[32]))
  :extrafuns ((member_0_result_1 BitVec[32]))
  :assumption
(= member_0_result_1 (ite (and (not (= member_0_curr_1 (bvneg bv1[32]))) (= (select arr_val_15 member_0_curr_1) member_0_val_1)) bv1[32] member_0_result_0))
  :extrafuns ((member_0_curr_2 BitVec[32]))
  :assumption
(flet ($cvc_0 (not (= member_0_curr_1 (bvneg bv1[32])))) (= member_0_curr_2 (ite (and (not (and $cvc_0 (= (select arr_val_15 member_0_curr_1) member_0_val_1))) $cvc_0) (select arr_next_43 member_0_curr_1) member_0_curr_1)))
  :extrafuns ((member_0_result_2 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= member_0_result_2 (ite (and (and (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1))) (not (= member_0_curr_2 ?cvc_0))) (= (select arr_val_15 member_0_curr_2) member_0_val_1)) bv1[32] member_0_result_1)))
  :extrafuns ((member_0_curr_3 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (flet ($cvc_1 (not (= member_0_curr_2 ?cvc_0))) (= member_0_curr_3 (ite (and (and (not (and $cvc_1 (= (select arr_val_15 member_0_curr_2) member_0_val_1))) (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1)))) $cvc_1) (select arr_next_43 member_0_curr_2) member_0_curr_2))))
  :extrafuns ((member_0_result_3 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= member_0_result_3 (ite (and (and (and (not (and (not (= member_0_curr_2 ?cvc_0)) (= (select arr_val_15 member_0_curr_2) member_0_val_1))) (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1)))) (not (= member_0_curr_3 ?cvc_0))) (= (select arr_val_15 member_0_curr_3) member_0_val_1)) bv1[32] member_0_result_2)))
  :extrafuns ((member_0_curr_4 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (flet ($cvc_1 (not (= member_0_curr_3 ?cvc_0))) (= member_0_curr_4 (ite (and (and (and (not (and $cvc_1 (= (select arr_val_15 member_0_curr_3) member_0_val_1))) (not (and (not (= member_0_curr_2 ?cvc_0)) (= (select arr_val_15 member_0_curr_2) member_0_val_1)))) (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1)))) $cvc_1) (select arr_next_43 member_0_curr_3) member_0_curr_3))))
  :extrafuns ((member_0_result_4 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= member_0_result_4 (ite (and (and (and (and (not (and (not (= member_0_curr_3 ?cvc_0)) (= (select arr_val_15 member_0_curr_3) member_0_val_1))) (not (and (not (= member_0_curr_2 ?cvc_0)) (= (select arr_val_15 member_0_curr_2) member_0_val_1)))) (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1)))) (not (= member_0_curr_4 ?cvc_0))) (= (select arr_val_15 member_0_curr_4) member_0_val_1)) bv1[32] member_0_result_3)))
  :extrafuns ((member_0_curr_5 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (flet ($cvc_1 (not (= member_0_curr_4 ?cvc_0))) (= member_0_curr_5 (ite (and (and (and (and (not (and $cvc_1 (= (select arr_val_15 member_0_curr_4) member_0_val_1))) (not (and (not (= member_0_curr_3 ?cvc_0)) (= (select arr_val_15 member_0_curr_3) member_0_val_1)))) (not (and (not (= member_0_curr_2 ?cvc_0)) (= (select arr_val_15 member_0_curr_2) member_0_val_1)))) (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1)))) $cvc_1) (select arr_next_43 member_0_curr_4) member_0_curr_4))))
  :extrafuns ((member_0_result_5 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= member_0_result_5 (ite (and (and (and (and (and (not (and (not (= member_0_curr_4 ?cvc_0)) (= (select arr_val_15 member_0_curr_4) member_0_val_1))) (not (and (not (= member_0_curr_3 ?cvc_0)) (= (select arr_val_15 member_0_curr_3) member_0_val_1)))) (not (and (not (= member_0_curr_2 ?cvc_0)) (= (select arr_val_15 member_0_curr_2) member_0_val_1)))) (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1)))) (not (= member_0_curr_5 ?cvc_0))) (= (select arr_val_15 member_0_curr_5) member_0_val_1)) bv1[32] member_0_result_4)))
  :extrafuns ((member_0_curr_6 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (flet ($cvc_1 (not (= member_0_curr_5 ?cvc_0))) (= member_0_curr_6 (ite (and (and (and (and (and (not (and $cvc_1 (= (select arr_val_15 member_0_curr_5) member_0_val_1))) (not (and (not (= member_0_curr_4 ?cvc_0)) (= (select arr_val_15 member_0_curr_4) member_0_val_1)))) (not (and (not (= member_0_curr_3 ?cvc_0)) (= (select arr_val_15 member_0_curr_3) member_0_val_1)))) (not (and (not (= member_0_curr_2 ?cvc_0)) (= (select arr_val_15 member_0_curr_2) member_0_val_1)))) (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1)))) $cvc_1) (select arr_next_43 member_0_curr_5) member_0_curr_5))))
  :extrafuns ((member_0_result_6 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= member_0_result_6 (ite (and (and (and (and (and (and (not (and (not (= member_0_curr_5 ?cvc_0)) (= (select arr_val_15 member_0_curr_5) member_0_val_1))) (not (and (not (= member_0_curr_4 ?cvc_0)) (= (select arr_val_15 member_0_curr_4) member_0_val_1)))) (not (and (not (= member_0_curr_3 ?cvc_0)) (= (select arr_val_15 member_0_curr_3) member_0_val_1)))) (not (and (not (= member_0_curr_2 ?cvc_0)) (= (select arr_val_15 member_0_curr_2) member_0_val_1)))) (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1)))) (not (= member_0_curr_6 ?cvc_0))) (= (select arr_val_15 member_0_curr_6) member_0_val_1)) bv1[32] member_0_result_5)))
  :extrafuns ((member_0_curr_7 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (flet ($cvc_1 (not (= member_0_curr_6 ?cvc_0))) (= member_0_curr_7 (ite (and (and (and (and (and (and (not (and $cvc_1 (= (select arr_val_15 member_0_curr_6) member_0_val_1))) (not (and (not (= member_0_curr_5 ?cvc_0)) (= (select arr_val_15 member_0_curr_5) member_0_val_1)))) (not (and (not (= member_0_curr_4 ?cvc_0)) (= (select arr_val_15 member_0_curr_4) member_0_val_1)))) (not (and (not (= member_0_curr_3 ?cvc_0)) (= (select arr_val_15 member_0_curr_3) member_0_val_1)))) (not (and (not (= member_0_curr_2 ?cvc_0)) (= (select arr_val_15 member_0_curr_2) member_0_val_1)))) (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1)))) $cvc_1) (select arr_next_43 member_0_curr_6) member_0_curr_6))))
  :extrafuns ((member_0_result_7 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= member_0_result_7 (ite (and (and (and (and (and (and (and (not (and (not (= member_0_curr_6 ?cvc_0)) (= (select arr_val_15 member_0_curr_6) member_0_val_1))) (not (and (not (= member_0_curr_5 ?cvc_0)) (= (select arr_val_15 member_0_curr_5) member_0_val_1)))) (not (and (not (= member_0_curr_4 ?cvc_0)) (= (select arr_val_15 member_0_curr_4) member_0_val_1)))) (not (and (not (= member_0_curr_3 ?cvc_0)) (= (select arr_val_15 member_0_curr_3) member_0_val_1)))) (not (and (not (= member_0_curr_2 ?cvc_0)) (= (select arr_val_15 member_0_curr_2) member_0_val_1)))) (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1)))) (not (= member_0_curr_7 ?cvc_0))) (= (select arr_val_15 member_0_curr_7) member_0_val_1)) bv1[32] member_0_result_6)))
  :extrafuns ((member_0_curr_8 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (flet ($cvc_1 (not (= member_0_curr_7 ?cvc_0))) (= member_0_curr_8 (ite (and (and (and (and (and (and (and (not (and $cvc_1 (= (select arr_val_15 member_0_curr_7) member_0_val_1))) (not (and (not (= member_0_curr_6 ?cvc_0)) (= (select arr_val_15 member_0_curr_6) member_0_val_1)))) (not (and (not (= member_0_curr_5 ?cvc_0)) (= (select arr_val_15 member_0_curr_5) member_0_val_1)))) (not (and (not (= member_0_curr_4 ?cvc_0)) (= (select arr_val_15 member_0_curr_4) member_0_val_1)))) (not (and (not (= member_0_curr_3 ?cvc_0)) (= (select arr_val_15 member_0_curr_3) member_0_val_1)))) (not (and (not (= member_0_curr_2 ?cvc_0)) (= (select arr_val_15 member_0_curr_2) member_0_val_1)))) (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1)))) $cvc_1) (select arr_next_43 member_0_curr_7) member_0_curr_7))))
  :extrafuns ((member_0_result_8 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= member_0_result_8 (ite (and (and (and (and (and (and (and (and (not (and (not (= member_0_curr_7 ?cvc_0)) (= (select arr_val_15 member_0_curr_7) member_0_val_1))) (not (and (not (= member_0_curr_6 ?cvc_0)) (= (select arr_val_15 member_0_curr_6) member_0_val_1)))) (not (and (not (= member_0_curr_5 ?cvc_0)) (= (select arr_val_15 member_0_curr_5) member_0_val_1)))) (not (and (not (= member_0_curr_4 ?cvc_0)) (= (select arr_val_15 member_0_curr_4) member_0_val_1)))) (not (and (not (= member_0_curr_3 ?cvc_0)) (= (select arr_val_15 member_0_curr_3) member_0_val_1)))) (not (and (not (= member_0_curr_2 ?cvc_0)) (= (select arr_val_15 member_0_curr_2) member_0_val_1)))) (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1)))) (not (= member_0_curr_8 ?cvc_0))) (= (select arr_val_15 member_0_curr_8) member_0_val_1)) bv1[32] member_0_result_7)))
  :extrafuns ((member_0_curr_9 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (flet ($cvc_1 (not (= member_0_curr_8 ?cvc_0))) (= member_0_curr_9 (ite (and (and (and (and (and (and (and (and (not (and $cvc_1 (= (select arr_val_15 member_0_curr_8) member_0_val_1))) (not (and (not (= member_0_curr_7 ?cvc_0)) (= (select arr_val_15 member_0_curr_7) member_0_val_1)))) (not (and (not (= member_0_curr_6 ?cvc_0)) (= (select arr_val_15 member_0_curr_6) member_0_val_1)))) (not (and (not (= member_0_curr_5 ?cvc_0)) (= (select arr_val_15 member_0_curr_5) member_0_val_1)))) (not (and (not (= member_0_curr_4 ?cvc_0)) (= (select arr_val_15 member_0_curr_4) member_0_val_1)))) (not (and (not (= member_0_curr_3 ?cvc_0)) (= (select arr_val_15 member_0_curr_3) member_0_val_1)))) (not (and (not (= member_0_curr_2 ?cvc_0)) (= (select arr_val_15 member_0_curr_2) member_0_val_1)))) (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1)))) $cvc_1) (select arr_next_43 member_0_curr_8) member_0_curr_8))))
  :extrafuns ((member_0_result_9 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= member_0_result_9 (ite (and (and (and (and (and (and (and (and (and (not (and (not (= member_0_curr_8 ?cvc_0)) (= (select arr_val_15 member_0_curr_8) member_0_val_1))) (not (and (not (= member_0_curr_7 ?cvc_0)) (= (select arr_val_15 member_0_curr_7) member_0_val_1)))) (not (and (not (= member_0_curr_6 ?cvc_0)) (= (select arr_val_15 member_0_curr_6) member_0_val_1)))) (not (and (not (= member_0_curr_5 ?cvc_0)) (= (select arr_val_15 member_0_curr_5) member_0_val_1)))) (not (and (not (= member_0_curr_4 ?cvc_0)) (= (select arr_val_15 member_0_curr_4) member_0_val_1)))) (not (and (not (= member_0_curr_3 ?cvc_0)) (= (select arr_val_15 member_0_curr_3) member_0_val_1)))) (not (and (not (= member_0_curr_2 ?cvc_0)) (= (select arr_val_15 member_0_curr_2) member_0_val_1)))) (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1)))) (not (= member_0_curr_9 ?cvc_0))) (= (select arr_val_15 member_0_curr_9) member_0_val_1)) bv1[32] member_0_result_8)))
  :extrafuns ((member_0_curr_10 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (flet ($cvc_1 (not (= member_0_curr_9 ?cvc_0))) (= member_0_curr_10 (ite (and (and (and (and (and (and (and (and (and (not (and $cvc_1 (= (select arr_val_15 member_0_curr_9) member_0_val_1))) (not (and (not (= member_0_curr_8 ?cvc_0)) (= (select arr_val_15 member_0_curr_8) member_0_val_1)))) (not (and (not (= member_0_curr_7 ?cvc_0)) (= (select arr_val_15 member_0_curr_7) member_0_val_1)))) (not (and (not (= member_0_curr_6 ?cvc_0)) (= (select arr_val_15 member_0_curr_6) member_0_val_1)))) (not (and (not (= member_0_curr_5 ?cvc_0)) (= (select arr_val_15 member_0_curr_5) member_0_val_1)))) (not (and (not (= member_0_curr_4 ?cvc_0)) (= (select arr_val_15 member_0_curr_4) member_0_val_1)))) (not (and (not (= member_0_curr_3 ?cvc_0)) (= (select arr_val_15 member_0_curr_3) member_0_val_1)))) (not (and (not (= member_0_curr_2 ?cvc_0)) (= (select arr_val_15 member_0_curr_2) member_0_val_1)))) (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1)))) $cvc_1) (select arr_next_43 member_0_curr_9) member_0_curr_9))))
  :extrafuns ((member_0_result_10 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= member_0_result_10 (ite (and (and (and (and (and (and (and (and (and (and (not (and (not (= member_0_curr_9 ?cvc_0)) (= (select arr_val_15 member_0_curr_9) member_0_val_1))) (not (and (not (= member_0_curr_8 ?cvc_0)) (= (select arr_val_15 member_0_curr_8) member_0_val_1)))) (not (and (not (= member_0_curr_7 ?cvc_0)) (= (select arr_val_15 member_0_curr_7) member_0_val_1)))) (not (and (not (= member_0_curr_6 ?cvc_0)) (= (select arr_val_15 member_0_curr_6) member_0_val_1)))) (not (and (not (= member_0_curr_5 ?cvc_0)) (= (select arr_val_15 member_0_curr_5) member_0_val_1)))) (not (and (not (= member_0_curr_4 ?cvc_0)) (= (select arr_val_15 member_0_curr_4) member_0_val_1)))) (not (and (not (= member_0_curr_3 ?cvc_0)) (= (select arr_val_15 member_0_curr_3) member_0_val_1)))) (not (and (not (= member_0_curr_2 ?cvc_0)) (= (select arr_val_15 member_0_curr_2) member_0_val_1)))) (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1)))) (not (= member_0_curr_10 ?cvc_0))) (= (select arr_val_15 member_0_curr_10) member_0_val_1)) bv1[32] member_0_result_9)))
  :extrafuns ((member_0_curr_11 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (flet ($cvc_1 (not (= member_0_curr_10 ?cvc_0))) (= member_0_curr_11 (ite (and (and (and (and (and (and (and (and (and (and (not (and $cvc_1 (= (select arr_val_15 member_0_curr_10) member_0_val_1))) (not (and (not (= member_0_curr_9 ?cvc_0)) (= (select arr_val_15 member_0_curr_9) member_0_val_1)))) (not (and (not (= member_0_curr_8 ?cvc_0)) (= (select arr_val_15 member_0_curr_8) member_0_val_1)))) (not (and (not (= member_0_curr_7 ?cvc_0)) (= (select arr_val_15 member_0_curr_7) member_0_val_1)))) (not (and (not (= member_0_curr_6 ?cvc_0)) (= (select arr_val_15 member_0_curr_6) member_0_val_1)))) (not (and (not (= member_0_curr_5 ?cvc_0)) (= (select arr_val_15 member_0_curr_5) member_0_val_1)))) (not (and (not (= member_0_curr_4 ?cvc_0)) (= (select arr_val_15 member_0_curr_4) member_0_val_1)))) (not (and (not (= member_0_curr_3 ?cvc_0)) (= (select arr_val_15 member_0_curr_3) member_0_val_1)))) (not (and (not (= member_0_curr_2 ?cvc_0)) (= (select arr_val_15 member_0_curr_2) member_0_val_1)))) (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1)))) $cvc_1) (select arr_next_43 member_0_curr_10) member_0_curr_10))))
  :extrafuns ((member_0_result_11 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= member_0_result_11 (ite (and (and (and (and (and (and (and (and (and (and (and (not (and (not (= member_0_curr_10 ?cvc_0)) (= (select arr_val_15 member_0_curr_10) member_0_val_1))) (not (and (not (= member_0_curr_9 ?cvc_0)) (= (select arr_val_15 member_0_curr_9) member_0_val_1)))) (not (and (not (= member_0_curr_8 ?cvc_0)) (= (select arr_val_15 member_0_curr_8) member_0_val_1)))) (not (and (not (= member_0_curr_7 ?cvc_0)) (= (select arr_val_15 member_0_curr_7) member_0_val_1)))) (not (and (not (= member_0_curr_6 ?cvc_0)) (= (select arr_val_15 member_0_curr_6) member_0_val_1)))) (not (and (not (= member_0_curr_5 ?cvc_0)) (= (select arr_val_15 member_0_curr_5) member_0_val_1)))) (not (and (not (= member_0_curr_4 ?cvc_0)) (= (select arr_val_15 member_0_curr_4) member_0_val_1)))) (not (and (not (= member_0_curr_3 ?cvc_0)) (= (select arr_val_15 member_0_curr_3) member_0_val_1)))) (not (and (not (= member_0_curr_2 ?cvc_0)) (= (select arr_val_15 member_0_curr_2) member_0_val_1)))) (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1)))) (not (= member_0_curr_11 ?cvc_0))) (= (select arr_val_15 member_0_curr_11) member_0_val_1)) bv1[32] member_0_result_10)))
  :extrafuns ((member_0_curr_12 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (flet ($cvc_1 (not (= member_0_curr_11 ?cvc_0))) (= member_0_curr_12 (ite (and (and (and (and (and (and (and (and (and (and (and (not (and $cvc_1 (= (select arr_val_15 member_0_curr_11) member_0_val_1))) (not (and (not (= member_0_curr_10 ?cvc_0)) (= (select arr_val_15 member_0_curr_10) member_0_val_1)))) (not (and (not (= member_0_curr_9 ?cvc_0)) (= (select arr_val_15 member_0_curr_9) member_0_val_1)))) (not (and (not (= member_0_curr_8 ?cvc_0)) (= (select arr_val_15 member_0_curr_8) member_0_val_1)))) (not (and (not (= member_0_curr_7 ?cvc_0)) (= (select arr_val_15 member_0_curr_7) member_0_val_1)))) (not (and (not (= member_0_curr_6 ?cvc_0)) (= (select arr_val_15 member_0_curr_6) member_0_val_1)))) (not (and (not (= member_0_curr_5 ?cvc_0)) (= (select arr_val_15 member_0_curr_5) member_0_val_1)))) (not (and (not (= member_0_curr_4 ?cvc_0)) (= (select arr_val_15 member_0_curr_4) member_0_val_1)))) (not (and (not (= member_0_curr_3 ?cvc_0)) (= (select arr_val_15 member_0_curr_3) member_0_val_1)))) (not (and (not (= member_0_curr_2 ?cvc_0)) (= (select arr_val_15 member_0_curr_2) member_0_val_1)))) (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1)))) $cvc_1) (select arr_next_43 member_0_curr_11) member_0_curr_11))))
  :extrafuns ((member_0_result_12 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= member_0_result_12 (ite (and (and (and (and (and (and (and (and (and (and (and (and (not (and (not (= member_0_curr_11 ?cvc_0)) (= (select arr_val_15 member_0_curr_11) member_0_val_1))) (not (and (not (= member_0_curr_10 ?cvc_0)) (= (select arr_val_15 member_0_curr_10) member_0_val_1)))) (not (and (not (= member_0_curr_9 ?cvc_0)) (= (select arr_val_15 member_0_curr_9) member_0_val_1)))) (not (and (not (= member_0_curr_8 ?cvc_0)) (= (select arr_val_15 member_0_curr_8) member_0_val_1)))) (not (and (not (= member_0_curr_7 ?cvc_0)) (= (select arr_val_15 member_0_curr_7) member_0_val_1)))) (not (and (not (= member_0_curr_6 ?cvc_0)) (= (select arr_val_15 member_0_curr_6) member_0_val_1)))) (not (and (not (= member_0_curr_5 ?cvc_0)) (= (select arr_val_15 member_0_curr_5) member_0_val_1)))) (not (and (not (= member_0_curr_4 ?cvc_0)) (= (select arr_val_15 member_0_curr_4) member_0_val_1)))) (not (and (not (= member_0_curr_3 ?cvc_0)) (= (select arr_val_15 member_0_curr_3) member_0_val_1)))) (not (and (not (= member_0_curr_2 ?cvc_0)) (= (select arr_val_15 member_0_curr_2) member_0_val_1)))) (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1)))) (not (= member_0_curr_12 ?cvc_0))) (= (select arr_val_15 member_0_curr_12) member_0_val_1)) bv1[32] member_0_result_11)))
  :extrafuns ((member_0_curr_13 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (flet ($cvc_1 (not (= member_0_curr_12 ?cvc_0))) (= member_0_curr_13 (ite (and (and (and (and (and (and (and (and (and (and (and (and (not (and $cvc_1 (= (select arr_val_15 member_0_curr_12) member_0_val_1))) (not (and (not (= member_0_curr_11 ?cvc_0)) (= (select arr_val_15 member_0_curr_11) member_0_val_1)))) (not (and (not (= member_0_curr_10 ?cvc_0)) (= (select arr_val_15 member_0_curr_10) member_0_val_1)))) (not (and (not (= member_0_curr_9 ?cvc_0)) (= (select arr_val_15 member_0_curr_9) member_0_val_1)))) (not (and (not (= member_0_curr_8 ?cvc_0)) (= (select arr_val_15 member_0_curr_8) member_0_val_1)))) (not (and (not (= member_0_curr_7 ?cvc_0)) (= (select arr_val_15 member_0_curr_7) member_0_val_1)))) (not (and (not (= member_0_curr_6 ?cvc_0)) (= (select arr_val_15 member_0_curr_6) member_0_val_1)))) (not (and (not (= member_0_curr_5 ?cvc_0)) (= (select arr_val_15 member_0_curr_5) member_0_val_1)))) (not (and (not (= member_0_curr_4 ?cvc_0)) (= (select arr_val_15 member_0_curr_4) member_0_val_1)))) (not (and (not (= member_0_curr_3 ?cvc_0)) (= (select arr_val_15 member_0_curr_3) member_0_val_1)))) (not (and (not (= member_0_curr_2 ?cvc_0)) (= (select arr_val_15 member_0_curr_2) member_0_val_1)))) (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1)))) $cvc_1) (select arr_next_43 member_0_curr_12) member_0_curr_12))))
  :extrafuns ((member_0_result_13 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= member_0_result_13 (ite (and (and (and (and (and (and (and (and (and (and (and (and (and (not (and (not (= member_0_curr_12 ?cvc_0)) (= (select arr_val_15 member_0_curr_12) member_0_val_1))) (not (and (not (= member_0_curr_11 ?cvc_0)) (= (select arr_val_15 member_0_curr_11) member_0_val_1)))) (not (and (not (= member_0_curr_10 ?cvc_0)) (= (select arr_val_15 member_0_curr_10) member_0_val_1)))) (not (and (not (= member_0_curr_9 ?cvc_0)) (= (select arr_val_15 member_0_curr_9) member_0_val_1)))) (not (and (not (= member_0_curr_8 ?cvc_0)) (= (select arr_val_15 member_0_curr_8) member_0_val_1)))) (not (and (not (= member_0_curr_7 ?cvc_0)) (= (select arr_val_15 member_0_curr_7) member_0_val_1)))) (not (and (not (= member_0_curr_6 ?cvc_0)) (= (select arr_val_15 member_0_curr_6) member_0_val_1)))) (not (and (not (= member_0_curr_5 ?cvc_0)) (= (select arr_val_15 member_0_curr_5) member_0_val_1)))) (not (and (not (= member_0_curr_4 ?cvc_0)) (= (select arr_val_15 member_0_curr_4) member_0_val_1)))) (not (and (not (= member_0_curr_3 ?cvc_0)) (= (select arr_val_15 member_0_curr_3) member_0_val_1)))) (not (and (not (= member_0_curr_2 ?cvc_0)) (= (select arr_val_15 member_0_curr_2) member_0_val_1)))) (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1)))) (not (= member_0_curr_13 ?cvc_0))) (= (select arr_val_15 member_0_curr_13) member_0_val_1)) bv1[32] member_0_result_12)))
  :extrafuns ((member_0_curr_14 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (flet ($cvc_1 (not (= member_0_curr_13 ?cvc_0))) (= member_0_curr_14 (ite (and (and (and (and (and (and (and (and (and (and (and (and (and (not (and $cvc_1 (= (select arr_val_15 member_0_curr_13) member_0_val_1))) (not (and (not (= member_0_curr_12 ?cvc_0)) (= (select arr_val_15 member_0_curr_12) member_0_val_1)))) (not (and (not (= member_0_curr_11 ?cvc_0)) (= (select arr_val_15 member_0_curr_11) member_0_val_1)))) (not (and (not (= member_0_curr_10 ?cvc_0)) (= (select arr_val_15 member_0_curr_10) member_0_val_1)))) (not (and (not (= member_0_curr_9 ?cvc_0)) (= (select arr_val_15 member_0_curr_9) member_0_val_1)))) (not (and (not (= member_0_curr_8 ?cvc_0)) (= (select arr_val_15 member_0_curr_8) member_0_val_1)))) (not (and (not (= member_0_curr_7 ?cvc_0)) (= (select arr_val_15 member_0_curr_7) member_0_val_1)))) (not (and (not (= member_0_curr_6 ?cvc_0)) (= (select arr_val_15 member_0_curr_6) member_0_val_1)))) (not (and (not (= member_0_curr_5 ?cvc_0)) (= (select arr_val_15 member_0_curr_5) member_0_val_1)))) (not (and (not (= member_0_curr_4 ?cvc_0)) (= (select arr_val_15 member_0_curr_4) member_0_val_1)))) (not (and (not (= member_0_curr_3 ?cvc_0)) (= (select arr_val_15 member_0_curr_3) member_0_val_1)))) (not (and (not (= member_0_curr_2 ?cvc_0)) (= (select arr_val_15 member_0_curr_2) member_0_val_1)))) (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1)))) $cvc_1) (select arr_next_43 member_0_curr_13) member_0_curr_13))))
  :extrafuns ((member_0_result_14 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= member_0_result_14 (ite (and (and (and (and (and (and (and (and (and (and (and (and (and (and (not (and (not (= member_0_curr_13 ?cvc_0)) (= (select arr_val_15 member_0_curr_13) member_0_val_1))) (not (and (not (= member_0_curr_12 ?cvc_0)) (= (select arr_val_15 member_0_curr_12) member_0_val_1)))) (not (and (not (= member_0_curr_11 ?cvc_0)) (= (select arr_val_15 member_0_curr_11) member_0_val_1)))) (not (and (not (= member_0_curr_10 ?cvc_0)) (= (select arr_val_15 member_0_curr_10) member_0_val_1)))) (not (and (not (= member_0_curr_9 ?cvc_0)) (= (select arr_val_15 member_0_curr_9) member_0_val_1)))) (not (and (not (= member_0_curr_8 ?cvc_0)) (= (select arr_val_15 member_0_curr_8) member_0_val_1)))) (not (and (not (= member_0_curr_7 ?cvc_0)) (= (select arr_val_15 member_0_curr_7) member_0_val_1)))) (not (and (not (= member_0_curr_6 ?cvc_0)) (= (select arr_val_15 member_0_curr_6) member_0_val_1)))) (not (and (not (= member_0_curr_5 ?cvc_0)) (= (select arr_val_15 member_0_curr_5) member_0_val_1)))) (not (and (not (= member_0_curr_4 ?cvc_0)) (= (select arr_val_15 member_0_curr_4) member_0_val_1)))) (not (and (not (= member_0_curr_3 ?cvc_0)) (= (select arr_val_15 member_0_curr_3) member_0_val_1)))) (not (and (not (= member_0_curr_2 ?cvc_0)) (= (select arr_val_15 member_0_curr_2) member_0_val_1)))) (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1)))) (not (= member_0_curr_14 ?cvc_0))) (= (select arr_val_15 member_0_curr_14) member_0_val_1)) bv1[32] member_0_result_13)))
  :extrafuns ((member_0_curr_15 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (flet ($cvc_1 (not (= member_0_curr_14 ?cvc_0))) (= member_0_curr_15 (ite (and (and (and (and (and (and (and (and (and (and (and (and (and (and (not (and $cvc_1 (= (select arr_val_15 member_0_curr_14) member_0_val_1))) (not (and (not (= member_0_curr_13 ?cvc_0)) (= (select arr_val_15 member_0_curr_13) member_0_val_1)))) (not (and (not (= member_0_curr_12 ?cvc_0)) (= (select arr_val_15 member_0_curr_12) member_0_val_1)))) (not (and (not (= member_0_curr_11 ?cvc_0)) (= (select arr_val_15 member_0_curr_11) member_0_val_1)))) (not (and (not (= member_0_curr_10 ?cvc_0)) (= (select arr_val_15 member_0_curr_10) member_0_val_1)))) (not (and (not (= member_0_curr_9 ?cvc_0)) (= (select arr_val_15 member_0_curr_9) member_0_val_1)))) (not (and (not (= member_0_curr_8 ?cvc_0)) (= (select arr_val_15 member_0_curr_8) member_0_val_1)))) (not (and (not (= member_0_curr_7 ?cvc_0)) (= (select arr_val_15 member_0_curr_7) member_0_val_1)))) (not (and (not (= member_0_curr_6 ?cvc_0)) (= (select arr_val_15 member_0_curr_6) member_0_val_1)))) (not (and (not (= member_0_curr_5 ?cvc_0)) (= (select arr_val_15 member_0_curr_5) member_0_val_1)))) (not (and (not (= member_0_curr_4 ?cvc_0)) (= (select arr_val_15 member_0_curr_4) member_0_val_1)))) (not (and (not (= member_0_curr_3 ?cvc_0)) (= (select arr_val_15 member_0_curr_3) member_0_val_1)))) (not (and (not (= member_0_curr_2 ?cvc_0)) (= (select arr_val_15 member_0_curr_2) member_0_val_1)))) (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1)))) $cvc_1) (select arr_next_43 member_0_curr_14) member_0_curr_14))))
  :extrafuns ((member_0_result_15 BitVec[32]))
  :assumption
(let (?cvc_0 (bvneg bv1[32])) (= member_0_result_15 (ite (and (and (and (and (and (and (and (and (and (and (and (and (and (not (and (not (= member_0_curr_14 ?cvc_0)) (= (select arr_val_15 member_0_curr_14) member_0_val_1))) (not (and (not (= member_0_curr_13 ?cvc_0)) (= (select arr_val_15 member_0_curr_13) member_0_val_1)))) (not (and (not (= member_0_curr_12 ?cvc_0)) (= (select arr_val_15 member_0_curr_12) member_0_val_1)))) (not (and (not (= member_0_curr_11 ?cvc_0)) (= (select arr_val_15 member_0_curr_11) member_0_val_1)))) (not (and (not (= member_0_curr_10 ?cvc_0)) (= (select arr_val_15 member_0_curr_10) member_0_val_1)))) (not (and (not (= member_0_curr_9 ?cvc_0)) (= (select arr_val_15 member_0_curr_9) member_0_val_1)))) (not (and (not (= member_0_curr_8 ?cvc_0)) (= (select arr_val_15 member_0_curr_8) member_0_val_1)))) (not (and (not (= member_0_curr_7 ?cvc_0)) (= (select arr_val_15 member_0_curr_7) member_0_val_1)))) (not (and (not (= member_0_curr_6 ?cvc_0)) (= (select arr_val_15 member_0_curr_6) member_0_val_1)))) (not (and (not (= member_0_curr_5 ?cvc_0)) (= (select arr_val_15 member_0_curr_5) member_0_val_1)))) (not (and (not (= member_0_curr_4 ?cvc_0)) (= (select arr_val_15 member_0_curr_4) member_0_val_1)))) (not (and (not (= member_0_curr_3 ?cvc_0)) (= (select arr_val_15 member_0_curr_3) member_0_val_1)))) (not (and (not (= member_0_curr_2 ?cvc_0)) (= (select arr_val_15 member_0_curr_2) member_0_val_1)))) (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1)))) bv0[32] member_0_result_14)))
  :extrafuns ((main_0_x_1 BitVec[32]))
  :assumption
(= main_0_x_1 member_0_result_15)
  :formula
(let (?cvc_0 (bvneg bv1[32])) (flet ($cvc_1 (not (= (select arr_next_29 delete_0_head_1) ?cvc_0))) (flet ($cvc_2 (not (= member_0_curr_14 ?cvc_0))) (not (and (and (and (and (implies (bvult main_0_i_14 bv13[32]) (not (bvult main_0_i_15 bv13[32]))) (implies (and (= (select arr_val_15 delete_0_head_14) delete_0_val_1) $cvc_1) (not (= (select arr_val_15 delete_0_head_15) delete_0_val_1)))) (implies (and (not (= delete_0_curr_27 ?cvc_0)) $cvc_1) (not (not (= delete_0_curr_29 ?cvc_0))))) (implies (and (and (and (and (and (and (and (and (and (and (and (and (and (and (not (and $cvc_2 (= (select arr_val_15 member_0_curr_14) member_0_val_1))) (not (and (not (= member_0_curr_13 ?cvc_0)) (= (select arr_val_15 member_0_curr_13) member_0_val_1)))) (not (and (not (= member_0_curr_12 ?cvc_0)) (= (select arr_val_15 member_0_curr_12) member_0_val_1)))) (not (and (not (= member_0_curr_11 ?cvc_0)) (= (select arr_val_15 member_0_curr_11) member_0_val_1)))) (not (and (not (= member_0_curr_10 ?cvc_0)) (= (select arr_val_15 member_0_curr_10) member_0_val_1)))) (not (and (not (= member_0_curr_9 ?cvc_0)) (= (select arr_val_15 member_0_curr_9) member_0_val_1)))) (not (and (not (= member_0_curr_8 ?cvc_0)) (= (select arr_val_15 member_0_curr_8) member_0_val_1)))) (not (and (not (= member_0_curr_7 ?cvc_0)) (= (select arr_val_15 member_0_curr_7) member_0_val_1)))) (not (and (not (= member_0_curr_6 ?cvc_0)) (= (select arr_val_15 member_0_curr_6) member_0_val_1)))) (not (and (not (= member_0_curr_5 ?cvc_0)) (= (select arr_val_15 member_0_curr_5) member_0_val_1)))) (not (and (not (= member_0_curr_4 ?cvc_0)) (= (select arr_val_15 member_0_curr_4) member_0_val_1)))) (not (and (not (= member_0_curr_3 ?cvc_0)) (= (select arr_val_15 member_0_curr_3) member_0_val_1)))) (not (and (not (= member_0_curr_2 ?cvc_0)) (= (select arr_val_15 member_0_curr_2) member_0_val_1)))) (not (and (not (= member_0_curr_1 ?cvc_0)) (= (select arr_val_15 member_0_curr_1) member_0_val_1)))) $cvc_2) (not (not (= member_0_curr_15 ?cvc_0))))) (= main_0_x_1 bv0[32]))))))
)
