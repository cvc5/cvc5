(benchmark B_
  :status sat
  :category { unknown }
  :logic QF_AUFBV
  :extrafuns ((delete_0_val_1 BitVec[32]))
  :extrafuns ((delete_0_curr_6 BitVec[32]))
  :extrafuns ((arr_next_13 Array[32:32]))
  :extrafuns ((arr_next_14 Array[32:32]))
  :extrafuns ((delete_0_head_1 BitVec[32]))
  :formula (and (= bv0[32] (ite (= bv0[32] delete_0_head_1) (select arr_next_14 delete_0_curr_6) delete_0_curr_6)) (= arr_next_14 arr_next_13) (= bv1[32] (select arr_next_13 bv1[32])) (= delete_0_curr_6 (ite (= bv0[32] delete_0_val_1) bv0[32] bv1[32])))
)
