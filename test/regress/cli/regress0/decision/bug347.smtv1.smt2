; COMMAND-LINE: --decision=justification
; EXPECT: sat
(set-option :incremental false)
(set-info :status sat)
(set-info :category "unknown")
(set-logic QF_AUFBV)
(declare-fun delete_0_val_1 () (_ BitVec 32))
(declare-fun delete_0_curr_6 () (_ BitVec 32))
(declare-fun arr_next_13 () (Array (_ BitVec 32) (_ BitVec 32)))
(declare-fun arr_next_14 () (Array (_ BitVec 32) (_ BitVec 32)))
(declare-fun delete_0_head_1 () (_ BitVec 32))
(check-sat-assuming ( (and (= (_ bv0 32) (ite (= (_ bv0 32) delete_0_head_1) (select arr_next_14 delete_0_curr_6) delete_0_curr_6)) (= arr_next_14 arr_next_13) (= (_ bv1 32) (select arr_next_13 (_ bv1 32))) (= delete_0_curr_6 (ite (= (_ bv0 32) delete_0_val_1) (_ bv0 32) (_ bv1 32)))) ))
