; COMMAND-LINE: -i
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
(set-logic QF_AUFBV)
(declare-const bv_58-0 (_ BitVec 4))
(check-sat)
(declare-const arr1 (Array (_ BitVec 4) Bool))
(check-sat)
(assert (xor false true false true true true true true true (select arr1 bv_58-0)))
(check-sat)
(assert (select arr1 (bvxor bv_58-0 bv_58-0 bv_58-0 (bvlshr bv_58-0 bv_58-0))))
(check-sat)
