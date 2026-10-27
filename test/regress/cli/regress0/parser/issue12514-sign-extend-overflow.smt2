; DISABLE-TESTER: dump
; SCRUBBER: grep -o 'resulting bit-vector size is too large'
; EXPECT: resulting bit-vector size is too large
; EXIT: 1
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(assert (= ((_ sign_extend 4294967295) x) ((_ sign_extend 4294967295) x)))
(check-sat)
