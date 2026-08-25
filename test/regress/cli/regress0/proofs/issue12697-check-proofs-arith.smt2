; COMMAND-LINE: --check-proofs
; EXPECT: unsat
(set-logic QF_UFLIRA)
(declare-fun d (Int Int) Bool)
(assert (= 0 (- (ite (d 6 3) 3 6) (to_int (ite (d 0 0) 0.0 1.0)))))
(check-sat)
