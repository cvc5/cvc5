; EXPECT: unsat
;; FP is not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic QF_FP)
(declare-const x Float32)
(assert (not (= x (fp.neg (fp.neg x)))))
(check-sat)
