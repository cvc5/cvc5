; EXPECT: unsat
(set-logic QF_FP)
(declare-const r RoundingMode)
(assert (distinct ((_ to_fp_unsigned 8 24) r (_ bv0 1)) (fp (_ bv0 1) (_ bv0 8) (_ bv0 23))))
(check-sat)
