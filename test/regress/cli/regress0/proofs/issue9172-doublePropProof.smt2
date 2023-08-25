; COMMAND-LINE: --strings-exp --check-proofs --check-unsat-cores
; EXPECT: unsat
(set-logic QF_SLIA)
(declare-fun b () String)
(assert (> (ite (str.prefixof "-" b) 1 0) 1))
(assert (ite (str.prefixof "-" b) false (ite (= 0 (str.to_int (str.at b
            (+ (str.len b) (- 1))))) false true)))
(assert (= (str.len b) 1))
(check-sat)