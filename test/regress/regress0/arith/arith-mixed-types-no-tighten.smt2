; COMMAND-LINE: --no-check-models  --no-check-unsat-cores --no-check-proofs
; EXPECT: unsat
(set-logic QF_LIRA)
(set-info :smt-lib-version 2.0)

(declare-fun x () Real)
(declare-fun n () Int)

; Even though `n` is an integer, this would be UNSAT for real `n`, so the integrality can be ignored.
(assert
    (and
        (>= (+ x n) 1)
        (<= n 0)
        (<= x 0)
    )
)

(check-sat)

