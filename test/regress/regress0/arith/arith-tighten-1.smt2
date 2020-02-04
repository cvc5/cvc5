; COMMAND-LINE: --no-check-unsat-cores --no-check-proofs
; EXPECT: unsat
(set-logic QF_LIRA)

(declare-fun n () Int)

; tests tightenings of the form [Int] >= r   to [Int] >= ceiling(r)
; where r is a real.
(assert
    (and
        (>= n 1.5)
        (<= n 1.9)
    )
)

(check-sat)

