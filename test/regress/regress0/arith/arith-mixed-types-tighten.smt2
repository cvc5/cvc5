; COMMAND-LINE:
; EXPECT: unsat
(set-logic QF_LIRA)

(declare-fun x_44 () Real)
(declare-fun x_45 () Real)

; This test is a subset of one of the `../lemmas` tests. I think `../lemmas/sc_init_frame_gap.induction.smtv1.smt2`.
(declare-fun termITE_30 () Int)
(declare-fun termITE_3 () Real)
(declare-fun termITE_4 () Real)
(declare-fun termITE_8 () Real)
(declare-fun termITE_9 () Real)
(declare-fun termITE_31 () Int)

(assert
    (let ((_let_0 (* (- 1.0) termITE_3)))
        (and
            (>= (+ termITE_8 (* (- 1.0) termITE_9)) 0.0)
            ; This literal can be tightened to `termITE_31 <= 1`.
            (not (>= termITE_31 2))
            (>= (+ (* (- 1.0) x_44) (/ termITE_31 1)) 0.0)
            (>= (+ x_44 (* (- 1.0) termITE_4)) 0.0)
            (not (>= (+ _let_0 (* (/ 1 2) termITE_8)) 0.0))
            (>= (+ (* (- 1.0) x_45) termITE_9) 0.0)
            (>= (+ x_45 (/ (* (- 1) termITE_30) 1)) 0.0)
            (>= termITE_30 2)
            (>= (+ _let_0 termITE_4) 0.0)))
)

(check-sat)

