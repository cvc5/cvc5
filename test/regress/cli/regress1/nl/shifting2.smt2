; COMMAND-LINE: --nl-ext=full
; EXPECT: unsat
(set-logic QF_NIRA)
(set-info :status unsat)
(declare-fun pi () Real)

(assert (and (< 3.0 pi) (< pi 3.5)))

(declare-fun y () Real)
(assert (and (< (- pi) y) (< y pi)))

(declare-fun s () Int)

(declare-fun z () Real)

(assert (= z (+ y (* 2.0 pi (to_real s)))))

(assert (and (< (- pi) z) (< z pi)))

(assert (not (= z y)))

(check-sat)
