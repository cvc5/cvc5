(set-logic QF_NIA)
(set-info :status unsat)
(declare-fun ld () Int)
(declare-fun d () Int)
(declare-fun ud () Int)
(declare-fun ln () Int)
(declare-fun n () Int)
(declare-fun un () Int)
(define-fun sgn ((x Int)) Int (ite (< x 0) (- 1) (ite (> x 0) 1 0)))

(assert (<= ld d ud))
(assert (<= ln n un))

(assert (< (abs ln) (abs ld)))
(assert (< (abs ln) (abs ud)))
(assert (< (abs un) (abs ld)))
(assert (< (abs un) (abs ud)))

(assert (= (sgn ld) (sgn ud)))
(assert (= (sgn ln) (sgn un)))

(assert (not (= (mod n d) (ite (< n 0) (+ (abs d) n) n))))

(check-sat)
