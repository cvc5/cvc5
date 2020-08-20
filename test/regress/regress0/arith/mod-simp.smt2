(set-logic QF_LIA)
(set-info :status unsat)

(declare-fun x () Int)

(assert (not (= (mod (* 3 x) 10) (mod (* 3 (+ x 10)) 10))))

(check-sat)
