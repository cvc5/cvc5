(set-logic QF_NIA)
(set-info :status unsat)
(declare-fun i () Int)
(declare-fun n () Int)
(declare-fun s () Int)

(assert (and 
(= i (+ (* (- 2) s) (* i i))) 
(>= (+ i (* (- 1) n)) 1) 
(not (>= (+ i (* (- 1) n)) 2))
))
(assert (not (= n (+ (* 2 s) (* (- 1) (* n n))))))

(check-sat)
