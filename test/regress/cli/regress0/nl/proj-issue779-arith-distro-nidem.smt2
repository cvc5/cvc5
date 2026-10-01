; EXPECT: unsat
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-fun a () Int)                                                             
(declare-fun b () Int)                                                             
(assert (< (- a (* b (/ a (- 1)))) (* (- a (+ 1 b)) (/ a (- 1)))))                 
(check-sat)
