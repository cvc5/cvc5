; COMMAND-LINE: --cegqi
; EXPECT: unsat
(set-logic ALL)
(declare-datatypes ((List 0)) (((cons (head Int) (tail List)) (nil))))
(assert (exists ((y Int)) (forall ((x List)) (not (= (head x) (+ y 7))))))
(check-sat)
