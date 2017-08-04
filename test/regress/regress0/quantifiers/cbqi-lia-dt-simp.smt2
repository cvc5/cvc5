; COMMAND-LINE: --cbqi --dt-rewrite-error-sel --lang=smt2.5
; EXPECT: unsat
(set-logic ALL_SUPPORTED)
(declare-datatypes () ((List (cons (head Int) (tail List)) (nil))))
(assert (exists ((y Int)) (forall ((x List)) (not (= (head x) (+ y 7))))))
(check-sat)
