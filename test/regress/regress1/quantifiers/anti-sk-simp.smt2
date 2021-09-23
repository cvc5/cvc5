; COMMAND-LINE: --sygus-inference
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun f (Int) Int)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (forall ((X Int)) (< X (f X))))
(assert (forall ((X Int)) (> (+ a b) (f X))))
(check-sat)
