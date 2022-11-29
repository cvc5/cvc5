; COMMAND-LINE: --ieval=use
; EXPECT: unsat
(set-logic ALL)
(declare-const x9 Bool)
(declare-fun p () Int)
(declare-fun s4 (Int) Bool)
(declare-fun s (Int) Bool)
(declare-fun x (Int Int) Bool)
(assert (and (forall ((? Int)) (or (s p))) (forall ((q Int)) (not (x p q))) (forall ((q Int)) (or (x p q))) (forall ((? Int)) (or (s4 0) (s 0))) (or x9 (exists ((? Int)) (or (x 0 0))))))
(check-sat)
