; COMMAND-LINE: --enum-inst --ieval=use
; EXPECT: unsat
(set-logic ALL)
(declare-fun p (Int) Int)
(declare-fun H (Int Int Int) Int)
(assert (and (forall ((? Int) (z Int)) (! (= z 0) :pattern ((H ? 0 z))))))
(assert (or (exists ((? Int)) (= 0 (p 0)))))
(check-sat)
