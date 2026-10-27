; COMMAND-LINE: --enum-inst
; EXPECT: unsat
(set-logic ALL)
(declare-fun t () Int)
(declare-fun ss (Int Int Int) Int)
(declare-fun s (Int Int Int Int Int) Int)
(declare-fun _1 (Int Int) Int)
(assert (and (forall ((x Int) (? Int)) (! (= 0 (_1 1 x)) :pattern ((s 0 0 x 0 ?)))) (forall ((? Int) (y Int)) (! (= (_1 0 0) (- ? (* y (_1 ? 0)))) :pattern ((_1 ? y)) :pattern ((_1 0 0))))))
(assert (and (= 0 (_1 t 1)) (= 0 (s 0 0 2 0 (ss 0 0 0)))))
(check-sat)
