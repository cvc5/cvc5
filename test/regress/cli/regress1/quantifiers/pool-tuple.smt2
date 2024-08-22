; COMMAND-LINE: --no-cbqi --no-e-matching
; EXPECT: unsat
; DISABLE-TESTER: unsat-core
(set-logic ALL)
(declare-pool P (Tuple Int Int) ())
(declare-pool Q Int (0 1 2))

(declare-fun f (Int Int) Bool)
(declare-fun g (Int) Bool)

(assert (forall ((x Int)) (! true :pool (Q) :inst-add-to-pool ((tuple x 7) P))))
(assert (forall ((x Int) (y Int)) (! (f x y) :pool (P))))

(assert (or (not (f 0 7)) (not (f 1 7)) (not (f 2 7))))

(check-sat)
