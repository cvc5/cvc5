(set-logic QF_LIA)
(set-info :status unsat)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (or (= x 5) (= x 7)))
(assert (or (! (= x 5) :named foo) (= x y)))

(assert (= foo (= x 7)))

(check-sat)
