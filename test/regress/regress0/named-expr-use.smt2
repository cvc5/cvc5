(set-logic QF_LIA)
(set-info :status sat)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (or (! (= x y) :named foo) (= x 5)))

(assert (or foo (= x 7)))

(check-sat)
