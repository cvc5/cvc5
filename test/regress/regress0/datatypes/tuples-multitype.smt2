; EXPECT: sat
(set-logic ALL)
(set-info :status sat)

(declare-fun t () (Tuple Int String))
(declare-fun i () String)

(assert (= t (mkTuple 0 "0")))
(assert (= i ((_ tupSel 1) t)))

(check-sat)
