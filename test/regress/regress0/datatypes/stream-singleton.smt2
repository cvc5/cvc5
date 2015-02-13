(set-logic QF_ALL_SUPPORTED)
(set-info :status unsat)

(declare-codatatypes () ((Stream (S (s Stream)))))

(declare-fun x () Stream)
(declare-fun y () Stream)

(assert (not (= x y)))

(check-sat)