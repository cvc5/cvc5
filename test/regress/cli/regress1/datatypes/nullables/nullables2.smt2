; DISABLE-TESTER: cpc
(set-logic ALL)
(set-info :status unsat)
(set-option :produce-models true)
(declare-fun x () (Nullable Int))
(declare-fun y () (Nullable Int))
(assert (= (nullable.some x) (nullable.some y)))
(assert (distinct x y))
(check-sat)
