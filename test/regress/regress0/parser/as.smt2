(set-logic QF_UF)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)
(declare-sort I 0)
(declare-fun e0 () I)

;; as was badly parsed in default case
;; no specialization (emptyset) just dumb type-checking

(assert (= (as e0 I) (as e0 I)))

(check-sat)
(exit)
