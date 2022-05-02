(set-logic QF_UF)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status sat)
(declare-sort I 0)
(declare-fun e0 () I)

;; below we type cast e0 to its type
;; in other words, this just affirms that e0 has type I
;; previously, this was not handled correctly in the smt2 parser
(assert (= (as e0 I) (as e0 I)))

(check-sat)
(exit)
