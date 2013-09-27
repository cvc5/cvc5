(set-logic QF_S)
(set-info :status unsat)

(declare-fun xx () String)
(declare-fun yy () String)
(declare-fun zz () String)
(declare-fun ww () String)
(declare-fun pp () String)
(declare-fun qq () String)

; common postfix
;(assert (= (str.++ xx "aa") (str.++ xx "bb")))

(assert (= (str.len yy) 0))
(assert (not (= yy "")))

(check-sat)

