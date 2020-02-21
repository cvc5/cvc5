(set-logic QF_SLIA)
(set-info :status unsat)

(declare-fun xx () String)
(declare-fun yy () String)
(declare-fun zz () String)
(declare-fun ww () String)
(declare-fun pp () String)
(declare-fun qq () String)

; Morgan says it needs length bound
(assert (> (str.len yy) (str.len xx)))
(assert (= xx (str.++ xx yy)))

(check-sat)
