(set-logic QF_S)
(set-info :status unsat)

(declare-fun xx () String)
(declare-fun yy () String)
(declare-fun zz () String)
(declare-fun ww () String)
(declare-fun pp () String)
(declare-fun qq () String)

(assert (= "ab" (str.++ "a" xx)))
(assert (not (= xx yy)))
(assert (= "b" yy))

(check-sat)
