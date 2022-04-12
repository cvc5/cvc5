(set-logic QF_S)
(set-info :status unsat)

(declare-fun xx () String)
(declare-fun yy () String)
(declare-fun zz () String)
(declare-fun ww () String)
(declare-fun pp () String)
(declare-fun qq () String)

(assert (= (str.++ xx yy zz) (str.++ ww qq)))
(assert (= ww (str.++ xx pp)))
(assert (= yy pp))
(assert (not (= zz qq)))

(check-sat)
