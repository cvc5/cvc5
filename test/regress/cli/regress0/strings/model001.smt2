(set-logic QF_S)
(set-info :status sat)
(set-option :produce-models true)

(declare-fun x () String)
(declare-fun y () String)

(assert (not (= x y)))
(assert (= (str.len x) (str.len y)))

(check-sat)
;(get-model)
