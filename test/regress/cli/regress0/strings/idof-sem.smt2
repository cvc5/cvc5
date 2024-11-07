(set-logic SLIA)

(set-info :status sat)
(declare-fun x () String)
(assert (not (= (str.indexof x "" 0) (- 1))))
(check-sat)
