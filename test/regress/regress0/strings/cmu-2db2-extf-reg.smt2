(set-logic ALL_SUPPORTED)
(set-info :status sat)
(set-option :strings-exp true)

(declare-fun s () String)

(assert (and (not (not (= (ite (= (str.indexof s "bar" 1) (- 1)) 1 0) 0))) (not (not (= (ite (= (str.indexof s "bar" 1) 3) 1 0) 0)))))

(check-sat)
