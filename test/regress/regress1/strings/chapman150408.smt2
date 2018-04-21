(set-logic SLIA)
(set-info :status sat)
(set-option :strings-exp true)
(set-option :rewrite-divk true)
(declare-fun string () String)
(assert (and
     (and (not (not (not (= (ite (> (str.indexof string ";" 0) 0) 1 0)
     0)))) (not (= (ite (not (= (str.len string) 0)) 1 0) 0))) (not
     (not (= (ite (str.contains string "]") 1 0) 0)))))
(check-sat)
