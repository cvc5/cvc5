(set-logic ALL)
(set-info :status unsat)
(set-option :strings-exp true)
 
(declare-fun s () String)
(assert (or (= s "Id like cookies.") (= s "Id not like cookies.")))
 
(declare-fun target () String)
(assert (or (= target "l") (= target "m")))
 
(declare-fun location () Int)
(assert (= (* 2 location) (str.indexof s target 0)))
 
(check-sat)