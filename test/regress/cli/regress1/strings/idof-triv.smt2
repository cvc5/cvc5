(set-logic ALL)
(set-info :status sat)

(declare-fun string () String)
;(assert (= string "::")) 
(assert (> (str.indexof string ":" 0) 0))
(check-sat)
