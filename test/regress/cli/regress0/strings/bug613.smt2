(set-logic QF_SLIA)
(set-info :status sat)


(declare-fun s () String)
(assert (= s "<a></a>"))
(assert (< (str.indexof s "<a>" 0) (str.indexof s "</a>" 0)))

(check-sat)
