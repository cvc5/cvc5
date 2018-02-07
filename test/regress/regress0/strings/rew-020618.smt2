(declare-fun s () String)

(assert (or
(= (str.++ s "A") "")
(= (str.++ s s) "A")
)
)
(check-sat)