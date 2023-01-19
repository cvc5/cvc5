(declare-fun a () String)
(assert (not (= "B" (str.replace "B" (str.replace "B" a "B") a))))
(check-sat)
