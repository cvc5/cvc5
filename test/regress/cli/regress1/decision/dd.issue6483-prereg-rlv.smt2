; COMMAND-LINE: --preregister-mode=rlv
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun a () String)
(assert (not (= "B" (str.replace "B" (str.replace "B" a "B") a))))
(check-sat)
