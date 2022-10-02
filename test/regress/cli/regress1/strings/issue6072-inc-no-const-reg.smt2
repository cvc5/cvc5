; COMMAND-LINE: -i --strings-exp
; EXPECT: sat
; EXPECT: sat
(set-logic ALL)
(declare-fun i4 () Int)
(declare-fun str5 () String)
(assert (= (str.++ str5 (str.from_int i4)) (str.++ "15" str5 "1")))
(push)
(check-sat)
(pop)
(check-sat)
