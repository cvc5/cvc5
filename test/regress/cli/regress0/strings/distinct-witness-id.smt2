; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (= (str.len x) 999999999999999999999999))
(assert (= (str.len y) 999999999999999999999999))
(assert (= z (str.++ x y)))
(check-sat)
