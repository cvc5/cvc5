; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (= (str.rev "ABC") "CBA"))
(assert (= (str.rev "") ""))
(assert (= (str.rev "A") x))
(assert (= (str.rev (str.++ x y)) "BCA"))
(assert (= (str.rev y) "BC"))
(check-sat)
