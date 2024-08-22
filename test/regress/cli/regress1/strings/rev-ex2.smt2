; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (= x (str.rev (str.++ y "A"))))
(assert (> (str.len x) (+ (str.len y) 1)))
(check-sat)
