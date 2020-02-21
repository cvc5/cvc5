; COMMAND-LINE: --strings-exp --no-strings-lazy-pp
; EXPECT: sat
(set-info :smt-lib-version 2.5)
(set-logic ALL)
(set-info :status sat)
(declare-fun result () Int)
(declare-fun s () String)
(assert (! (not (= (str.to.int s) result)) :named a0))
(check-sat)
