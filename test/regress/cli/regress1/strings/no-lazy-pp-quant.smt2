; COMMAND-LINE: --strings-exp --no-strings-lazy-pp
; EXPECT: sat
(set-info :smt-lib-version 2.6)
(set-logic ALL)
(set-info :status sat)
(declare-fun result () Int)
(declare-fun s () String)
(assert (! (not (= (str.to_int s) result)) :named a0))
(check-sat)
