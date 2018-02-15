; COMMAND-LINE: --simplification=none --strings-exp --no-strings-lazy-pp
; EXPECT: sat
(set-logic SLIA)
(set-info :status sat)
(declare-fun x () String)
(declare-fun f () String)
(declare-fun y () Int)
(assert (= (str.len f) 0))
; command line options ensure reduction is invoked for indexof, f is "", should return -1
(assert (= (str.indexof x f 4) y))
(check-sat)
