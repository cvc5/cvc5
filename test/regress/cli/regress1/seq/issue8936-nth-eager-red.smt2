; COMMAND-LINE: --strings-exp --no-strings-lazy-pp
; EXPECT: unsat
(set-logic ALL)
(declare-fun a () (Seq Int))
(declare-fun b () (Seq Int))
(declare-fun c () Int)
(assert (= a b))
(assert (not (= (seq.nth a c) (seq.nth b c))))
(check-sat)
