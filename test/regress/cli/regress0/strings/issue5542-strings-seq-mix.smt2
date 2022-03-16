; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () (Seq Int))
(assert (distinct b (str.++ a a)))
(assert (distinct (seq.unit 0) (seq.extract c 1 1)))
(assert (= (seq.len c) 1))
(check-sat)
