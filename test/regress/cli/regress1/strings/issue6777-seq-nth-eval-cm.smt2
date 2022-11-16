; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :strings-lazy-pp false)
(set-option :check-unsat-cores true)
(declare-fun b () (Seq Int))
(declare-fun y () Int)
(declare-fun l () Bool)
(assert (distinct (seq.nth b y) (seq.nth b 1)))
(assert (= l (> y 2)))
(check-sat)
