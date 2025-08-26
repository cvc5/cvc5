; COMMAND-LINE: --strings-deq-ext --enum-inst
; EXPECT: unsat
(set-logic ALL)
(declare-const s String)
(declare-const t String)
(assert (= (str.len s) (str.len t) 1))
(assert (not (= s t)))
(assert (forall ((x Int)) (= (str.substr s x 1) (str.substr t x 1))))
(check-sat)
