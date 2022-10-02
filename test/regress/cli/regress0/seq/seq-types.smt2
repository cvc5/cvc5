; COMMAND-LINE: --strings-exp
;EXPECT: unsat
(set-logic ALL)
(declare-fun s () (Seq Int))
(declare-fun n () Int)
(assert (= 5 (seq.nth s n)))
(assert (< n (seq.len s)))
(assert (> n 0))
(assert (= (seq.unit 6) (seq.at s n)))
(check-sat)

