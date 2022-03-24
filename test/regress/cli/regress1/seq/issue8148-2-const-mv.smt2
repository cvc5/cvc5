; COMMAND-LINE: --strings-exp -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(assert (forall ((V Int)) (= 0 (seq.nth (seq.unit 0) 1))))
(check-sat)
