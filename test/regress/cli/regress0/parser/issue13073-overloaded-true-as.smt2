; DISABLE-TESTER: dump
; EXPECT: sat
(set-logic ALL)
(declare-const true Int)
(assert (or (as true Bool) false false))
(assert (> (as true Int) 0))
(check-sat)
