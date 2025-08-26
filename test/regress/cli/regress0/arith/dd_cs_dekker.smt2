; EXPECT: unsat
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-fun o () Int)
(declare-fun d () Int)
(assert (<= d o))
(assert (>= d o))
(assert (<= o 0))
(assert (>= o 0))
(assert (= 1 (mod d 2)))
(check-sat)
