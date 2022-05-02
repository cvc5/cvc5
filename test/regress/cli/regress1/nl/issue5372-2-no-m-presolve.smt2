; COMMAND-LINE: -i
; EXPECT: sat
; EXPECT: unsat
(set-logic ALL)
(declare-fun i4 () Int)
(declare-fun i6 () Int)
(declare-fun i7 () Int)
(assert (= true true true (< i7 (* i4 i4)) true true true true))
(check-sat)
(assert (< i6 (* 51 51 i4 i6) 0 74))
(check-sat)
