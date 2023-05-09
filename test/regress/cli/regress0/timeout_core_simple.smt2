; EXPECT: unsat
; EXPECT: (
; EXPECT: c
; EXPECT: )
(set-logic ALL)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (! (> x 0) :named a))
(assert (! (< y 0) :named b))
(assert (! false :named c))
(get-timeout-core)
