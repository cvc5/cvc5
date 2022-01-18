; EXPECT: unsat
; COMMAND-LINE: --simplification=none

; demostrates core issue with UniqueZipper.hs.1030minimized.cvc4.smt2
; unlike original benchmark, this is unsat.

(set-logic QF_UFLIAFS)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun a () (Set Int))
(declare-fun b () (Set Int))
(assert (set.member x (set.union a b)))
(assert (not (set.member y a)))
(assert (not (set.member z b)))
(assert (= z y))
(assert (= x y))
(check-sat)
