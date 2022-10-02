; EXPECT: sat
; COMMAND-LINE: --simplification=none

; demostrates core issue with UniqueZipper.hs.1030minimized.cvc4.smt2
; fails check-model, even though answer is correct

(set-logic QF_UFLIAFS)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun a () (Set Int))
(declare-fun b () (Set Int))
(assert (set.member x (set.union a b)))
(assert (not (set.member y a)))
(assert (= x y))
(check-sat)
