; EXPECT: sat
; COMMAND-LINE: --simplfication=none

; demostrates core issue with UniqueZipper.hs.1030minimized.cvc4.smt2
; fails check-model, even though answer is correct

(set-logic QF_UFLIA_SETS)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun a () (Set Int))
(declare-fun b () (Set Int))
(assert (in x (union a b)))
(assert (not (in y a)))
(assert (= x y))
(check-sat)
