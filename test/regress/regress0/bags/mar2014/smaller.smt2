; EXPECT: sat
; COMMAND-LINE: --simplification=none

; demostrates core issue with UniqueZipper.hs.1030minimized.cvc4.smt2
; fails check-model, even though answer is correct

(set-logic ALL)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun a () (Bag Int))
(declare-fun b () (Bag Int))
(assert (>= (bag.count x (bag.union_disjoint a b)) 1))
(assert (not (>= (bag.count y a) 1)))
(assert (= x y))
(check-sat)
