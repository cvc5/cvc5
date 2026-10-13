; REQUIRES: unrestricted-mode
; DISABLE-TESTER: model
; EXPECT: sat
(set-logic ALL)
(declare-const x (Array Int Int))
(declare-const x7 Int)
(declare-fun x8 (Int) Int)
(check-sat-assuming (((_ divisible 3) (select (store (store (store (store x 0 (int.pow2 1)) (int.pow2 x7) (int.pow2 0)) 76044041 0) (+ x7 (int.pow2 0)) (int.pow2 0)) (x8 (int.pow2 0))))))
