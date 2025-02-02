; COMMAND-LINE: --dt-stc-ind
; EXPECT: unsat
(set-logic UFDT)
(declare-datatype Nat ((zero) (succ (pred Nat))))
(declare-datatype Lst ((nil) (cons (head Nat) (tail Lst))))
(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Nat) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))
(declare-fun qreva (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (qreva nil x) x)))
(assert (forall ((x Lst) (y Lst) (z Nat)) (= (qreva (cons z x) y) (qreva x (cons z y)))))
(assert (not (forall ((x Lst) (y Lst) (z Lst)) (= (append (qreva x y) z) (qreva x (append y z))) )))
(check-sat)
