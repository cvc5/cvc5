; COMMAND-LINE: --dt-stc-ind
; EXPECT: unsat
(set-logic UFDT)
(declare-datatype Nat ((zero) (succ (pred Nat))))
(declare-datatype Lst ((nil) (cons (head Nat) (tail Lst))))
(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Nat) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))
(declare-fun count (Nat Lst) Nat)
(assert (forall ((x Nat) (y Nat) (z Lst)) (= (count x (cons y z)) (ite (= x y) (succ (count x z)) (count x z)))))
(assert (not (forall ((n Nat) (x Lst)) (= (count n (append x (cons n nil))) (succ (count n x))))))
(check-sat)