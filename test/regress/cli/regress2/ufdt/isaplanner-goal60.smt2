; COMMAND-LINE: --dt-stc-ind --conjecture-gen
; DISABLE-TESTER: unsat-core
; EXPECT: unsat
(set-logic UFDT)
(declare-datatype Nat ((zero) (succ (pred Nat))))
(declare-datatype Lst ((nil) (cons (head Nat) (tail Lst))))
(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Nat) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))
(declare-fun last (Lst) Nat)
(assert (forall ((x Nat) (y Lst)) (= (last (cons x y)) (ite (= y nil) x (last y)))))
(assert (not (forall ((xs Lst) (ys Lst)) (=> (= ys nil) (= (last (append xs ys)) (last xs))))))
(check-sat)
