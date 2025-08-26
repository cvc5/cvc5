; COMMAND-LINE: --dt-stc-ind
; EXPECT: unsat
(set-logic UFDT)
(declare-datatype Nat ((zero) (succ (pred Nat))))
(declare-datatype Lst ((nil) (cons (head Nat) (tail Lst))))
(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x) ))
(assert (forall ((x Nat) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z))) ))
(declare-fun rev (Lst) Lst)
(assert (= (rev nil) nil))
(assert (forall ((x Nat) (y Lst)) (= (rev (cons x y)) (append (rev y) (cons x nil))) ))
(assert (not (forall ((x Lst) (y Nat)) (= (rev (append (append x (cons y nil)) nil)) (cons y (rev (append x nil)))))))
(check-sat)
