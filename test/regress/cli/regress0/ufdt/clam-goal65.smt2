; COMMAND-LINE: --dt-stc-ind
; EXPECT: unsat
(set-logic UFDT)
(declare-datatype Nat ((succ (pred Nat)) (zero)))
(declare-datatype Lst ((cons (head Nat) (tail Lst)) (nil)))
(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x) ))
(assert (forall ((x Nat) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z))) ))
(declare-fun len (Lst) Nat)
(assert (= (len nil) zero))
(assert (forall ((x Nat) (y Lst)) (= (len (cons x y)) (succ (len y))) ))
(assert (not (forall ((w Lst) (x Nat) (y Nat) (z Lst)) (= (len (append w (cons x (cons y z)))) (succ (succ (len (append w z))))) )))
(check-sat)
