; COMMAND-LINE: --dt-stc-ind
; EXPECT: unsat
(set-logic UFDT)
(declare-datatype Nat ((succ (pred Nat)) (zero)))
(declare-datatype Lst ((cons (head Nat) (tail Lst)) (nil)))
(define-fun-rec plus ((m Nat) (n Nat)) Nat
  (match m
    (((zero) n)
     ((succ pm) (succ (plus pm n))))))
(define-fun-rec len ((l Lst)) Nat
  (match l
    (((nil) zero)
     ((cons h t) (succ (len t))))))
(declare-fun qreva (Lst Lst) Lst)
(assert (forall ((x Lst) (y Lst)) (= (len (qreva x y)) (plus (len x) (len y)))))
(assert (not (forall ((x Lst)) (= (len (qreva x nil)) (len x)))))
(check-sat)
