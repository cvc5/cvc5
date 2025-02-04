; COMMAND-LINE: --dt-stc-ind --conjecture-gen
; DISABLE-TESTER: unsat-core
; EXPECT: unsat
(set-logic UFDT)
(declare-datatypes ((Nat 0)) (((Z) (S (proj1-S Nat)))))
(declare-datatypes ((list 0)) (((nil) (cons (head Nat) (tail list)))))
(define-fun-rec len ((x list)) Nat
  (match x
    (((nil) Z)
     ((cons h t) (S (len t))))))
(define-fun-rec <=2 ((x Nat) (y Nat)) Bool
  (match x
    (((S px) (match y
               (((S py) (<=2 px py))
                ((Z) false))))
     ((Z) true))))
(define-fun-rec insort ((x Nat) (y list)) list
  (match y
    (((cons h t) (ite (<=2 x h) (cons x (cons h t))
                                (cons h (insort x t))))
     ((nil) (cons x nil)))))
(define-fun-rec sort ((x list)) list
  (match x
    (((cons h t) (insort h (sort t)))
     ((nil) nil))))
(assert
 (not
  (forall ((xs list))
    (= (len (sort xs)) (len xs)))))
(check-sat)
