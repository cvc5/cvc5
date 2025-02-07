; COMMAND-LINE: --dt-stc-ind --conjecture-gen
; DISABLE-TESTER: unsat-core
; EXPECT: unsat
(set-logic UFLIA)
(define-fun-rec mult ((m Int) (n Int)) Int
  (ite (> n 0) (+ m (mult m (- n 1)))
               0))
(assert
 (forall ((m Int) (n Int))
   (= (- (mult m n) n) (mult (- m 1) n))))
(assert
 (not
  (forall ((m Int) (n Int))
    (= (mult m n) (mult n m)))))
(check-sat)
