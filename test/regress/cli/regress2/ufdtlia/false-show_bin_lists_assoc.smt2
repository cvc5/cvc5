; COMMAND-LINE: --dt-stc-ind --conjecture-gen
; DISABLE-TESTER: unsat-core
; EXPECT: unsat
(set-logic UFDTLIA)
(declare-datatype B ((I) (O)))
(declare-datatype list ((nil) (cons (head B) (tail list))))
(define-fun half ((x Int)) Int
  (div x 2))
(define-fun-rec shw ((x Int)) list
  (ite (= x 0) nil
  (ite (= (mod x 2) 0) (cons O (shw (half x))) 
                       (cons I (shw (half x))))))
(define-fun double ((x Int)) Int 
  (+ x x))
(define-fun-rec rd ((x list)) Int
  (match x
    (((cons h t) (match h
                   (((O) (double (rd t)))
                    ((I) (+ 1 (double (rd t)))))))
     ((nil) 0))))
(define-fun-rec ++ ((x list) (y list)) list
  (match x
    (((cons h t) (cons h (++ t y)))
     ((nil) y))))
(define-fun hash ((x Int) (y Int)) Int
  (rd (++ (shw x) (shw y))))
(assert                                         
 (not                                          
  (forall ((x Int) (y Int) (z Int))           
    (= (hash x (hash y z)) (hash (hash x y) z)))))
(check-sat)
