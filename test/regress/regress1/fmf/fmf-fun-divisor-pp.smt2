; COMMAND-LINE: --fmf-fun
; EXPECT: unsat
(set-logic UFNIA)
(set-info :status unsat)
(define-fun-rec pow ((a Int)(b Int)) Int 
    (ite (<= b 0) 
         1 
         (* a (pow a (- b 1)))))

(declare-fun x () Int)

(assert (>= x 0))
(assert (< x (pow 2 2)))
(assert (>= (mod (div x (pow 2 3)) (pow 2 2)) 2))

(check-sat)
