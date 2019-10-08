(set-logic ALL)
(set-info :status unsat)
(declare-fun a () Real)   
(assert 
    (and  
        (and 
            (exists ((?b Real)) (forall ((?c Real)) (exists ((?d Real)) 
            (or  (and  (and  (and (and (< (+ (+ (+ 0 (* 68.0 ?c)) 0) (* 33.0 a)) 0.0) (<= 0 2.0)) 
            (or (<= 0 (+  (*  (+ (* 55.0 ?d) 0) (* 49.0 ?b)) 0))))))))))
        )
    )
) 

(check-sat)
