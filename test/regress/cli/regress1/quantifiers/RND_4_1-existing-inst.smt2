(set-logic LRA)
(set-info :status unsat)
(declare-fun a () Real)
(assert 
  (forall ((?y2 Real) (?y3 Real)) 
    (or 
        (= ?y3 1) 
        (> ?y3 0)
        (and 
          (< ?y2 0) 
          (< ?y3 49) 
        )))
)
(check-sat)
(exit)
