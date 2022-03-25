; COMMAND-LINE: --full-saturate-quant
; EXPECT: unsat
(set-logic LRA)
(set-info :status unsat)
(declare-fun x4 () Real)
(declare-fun x3 () Real)
(assert (forall ((?lambda Real)) 

(let ((?v_26 (* (- 1) x4))) 
(let ((?v_28 (+ ?lambda (* (/ 3 40) x4)))) 
 
(and 
(<= (+ ?lambda (* (/ 1 60) x4)) (/ 400 3)) 
(<= (+ (* (- 1) ?lambda) (* (/ (- 1) 60) x4)) (/ (- 731) 6))
(<= ?v_28 610) 
(<= ?v_28 359) 
(<= ?v_26 (- 4100)) 
(<= ?v_26 (- 4500)) 
(<= ?v_26 (- 4910)) 
))
 
 )))
(check-sat)
(exit)
