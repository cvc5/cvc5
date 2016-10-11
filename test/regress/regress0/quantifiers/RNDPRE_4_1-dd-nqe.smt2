; COMMAND-LINE: --cbqi-nested-qe
; EXPECT: unsat
(set-logic LRA)

(declare-fun c () Real)

(assert 
(forall ((?x2 Real)) 
(exists ((?x3 Real)) 
(and
(forall ((?x4 Real)) (or 
(not (>= ?x4 4)) 
(and (> c (+ ?x2 ?x3)) (> (+ c ?x3 ?x4) 0))) )
(not (> (+ c ?x2 ?x3) 0)) )
)) )

(check-sat)
(exit)
