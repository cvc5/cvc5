; COMMAND-LINE: --sygus-inst
; EXPECT: unsat
(set-logic ALL)
(declare-sort a 0)
(declare-datatypes ((t 0)) (((L (s a)))))
(declare-datatypes ((l 0)) (((N))))
(declare-fun i (t l) l)
(assert (forall ((u t)) (forall ((t l)) (distinct N (i u N)))))
(check-sat)
