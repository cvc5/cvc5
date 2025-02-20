; COMMAND-LINE: --sygus-inst --arrays-exp
; EXPECT: unsat
(set-logic ALL)
(assert (forall ((v (Array (_ BitVec 1) Bool))) (select v (_ bv0 1))))
(check-sat)
