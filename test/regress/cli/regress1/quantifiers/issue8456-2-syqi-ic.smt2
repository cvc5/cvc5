; COMMAND-LINE: --sygus-inst
; EXPECT: unsat
(set-logic ALL)
(assert (and (forall ((v (Array (_ BitVec 1) Bool))) (select v (_ bv0 1)))))
(check-sat)
