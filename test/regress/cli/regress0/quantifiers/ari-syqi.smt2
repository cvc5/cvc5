; COMMAND-LINE: --sygus-inst --no-cegqi
; EXPECT: unsat
(set-logic BV)
(set-info :status unsat)
(assert (not (exists ((?X (_ BitVec 32))) (not (= ?X (_ bv12 32))))))
(check-sat)
(exit)
