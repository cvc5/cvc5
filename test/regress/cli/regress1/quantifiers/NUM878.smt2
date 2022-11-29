; DISABLE-TESTER: lfsc
; COMMAND-LINE: --cegqi-bv
; EXPECT: unsat
(set-logic BV)
(set-info :status unsat)
(assert (not (exists ((?X (_ BitVec 32))) (= (bvmul ?X ?X) ?X))))
(check-sat)
(exit)
