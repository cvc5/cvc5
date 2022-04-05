; EXPECT: unsat
; COMMAND-LINE: --sygus-inference --fmf-bound
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic HO_ALL)
(declare-fun a () (_ BitVec 1))
(assert (bvsgt (bvsmod a a) #b0))
(check-sat)
