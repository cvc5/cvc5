; REQUIRES: unrestricted-mode
; EXPECT: unsat
; COMMAND-LINE: --sygus-inference=try --fmf-bound
; --sygus-inference is not supported with full proofs.
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic HO_ALL)
(declare-fun a () (_ BitVec 1))
(assert (bvsgt (bvsmod a a) #b0))
(check-sat)
