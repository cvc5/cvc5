; COMMAND-LINE: --check-proofs
; EXPECT: unsat
(set-logic QF_UF)
(declare-const x Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(assert (and (ite c x false) (ite (= x b) (not b) x) (ite d (= b (ite b true d)) b)))
(check-sat)
