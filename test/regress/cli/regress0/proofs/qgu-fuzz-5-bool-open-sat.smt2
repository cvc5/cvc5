; COMMAND-LINE: --proof-check=eager
; EXPECT: unsat
(set-logic ALL)
(declare-const x Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(assert (and (ite c x false) (ite (or x d) (not b) x) (ite d (= b (ite b true d)) b)))
(check-sat)
