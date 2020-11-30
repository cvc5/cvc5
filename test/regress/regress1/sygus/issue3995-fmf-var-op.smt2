; EXPECT: unsat
; COMMAND-LINE: --sygus-inference --fmf-bound --uf-ho
(set-logic ALL)
(declare-fun a () (_ BitVec 1))
(assert (bvsgt (bvsmod a a) #b0))
(check-sat)
