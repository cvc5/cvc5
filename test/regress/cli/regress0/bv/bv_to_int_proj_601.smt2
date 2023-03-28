; EXPECT: unsat
(set-logic ALL)
(set-option :check-proof-steps true)
(set-option :solve-bv-as-int sum)
(define-fun f ((_f18_0 Bool) (_f18_1 Bool)) Bool _f18_0)
(define-fun _f ((_f19_0 (_ BitVec 68))) (_ BitVec 68) _f19_0)
(assert (f false false))
(check-sat)

