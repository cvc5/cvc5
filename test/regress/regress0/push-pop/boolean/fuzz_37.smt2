; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: sat
(set-logic QF_LIA)
(declare-fun x0 () Bool)
(declare-fun x1 () Bool)
(assert (or (not (or (not (not x0)) (and (or x1 x0) (not x0)))) (and (and (or (and x1 x1) (and x0 x1)) (not (not x1))) (or (not (or x0 x1)) (or (not x1) (or x0 x0))))))
(check-sat)
(push 1)
(assert (or (not (and (and (or (not (not (and x1 x1))) (not (and (or x1 x0) (or x0 x1)))) (or (not (and (not x0) (and x0 x0))) (and (and (or x1 x0) (and x1 x1)) (not (not x1))))) (not (and (or (or (and x1 x0) (and x1 x1)) (not (or x1 x1))) (and (not (not x0)) (not (or x1 x1))))))) (and (not (and (or (and (and (not x0) (not x0)) (or (or x0 x1) (or x0 x1))) (not (and (or x1 x0) (and x1 x0)))) (and (not (or (not x1) (not x1))) (not (or (or x0 x1) (and x0 x0)))))) (not (or (and (or (and (and x0 x1) (or x1 x0)) (or (or x0 x1) (or x1 x1))) (and (not (not x1)) (and (not x1) (not x1)))) (not (or (not (or x0 x0)) (and (or x0 x1) (or x0 x0)))))))))
(assert (not (not (not x0))))
(assert (or (not (or (or (or (not (not (or (and (not x0) (or x0 x1)) (or (not x0) (and x1 x1))))) (not (or (and (not (or x1 x0)) (not (not x0))) (not (or (and x0 x0) (not x0)))))) (and (not (not (or (or (or x1 x1) (and x1 x1)) (or (and x1 x0) (and x0 x0))))) (not (or (and (not (and x0 x0)) (not (not x0))) (or (and (not x1) (not x0)) (or (or x0 x1) (or x1 x0))))))) (and (and (and (and (and (not (or x1 x1)) (and (not x0) (not x0))) (not (and (or x1 x1) (not x0)))) (and (not (and (and x0 x0) (or x1 x1))) (not (not (not x1))))) (or (and (or (or (not x0) (or x0 x1)) (not (and x1 x0))) (and (or (or x1 x0) (and x0 x0)) (and (and x0 x1) (or x0 x1)))) (not (not (not (or x0 x0)))))) (and (not (not (and (not (or x0 x0)) (and (not x0) (not x1))))) (and (or (and (or (not x0) (and x1 x0)) (and (and x1 x0) (or x0 x0))) (or (not (not x0)) (and (not x0) (or x0 x1)))) (and (and (not (or x1 x0)) (or (or x0 x1) (and x1 x0))) (and (or (and x1 x1) (not x1)) (or (or x1 x0) (or x0 x0))))))))) (or (and (and (not (not (or (and (not (not x1)) (and (or x1 x1) (and x1 x1))) (or (or (and x0 x1) (or x0 x0)) (or (not x0) (and x1 x1)))))) (not (and (not (and (or (or x1 x0) (not x0)) (not (not x1)))) (not (and (or (or x0 x0) (and x1 x1)) (not (or x1 x1))))))) (or (and (not (not (not (not (and x0 x1))))) (not (not (or (and (not x0) (or x0 x1)) (or (not x0) (or x0 x0)))))) (not (or (and (and (and (and x0 x1) (or x0 x1)) (or (not x0) (or x1 x0))) (not (and (and x1 x1) (and x0 x1)))) (not (not (not (or x0 x1)))))))) (not (and (or (not (not (or (not (and x0 x1)) (or (not x0) (and x0 x1))))) (and (not (not (or (or x0 x0) (or x1 x0)))) (or (or (or (or x0 x0) (and x1 x1)) (and (or x0 x1) (not x0))) (not (and (not x1) (and x1 x0)))))) (and (and (and (not (or (and x1 x0) (not x0))) (not (not (and x1 x1)))) (not (not (or (and x1 x1) (or x0 x1))))) (not (and (and (and (or x0 x0) (and x1 x1)) (not (not x0))) (not (or (and x0 x1) (and x0 x0)))))))))))
(check-sat)
(pop 1)
(assert (or x0 x1))
(check-sat)
(push 1)
(check-sat)
(push 1)
(check-sat)
(push 1)
(assert (or (not (or (and (and (and (and (and x0 x1) (and x1 x1)) (or (not x1) (not x0))) (and (or (not x1) (and x0 x1)) (not (and x0 x0)))) (and (not (not (or x1 x0))) (and (not (or x0 x0)) (and (and x1 x1) (and x1 x0))))) (not (not (not (not (not x0))))))) (not (and (not (and (or (not (and x0 x0)) (or (not x1) (not x1))) (or (or (and x0 x0) (and x0 x0)) (or (or x0 x1) (or x1 x0))))) (or (not (not (and (and x0 x1) (or x0 x0)))) (or (or (or (and x1 x0) (not x1)) (and (or x0 x0) (or x0 x0))) (and (and (or x1 x0) (or x0 x0)) (or (or x0 x1) (not x0)))))))))
(check-sat)
(push 1)
(assert (or (not (or (or (not (or (not (or (and x1 x1) (not x1))) (or (and (or x0 x0) (not x0)) (not (not x1))))) (and (not (or (and (not x0) (or x1 x1)) (and (not x0) (or x1 x1)))) (and (not (not (and x0 x1))) (and (not (not x1)) (or (not x1) (not x0)))))) (not (and (not (not (or (and x1 x0) (and x1 x0)))) (or (not (or (and x0 x0) (not x0))) (and (not (and x1 x1)) (not (not x1)))))))) (and (and (and (and (or (not (and (or x1 x0) (not x1))) (and (and (and x0 x0) (not x0)) (and (or x1 x1) (and x0 x0)))) (and (and (not (not x0)) (not (or x1 x0))) (or (or (not x0) (and x1 x1)) (not (not x0))))) (not (not (not (not (not x0)))))) (not (not (or (and (or (and x0 x1) (and x1 x0)) (or (not x1) (not x0))) (not (and (and x0 x1) (or x1 x1))))))) (or (or (or (or (not (or (not x0) (or x0 x0))) (and (not (or x1 x1)) (not (not x1)))) (not (or (and (or x1 x1) (not x1)) (and (not x0) (and x0 x1))))) (not (and (not (or (or x1 x1) (or x1 x1))) (not (or (not x0) (or x0 x1)))))) (or (or (and (or (or (not x1) (not x0)) (or (and x0 x1) (not x1))) (not (or (not x0) (not x1)))) (and (not (or (and x0 x0) (or x1 x0))) (or (not (not x0)) (or (or x1 x0) (not x0))))) (not (not (and (and (and x1 x0) (and x1 x0)) (and (not x1) (and x0 x0))))))))))
(assert (not (or (or (or (not (and (or (not x0) (and x1 x1)) (and (and x1 x1) (or x1 x0)))) (and (or (not (or x0 x0)) (and (or x1 x0) (not x0))) (not (or (or x0 x1) (not x1))))) (or (not (and (and (not x0) (or x1 x1)) (or (or x1 x0) (and x1 x1)))) (or (and (not (and x1 x1)) (not (and x0 x0))) (not (and (not x1) (and x1 x0)))))) (or (and (and (and (not (and x1 x0)) (and (not x0) (or x0 x1))) (and (or (and x0 x1) (or x0 x0)) (not (not x1)))) (or (not (or (not x0) (not x1))) (or (and (and x0 x1) (and x1 x0)) (or (or x1 x0) (or x0 x1))))) (not (or (and (or (not x1) (or x0 x0)) (and (and x0 x0) (or x0 x1))) (not (and (and x1 x1) (not x0)))))))))
(check-sat)
(push 1)
(assert (or (and (or (or x0 x0) (or x1 x0)) (or (not x0) (or x0 x0))) (and (not (or x1 x0)) (not (not x1)))))
(assert (or (or (and (and (and x0 x1) (not x0)) (and (and x0 x1) (or x0 x0))) (or (or (or x1 x1) (and x0 x0)) (not (not x1)))) (not (or (not (not x0)) (not (or x1 x0))))))
(check-sat)
(push 1)
(assert (or (or (not (not (and (not (not x0)) (or (or x0 x1) (and x0 x1))))) (and (not (and (and (or x1 x0) (and x1 x0)) (not (not x0)))) (not (and (and (and x0 x0) (and x1 x1)) (and (or x1 x0) (not x0)))))) (and (not (not (or (and (and x1 x0) (not x1)) (or (and x1 x1) (or x1 x0))))) (not (or (and (and (not x0) (not x1)) (or (and x1 x0) (or x1 x0))) (and (or (not x1) (not x1)) (or (not x1) (or x1 x0))))))))
(assert (or (and x1 x1) (not x0)))
(check-sat)
(pop 1)
(assert (or (or (or (and (not (and (or (and x1 x1) (and x1 x1)) (and (and x0 x0) (not x0)))) (not (and (not (or x0 x0)) (or (not x1) (not x0))))) (not (or (and (not (and x1 x0)) (not (or x1 x1))) (not (or (not x1) (not x0)))))) (and (not (not (or (or (or x0 x0) (not x1)) (and (or x0 x1) (or x1 x1))))) (not (not (or (or (not x1) (not x0)) (or (not x0) (not x1))))))) (or (and (and (and (not (and (and x0 x1) (and x0 x0))) (and (or (and x0 x1) (not x0)) (or (not x1) (or x1 x0)))) (or (and (not (and x1 x0)) (and (or x0 x1) (or x1 x1))) (and (or (not x1) (not x0)) (not (or x0 x1))))) (not (or (or (or (not x1) (not x0)) (not (and x0 x1))) (or (not (not x0)) (or (or x1 x0) (and x0 x0)))))) (not (and (not (and (and (or x1 x0) (not x0)) (or (or x0 x0) (not x0)))) (and (not (or (not x0) (or x0 x0))) (and (or (and x0 x1) (or x0 x0)) (not (and x1 x1)))))))))
(assert (or (and (or (and (or (and (and (or x1 x0) (not x1)) (and (and x0 x1) (not x0))) (not (or (and x1 x0) (or x0 x1)))) (and (or (not (or x0 x0)) (not (not x0))) (not (or (not x0) (or x0 x0))))) (and (not (and (and (and x1 x0) (or x1 x0)) (and (or x1 x1) (not x1)))) (not (not (not (and x1 x0)))))) (and (not (and (not (and (or x1 x1) (or x0 x0))) (not (or (or x1 x1) (and x0 x0))))) (and (or (not (not (not x0))) (not (not (or x0 x0)))) (and (or (and (or x0 x1) (and x1 x1)) (and (not x1) (and x1 x0))) (and (or (and x0 x0) (not x0)) (or (not x1) (not x0))))))) (and (not (and (or (not (and (and x0 x0) (not x0))) (not (or (and x1 x1) (not x0)))) (or (not (or (not x1) (not x0))) (or (not (and x0 x0)) (and (or x0 x1) (and x1 x1)))))) (not (not (and (not (not (or x1 x1))) (not (not (or x1 x0)))))))))
(assert (not x0))
(check-sat)
(pop 1)
(check-sat)
(pop 1)
(check-sat)
