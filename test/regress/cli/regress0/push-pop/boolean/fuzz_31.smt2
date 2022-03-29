; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: sat
(set-logic QF_LIA)
(declare-fun x0 () Bool)
(declare-fun x1 () Bool)
(assert (not (and (and (or (and (and (or (and (and x1 x1) (and x0 x0)) (or (and x1 x0) (or x1 x0))) (or (not (and x0 x0)) (or (or x0 x1) (or x0 x1)))) (not (and (not (and x1 x1)) (or (not x0) (not x0))))) (and (or (not (not (not x0))) (and (and (or x0 x1) (and x1 x0)) (not (and x1 x1)))) (or (not (not (not x1))) (or (or (and x1 x0) (not x1)) (not (and x0 x0)))))) (not (not (or (and (and (or x1 x0) (not x0)) (not (and x1 x0))) (and (or (not x0) (and x0 x0)) (and (or x0 x0) (or x1 x1))))))) (or (or (or (or (or (or (not x0) (and x1 x0)) (not (or x0 x0))) (and (not (or x0 x1)) (or (not x1) (not x0)))) (or (and (or (or x1 x0) (and x1 x0)) (not (and x1 x0))) (and (and (not x1) (or x1 x1)) (and (not x0) (and x0 x1))))) (or (and (or (or (not x0) (not x0)) (and (not x1) (and x1 x1))) (or (or (and x1 x1) (not x1)) (and (or x0 x1) (and x0 x1)))) (and (and (and (not x1) (not x0)) (or (or x0 x1) (or x1 x0))) (and (or (and x0 x0) (or x0 x1)) (or (or x1 x0) (and x1 x1)))))) (and (not (and (or (not (and x1 x1)) (or (and x0 x1) (not x1))) (not (and (not x1) (or x0 x0))))) (and (not (not (and (not x1) (not x0)))) (not (and (or (not x0) (and x1 x1)) (not (and x1 x0))))))))))
(check-sat)
(push 1)
(assert (not (or (not (and (and (not (not (not (or (or x0 x1) (not x1))))) (and (and (and (and (not x0) (not x1)) (or (not x1) (not x1))) (and (and (not x1) (or x1 x0)) (and (and x0 x0) (or x0 x1)))) (or (and (not (and x0 x0)) (and (and x1 x1) (and x0 x0))) (and (not (and x0 x1)) (or (and x0 x0) (or x1 x1)))))) (not (and (or (and (not (or x0 x1)) (or (or x0 x0) (and x1 x1))) (and (not (or x0 x1)) (or (not x1) (and x1 x0)))) (and (and (not (or x1 x0)) (and (or x0 x1) (and x0 x1))) (not (not (not x1)))))))) (and (or (not (and (not (not (and (or x1 x1) (or x0 x0)))) (or (not (and (or x1 x1) (not x1))) (not (and (and x0 x0) (not x1)))))) (not (not (not (not (not (and x1 x0))))))) (and (not (not (or (or (or (and x0 x1) (and x0 x0)) (and (not x0) (or x1 x0))) (and (or (or x1 x1) (and x0 x0)) (or (not x0) (and x1 x1)))))) (or (not (and (and (or (not x0) (not x0)) (not (or x1 x0))) (or (and (and x1 x0) (not x0)) (or (or x1 x1) (and x1 x0))))) (and (not (not (and (or x1 x0) (and x0 x1)))) (and (and (not (and x1 x1)) (or (or x0 x1) (not x0))) (and (and (not x0) (not x0)) (or (and x0 x0) (or x0 x1)))))))))))
(assert (not (not (and (or (or (not x1) (or x0 x0)) (and (and x0 x1) (or x0 x0))) (not (not (and x0 x1)))))))
(assert (or (and (or x0 x1) (and x1 x0)) (or (and x1 x0) (not x0))))
(assert (not (or x0 x0)))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(check-sat)
(push 1)
(assert (or (or (and x0 x0) (and x0 x0)) (and (or x1 x0) (and x1 x0))))
(assert (and x1 x1))
(check-sat)
(push 1)
(check-sat)
(pop 1)
(check-sat)
(pop 1)
(check-sat)
