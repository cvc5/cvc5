; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
(set-logic QF_LIA)
(declare-fun x0 () Bool)
(declare-fun x1 () Bool)
(check-sat)
(push 1)
(assert (or (not (or (and x1 x0) (or x1 x0))) (not (not (not x0)))))
(check-sat)
(push 1)
(assert (or (not (or (and (or (or (and (or (not x0) (not x0)) (not (not x0))) (not (not (and x0 x0)))) (and (or (or (and x0 x0) (and x1 x0)) (not (or x1 x0))) (and (and (and x1 x0) (and x0 x0)) (and (not x0) (or x0 x1))))) (and (and (and (or (or x1 x0) (not x1)) (and (or x1 x0) (or x1 x1))) (and (and (not x1) (and x0 x0)) (and (or x0 x0) (not x1)))) (not (not (not (or x0 x1)))))) (and (not (and (and (or (and x0 x1) (not x0)) (or (and x1 x1) (or x0 x0))) (and (or (or x1 x1) (not x0)) (and (not x1) (or x1 x1))))) (or (and (or (or (or x0 x0) (not x0)) (or (and x0 x0) (or x1 x1))) (not (and (and x0 x0) (or x0 x1)))) (not (not (or (and x0 x1) (not x0)))))))) (or (or (and (and (or (or (and (not x1) (not x1)) (and (not x0) (not x1))) (and (and (or x1 x0) (and x0 x0)) (and (or x1 x0) (not x1)))) (and (not (or (or x1 x1) (and x0 x0))) (or (or (or x0 x0) (not x0)) (and (and x1 x0) (not x1))))) (and (and (or (or (not x0) (not x0)) (not (and x1 x0))) (not (and (not x1) (not x1)))) (and (or (and (and x1 x0) (and x0 x0)) (not (not x1))) (not (or (not x1) (or x0 x1)))))) (or (not (and (not (and (and x0 x0) (or x1 x0))) (or (or (or x1 x0) (not x1)) (or (not x1) (not x1))))) (and (not (or (and (not x0) (and x1 x0)) (or (and x1 x1) (or x0 x1)))) (not (or (and (or x0 x1) (not x1)) (not (or x1 x0))))))) (or (and (or (not (or (and (and x1 x0) (or x0 x1)) (and (and x0 x1) (and x0 x0)))) (and (not (or (and x0 x1) (not x1))) (or (not (not x0)) (not (or x1 x0))))) (or (or (or (and (or x1 x0) (not x0)) (and (and x1 x1) (not x0))) (not (not (or x0 x1)))) (and (not (and (and x1 x1) (not x1))) (and (and (and x0 x1) (or x1 x0)) (and (and x1 x1) (or x1 x1)))))) (and (not (not (or (and (or x1 x1) (and x0 x0)) (not (not x1))))) (not (not (or (and (not x1) (or x0 x0)) (or (and x0 x0) (and x1 x1))))))))))
(check-sat)
(push 1)
(assert (and (not x0) (or x1 x0)))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(check-sat)
(pop 1)
(check-sat)
(push 1)
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (not (not (not (and x1 x1)))))
(check-sat)
(pop 1)
(check-sat)
