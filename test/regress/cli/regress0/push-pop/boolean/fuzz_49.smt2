; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: unsat
(set-logic QF_LIA)
(declare-fun x0 () Bool)
(declare-fun x1 () Bool)
(assert (and (not (and (or (and (and (or (or (or x0 x1) (and x0 x0)) (or (not x0) (and x0 x1))) (or (not (or x0 x0)) (not (and x0 x0)))) (not (or (not (not x0)) (not (and x0 x1))))) (and (or (and (and (not x1) (or x1 x0)) (not (and x0 x1))) (not (not (or x1 x0)))) (not (not (and (or x0 x1) (not x0)))))) (and (not (or (and (and (not x1) (not x0)) (and (and x0 x1) (and x1 x1))) (and (not (and x0 x0)) (not (or x0 x0))))) (and (or (or (and (or x1 x1) (and x0 x1)) (not (or x0 x0))) (and (or (or x1 x1) (or x0 x0)) (and (or x1 x1) (and x0 x1)))) (not (or (and (not x0) (or x0 x1)) (or (and x0 x0) (or x0 x1)))))))) (or (not (and (and (and (not (and (not x0) (not x0))) (and (and (or x0 x1) (not x0)) (or (not x0) (or x0 x0)))) (and (and (and (not x0) (and x0 x1)) (and (not x0) (not x1))) (and (not (not x0)) (and (and x1 x1) (not x0))))) (or (not (not (not (not x0)))) (not (and (and (or x0 x1) (or x1 x1)) (or (or x1 x1) (or x0 x1))))))) (or (and (not (and (or (not (not x0)) (or (or x0 x1) (or x1 x0))) (or (and (not x1) (and x0 x1)) (or (not x1) (and x1 x0))))) (and (not (and (not (not x0)) (and (not x1) (and x1 x0)))) (not (not (and (or x0 x1) (or x0 x1)))))) (and (or (and (and (and (or x1 x0) (and x1 x0)) (and (not x1) (or x1 x1))) (or (and (and x1 x0) (not x1)) (and (not x1) (or x1 x1)))) (or (and (or (not x1) (not x1)) (and (or x0 x0) (not x0))) (not (and (not x0) (and x0 x1))))) (and (and (or (and (not x1) (or x0 x1)) (and (not x1) (or x1 x1))) (and (and (and x1 x1) (or x1 x0)) (and (not x0) (or x1 x1)))) (or (and (or (and x1 x0) (or x1 x1)) (or (or x1 x1) (and x1 x0))) (not (and (and x0 x1) (not x1))))))))))
(assert (not (not (or (or (or (or (or (and x0 x0) (and x1 x0)) (or (and x1 x1) (and x0 x0))) (or (not (and x1 x1)) (and (or x1 x0) (or x0 x0)))) (and (and (or (and x1 x0) (or x1 x0)) (and (or x0 x1) (or x0 x0))) (and (not (not x0)) (and (and x1 x1) (or x1 x0))))) (and (not (not (and (or x0 x0) (and x1 x0)))) (not (or (or (and x1 x0) (or x0 x0)) (or (not x1) (and x1 x0)))))))))
(check-sat)
(push 1)
(assert (or (or (or (not (not (or x1 x1))) (not (not (and x0 x1)))) (and (not (not (not x0))) (not (and (not x0) (and x0 x1))))) (not (or (and (not (not x1)) (and (not x0) (or x1 x0))) (not (and (not x1) (and x1 x0)))))))
(assert (or x0 x0))
(assert (and (not (and (or (or x0 x0) (and x1 x1)) (and (or x1 x0) (or x0 x1)))) (and (or (not (or x1 x1)) (not (not x0))) (or (or (and x1 x1) (not x1)) (not (or x0 x0))))))
(check-sat)
