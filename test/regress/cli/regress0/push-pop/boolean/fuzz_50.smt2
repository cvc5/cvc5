; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: unsat
(set-logic QF_LIA)
(declare-fun x0 () Bool)
(assert (not (not (or x0 x0))))
(check-sat)
(push 1)
(assert (not (and (not (not (not (or (or x0 x0) (not x0))))) (not (not (and (and (or x0 x0) (and x0 x0)) (or (or x0 x0) (not x0))))))))
(assert (or (not (not (not (and (not (not (or x0 x0))) (not (or (not x0) (not x0))))))) (and (not (or (or (and (and (and x0 x0) (or x0 x0)) (not (not x0))) (or (not (not x0)) (and (not x0) (and x0 x0)))) (or (not (or (not x0) (not x0))) (or (or (and x0 x0) (or x0 x0)) (and (and x0 x0) (and x0 x0)))))) (and (and (or (not (and (not x0) (and x0 x0))) (and (not (not x0)) (not (or x0 x0)))) (not (or (or (or x0 x0) (and x0 x0)) (not (not x0))))) (not (and (or (not (and x0 x0)) (or (or x0 x0) (or x0 x0))) (not (and (and x0 x0) (and x0 x0)))))))))
(assert (or (or (not (or (or x0 x0) (or x0 x0))) (or (or (and x0 x0) (or x0 x0)) (or (or x0 x0) (and x0 x0)))) (or (or (not (or x0 x0)) (or (or x0 x0) (not x0))) (or (not (and x0 x0)) (and (or x0 x0) (or x0 x0))))))
(check-sat)
