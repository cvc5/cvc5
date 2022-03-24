; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
(set-logic QF_LIA)
(declare-fun x0 () Bool)
(declare-fun x1 () Bool)
(declare-fun x2 () Bool)
(check-sat)
(push 1)
(assert (or (and x1 x2) (and x1 x2)))
(assert (or (and (or (and (and (and (and (and (not (or x1 x2)) (not (and x0 x2))) (or (and (and x1 x2) (not x2)) (or (or x1 x2) (not x1)))) (or (or (not (not x1)) (or (and x0 x2) (or x2 x2))) (and (not (or x0 x0)) (not (and x1 x1))))) (not (not (and (not (not x2)) (and (or x1 x0) (and x0 x2)))))) (and (and (or (not (not (or x0 x2))) (not (or (not x2) (or x2 x0)))) (not (not (not (not x1))))) (or (not (and (not (and x1 x0)) (not (and x0 x1)))) (not (or (not (or x2 x2)) (or (not x2) (and x1 x0))))))) (not (not (or (not (not (or (and x0 x0) (and x1 x2)))) (not (and (or (and x2 x2) (or x2 x2)) (or (not x2) (or x1 x1)))))))) (or (not (and (or (not (or (and (and x0 x1) (or x0 x1)) (and (not x1) (and x1 x2)))) (or (and (not (and x1 x1)) (not (or x0 x2))) (not (not (not x2))))) (or (and (not (and (not x1) (and x2 x1))) (not (and (or x2 x1) (not x0)))) (or (or (not (or x1 x1)) (and (or x1 x2) (or x2 x1))) (or (and (or x1 x0) (and x2 x2)) (and (and x1 x0) (not x1))))))) (or (or (and (and (and (and (and x2 x0) (not x0)) (and (and x0 x1) (or x0 x2))) (not (or (and x1 x2) (or x1 x1)))) (and (or (not (not x1)) (not (or x1 x1))) (or (not (or x2 x0)) (not (and x2 x2))))) (and (and (or (not (and x1 x0)) (not (or x1 x0))) (and (not (not x1)) (and (not x1) (not x0)))) (not (or (and (not x1) (or x0 x1)) (and (or x0 x1) (not x2)))))) (and (or (or (not (or (and x0 x1) (not x0))) (not (and (not x1) (or x1 x2)))) (not (not (or (and x0 x1) (not x2))))) (or (or (or (not (not x2)) (and (or x0 x1) (and x1 x2))) (or (not (not x0)) (or (not x1) (and x1 x1)))) (or (and (and (not x2) (or x2 x2)) (not (not x0))) (and (not (or x0 x0)) (not (not x2))))))))) (and (and (or (or (not (or (and (not (and x2 x2)) (or (not x0) (or x0 x0))) (or (not (or x0 x0)) (and (not x2) (not x0))))) (or (and (or (or (or x2 x0) (and x2 x1)) (or (not x0) (not x1))) (and (or (not x1) (or x0 x2)) (or (or x0 x0) (not x0)))) (and (not (or (not x0) (and x2 x1))) (not (or (or x1 x1) (and x1 x1)))))) (and (not (not (and (not (and x2 x0)) (not (and x1 x2))))) (not (and (or (and (and x0 x0) (not x0)) (or (not x0) (or x2 x1))) (and (and (or x0 x2) (or x0 x2)) (and (or x1 x2) (not x0))))))) (and (not (or (or (not (and (and x0 x2) (and x0 x0))) (or (or (and x0 x0) (or x1 x1)) (or (and x2 x2) (or x0 x0)))) (or (or (not (or x2 x1)) (or (not x0) (or x1 x1))) (or (or (not x0) (and x0 x1)) (not (and x2 x1)))))) (not (or (not (or (or (or x0 x0) (or x2 x0)) (and (and x1 x0) (and x2 x0)))) (or (and (or (or x1 x1) (not x2)) (and (and x2 x0) (not x1))) (and (not (not x0)) (or (and x1 x1) (or x2 x2)))))))) (and (and (or (or (not (or (and (and x1 x1) (or x0 x2)) (not (and x0 x1)))) (not (or (and (and x0 x0) (and x1 x1)) (and (or x2 x0) (or x1 x2))))) (and (not (and (and (or x0 x0) (not x0)) (and (and x1 x2) (not x2)))) (and (or (and (or x1 x0) (or x0 x1)) (and (or x1 x2) (or x0 x1))) (and (not (and x0 x2)) (and (and x2 x0) (not x0)))))) (and (not (or (and (and (and x0 x1) (not x0)) (and (not x2) (not x2))) (and (and (and x2 x1) (not x1)) (not (or x2 x1))))) (not (and (and (and (not x0) (and x0 x2)) (not (and x2 x1))) (not (or (or x2 x0) (or x0 x2))))))) (not (and (not (or (or (and (or x2 x0) (or x1 x1)) (not (and x2 x0))) (not (not (not x0))))) (and (not (and (and (not x1) (and x2 x2)) (and (not x2) (not x1)))) (or (or (or (and x0 x0) (not x2)) (or (and x1 x2) (and x0 x2))) (or (or (and x2 x2) (or x2 x2)) (and (not x1) (or x1 x1)))))))))))
(assert (and x1 x2))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (not (and (or (and (not x2) (or x0 x1)) (or (not x1) (not x2))) (or (or (not x2) (or x0 x2)) (and (not x1) (or x1 x2))))))
(assert (not (and (and x1 x2) (or x1 x1))))
(assert (or (not (not x2)) (not (and x0 x2))))
(check-sat)
