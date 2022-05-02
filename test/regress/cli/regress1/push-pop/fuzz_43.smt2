; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
(set-logic QF_LIA)
(declare-fun x0 () Bool)
(declare-fun x1 () Bool)
(declare-fun x2 () Bool)
(check-sat)
(push 1)
(assert (not (not (or (and (or (or x1 x1) (and x0 x1)) (or (or x2 x0) (or x0 x0))) (not (and (or x2 x0) (not x1)))))))
(assert (and (and x0 x1) (and x1 x0)))
(assert (or (not (or (or (or (and (or (and (and x1 x2) (and x1 x1)) (and (not x1) (and x2 x0))) (or (not (not x2)) (or (and x1 x1) (and x2 x1)))) (or (or (not (or x1 x2)) (and (or x0 x2) (or x2 x1))) (not (or (and x1 x2) (or x2 x0))))) (or (not (or (and (or x2 x0) (or x2 x1)) (and (not x2) (and x2 x1)))) (or (not (and (or x2 x1) (and x2 x2))) (and (and (not x1) (and x0 x2)) (and (and x0 x2) (or x1 x2)))))) (not (and (or (or (or (not x2) (and x0 x1)) (or (or x2 x2) (or x2 x2))) (and (and (not x2) (not x0)) (not (and x1 x0)))) (or (not (not (or x2 x0))) (and (not (or x2 x2)) (not (not x2)))))))) (not (or (and (not (and (and (not (not x2)) (and (not x2) (not x2))) (or (and (not x0) (or x1 x1)) (or (and x1 x0) (and x0 x0))))) (and (or (or (not (and x1 x1)) (not (or x1 x1))) (not (and (and x1 x0) (or x2 x0)))) (not (not (or (not x2) (and x0 x0)))))) (or (or (and (and (not (and x1 x1)) (or (or x0 x0) (or x2 x2))) (not (and (and x1 x0) (not x0)))) (or (not (not (and x1 x2))) (or (or (not x1) (and x1 x2)) (or (or x0 x2) (and x0 x0))))) (and (or (not (and (or x2 x2) (and x2 x2))) (and (not (not x1)) (and (or x1 x2) (and x1 x0)))) (not (or (not (or x1 x0)) (not (or x0 x2))))))))))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (not (and (not (and x1 x1)) (and (and x0 x0) (not x2)))))
(check-sat)
(push 1)
(assert (or (and (or (and (or (and x0 x0) (not x0)) (and (and x1 x0) (or x0 x1))) (or (or (or x1 x1) (and x2 x2)) (not (and x0 x0)))) (or (and (and (and x2 x0) (not x1)) (or (or x2 x2) (and x0 x0))) (and (or (and x1 x1) (and x2 x1)) (and (not x0) (and x1 x0))))) (not (not (or (or (or x1 x1) (or x1 x0)) (not (or x2 x1)))))))
(assert (not (not (and (and (or (or (and x0 x2) (or x2 x0)) (and (and x1 x1) (or x1 x2))) (and (or (and x1 x0) (not x1)) (or (and x0 x0) (not x2)))) (not (and (not (or x2 x0)) (not (not x0))))))))
(assert (not (or (and (and x1 x0) (not x2)) (or (or x2 x1) (or x0 x2)))))
(assert (or (not (and (or (and (or (not (or (and x1 x0) (not x2))) (and (not (or x2 x1)) (not (or x0 x2)))) (and (not (and (not x2) (or x0 x2))) (not (or (not x0) (and x0 x2))))) (or (not (and (and (or x1 x2) (not x1)) (or (not x0) (or x0 x1)))) (or (and (and (not x1) (and x2 x1)) (and (and x2 x1) (or x1 x0))) (or (not (or x1 x1)) (or (or x1 x2) (not x1)))))) (not (or (not (not (not (or x1 x0)))) (not (or (and (or x0 x0) (not x2)) (not (or x1 x2)))))))) (or (and (or (not (or (or (or (and x1 x0) (or x0 x0)) (or (or x2 x1) (not x2))) (not (not (and x2 x2))))) (not (not (or (and (or x2 x1) (or x1 x2)) (or (and x2 x1) (or x0 x1)))))) (not (and (not (not (not (and x2 x1)))) (and (and (not (not x1)) (and (not x0) (not x1))) (or (or (or x2 x1) (not x2)) (and (not x1) (not x0))))))) (or (and (or (not (not (not (and x1 x2)))) (or (not (and (or x0 x0) (not x0))) (and (not (not x1)) (not (and x0 x2))))) (and (and (and (and (and x2 x1) (or x2 x2)) (not (or x0 x1))) (not (not (and x1 x2)))) (and (and (not (or x0 x1)) (or (and x2 x2) (not x1))) (and (and (or x2 x2) (not x1)) (and (or x1 x1) (or x2 x0)))))) (or (and (not (and (and (and x0 x1) (not x1)) (or (or x0 x0) (not x0)))) (and (or (not (and x1 x2)) (not (or x0 x2))) (and (or (or x0 x1) (or x2 x0)) (not (or x1 x0))))) (not (and (not (and (and x0 x1) (and x0 x0))) (not (or (not x0) (or x1 x0))))))))))
(check-sat)
(pop 1)
(check-sat)
(pop 1)
(assert (not (and (and (or (and x0 x2) (not x2)) (and (and x1 x0) (not x0))) (not (and (and x2 x1) (or x0 x1))))))
(check-sat)
(push 1)
(assert (and (not (and (or (not (and (and (not (not (or x2 x1))) (or (not (or x2 x2)) (and (not x2) (and x0 x1)))) (or (and (not (or x1 x2)) (and (and x2 x1) (or x2 x0))) (not (and (or x1 x2) (not x0)))))) (not (or (or (not (not (not x2))) (not (or (or x1 x1) (and x0 x1)))) (or (and (not (not x0)) (and (or x0 x0) (not x1))) (or (not (and x1 x2)) (and (and x0 x0) (and x1 x0))))))) (and (and (or (or (and (or (and x2 x0) (not x0)) (or (or x2 x1) (and x2 x1))) (or (or (or x2 x1) (not x0)) (or (and x2 x2) (not x2)))) (or (and (or (or x2 x0) (and x0 x1)) (not (and x1 x0))) (or (or (not x0) (not x0)) (or (not x2) (not x0))))) (not (or (and (and (not x1) (and x0 x0)) (not (and x1 x0))) (or (and (and x0 x2) (and x1 x0)) (and (and x0 x0) (not x1)))))) (or (and (or (or (and (and x2 x0) (or x0 x2)) (or (and x2 x2) (not x2))) (or (and (or x0 x1) (and x2 x2)) (or (and x0 x0) (or x2 x1)))) (not (or (and (and x2 x1) (not x2)) (and (not x1) (and x1 x0))))) (or (or (and (not (and x0 x1)) (and (or x0 x1) (not x1))) (not (or (and x2 x0) (and x1 x1)))) (or (or (and (and x2 x0) (or x0 x1)) (and (not x2) (or x2 x1))) (and (or (not x1) (not x1)) (or (and x2 x1) (not x1))))))))) (and (or (not (or (not (or (and (and (or x2 x1) (or x0 x2)) (or (or x0 x2) (and x1 x0))) (not (or (or x0 x1) (and x2 x2))))) (or (or (and (and (and x2 x0) (and x1 x1)) (and (or x0 x0) (and x1 x1))) (and (and (and x1 x1) (not x0)) (and (not x1) (not x0)))) (and (or (and (not x2) (not x1)) (not (or x0 x0))) (not (not (and x1 x0))))))) (or (not (not (not (and (and (and x2 x0) (not x1)) (or (or x1 x0) (and x2 x2)))))) (not (and (and (or (or (not x0) (not x0)) (and (and x1 x1) (and x0 x1))) (and (and (not x2) (and x2 x1)) (not (not x2)))) (and (or (and (or x2 x0) (or x2 x1)) (and (and x2 x1) (and x0 x2))) (not (not (not x0)))))))) (and (or (not (and (and (and (and (or x1 x1) (not x0)) (not (not x1))) (or (not (not x2)) (and (and x1 x1) (not x0)))) (and (or (or (and x2 x2) (or x0 x1)) (and (and x0 x2) (not x1))) (and (not (not x2)) (and (not x2) (not x1)))))) (not (or (or (or (and (and x1 x1) (not x0)) (not (and x2 x0))) (and (and (and x1 x1) (not x0)) (or (and x2 x0) (or x2 x0)))) (not (and (not (not x2)) (or (or x1 x2) (not x0))))))) (and (not (not (or (and (and (and x2 x2) (not x1)) (not (or x2 x1))) (or (not (and x0 x0)) (not (and x2 x1)))))) (or (not (not (not (not (not x0))))) (or (not (and (or (and x2 x0) (and x2 x0)) (or (not x1) (or x1 x2)))) (or (not (not (or x2 x1))) (not (not (not x0)))))))))))
(check-sat)
(push 1)
(assert (or (and (and (and (not (or (or (or (not x1) (and x2 x0)) (or (not x1) (or x0 x1))) (not (or (not x1) (or x1 x0))))) (and (or (or (and (not x2) (not x1)) (or (or x2 x2) (or x1 x0))) (not (and (and x0 x1) (or x0 x2)))) (not (or (or (and x1 x0) (or x0 x2)) (and (and x1 x1) (or x0 x0)))))) (not (and (not (not (or (or x0 x2) (not x2)))) (or (not (not (and x2 x2))) (not (not (and x1 x1))))))) (not (not (or (and (not (not (not x0))) (and (or (not x2) (not x2)) (not (and x0 x0)))) (or (or (and (not x2) (not x2)) (or (not x2) (and x2 x1))) (and (and (not x0) (or x2 x2)) (and (or x1 x1) (not x0)))))))) (not (or (and (or (or (or (and (and x0 x1) (or x0 x1)) (and (or x0 x0) (not x2))) (not (and (not x0) (or x2 x2)))) (and (or (and (not x1) (or x2 x0)) (not (not x0))) (or (or (and x1 x1) (not x0)) (not (or x0 x0))))) (not (not (or (or (not x1) (not x2)) (and (or x2 x2) (not x1)))))) (and (and (not (or (and (or x0 x2) (not x2)) (not (and x2 x2)))) (and (and (or (or x1 x1) (not x1)) (not (and x0 x0))) (not (not (not x2))))) (and (and (and (and (and x1 x1) (not x0)) (not (not x2))) (and (not (not x0)) (or (or x1 x0) (and x1 x1)))) (or (or (and (and x0 x1) (or x0 x0)) (or (not x1) (and x0 x1))) (not (and (and x1 x1) (not x1))))))))))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(check-sat)
(pop 1)
(assert (and x2 x2))
(check-sat)
(push 1)
