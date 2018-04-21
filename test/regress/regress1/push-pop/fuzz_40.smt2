; COMMAND-LINE: --incremental
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
(declare-fun x2 () Bool)
(declare-fun x3 () Bool)
(check-sat)
(push 1)
(check-sat)
(pop 1)
(assert (not (and (not (or (and (or (or x0 x3) (or x2 x1)) (and (or x1 x0) (not x0))) (or (and (not x2) (and x2 x3)) (not (and x2 x1))))) (and (not (and (or (and x3 x1) (not x2)) (not (or x3 x3)))) (or (not (and (and x1 x2) (and x0 x0))) (or (or (or x3 x2) (not x1)) (or (and x3 x2) (not x0))))))))
(check-sat)
(push 1)
(assert (and (and x3 x1) (and x2 x2)))
(check-sat)
(pop 1)
(assert (or (or (and (not (or (and (not (and (not (not x1)) (or (and x0 x2) (and x0 x3)))) (not (not (and (not x1) (and x0 x3))))) (not (not (not (and (not x0) (not x2))))))) (not (or (not (and (not (or (or x1 x1) (not x1))) (not (or (not x3) (or x3 x0))))) (not (or (not (or (or x2 x0) (not x3))) (and (not (and x0 x2)) (not (and x2 x3)))))))) (and (or (not (or (not (not (or (or x3 x2) (and x2 x3)))) (and (or (or (not x3) (or x0 x2)) (not (and x1 x2))) (or (and (or x3 x2) (not x0)) (and (and x3 x3) (not x2)))))) (not (not (not (or (and (or x1 x3) (or x2 x2)) (or (not x0) (not x1))))))) (and (or (not (or (and (or (and x1 x3) (or x2 x2)) (or (not x1) (not x3))) (or (or (and x2 x0) (not x3)) (not (not x1))))) (or (or (not (not (not x0))) (not (or (not x0) (not x1)))) (or (and (and (or x2 x1) (and x2 x0)) (not (and x0 x2))) (not (and (not x0) (or x3 x1)))))) (and (not (and (and (or (and x3 x0) (and x0 x1)) (not (or x1 x1))) (not (and (not x3) (not x0))))) (not (and (or (not (not x1)) (and (not x0) (or x1 x0))) (not (not (and x1 x1))))))))) (and (not (not (not (and (or (and (and (or x2 x3) (not x0)) (or (and x3 x3) (and x2 x0))) (or (not (or x2 x1)) (not (or x3 x1)))) (and (and (and (and x3 x2) (or x3 x2)) (not (not x0))) (or (and (or x2 x1) (and x1 x0)) (and (not x2) (not x1)))))))) (and (or (and (or (not (not (not (or x2 x0)))) (not (or (and (and x2 x2) (and x2 x1)) (and (and x3 x0) (or x1 x0))))) (not (or (or (and (not x2) (and x2 x1)) (not (not x0))) (not (and (and x3 x0) (or x1 x3)))))) (not (or (not (or (and (and x2 x2) (not x3)) (or (not x2) (or x0 x2)))) (or (or (and (or x0 x1) (or x0 x1)) (not (not x2))) (or (or (and x2 x0) (and x1 x2)) (and (not x1) (or x3 x3))))))) (or (and (or (and (and (or (and x3 x3) (and x0 x0)) (or (or x0 x3) (or x0 x3))) (and (not (or x3 x3)) (and (not x3) (or x1 x2)))) (and (and (and (not x0) (or x1 x3)) (or (not x2) (or x1 x2))) (and (or (not x3) (or x0 x0)) (or (not x0) (not x2))))) (and (not (and (or (not x3) (not x0)) (or (not x2) (or x0 x3)))) (not (not (not (and x0 x0)))))) (or (and (and (and (or (not x1) (not x0)) (and (or x2 x0) (not x2))) (or (not (and x1 x2)) (and (or x2 x2) (not x2)))) (and (not (not (not x3))) (or (and (not x0) (and x2 x1)) (and (not x3) (not x1))))) (or (and (or (not (or x1 x2)) (or (and x2 x1) (not x0))) (and (or (and x3 x0) (or x2 x3)) (or (or x0 x3) (and x3 x2)))) (or (not (not (and x2 x2))) (or (not (not x2)) (or (or x0 x3) (or x0 x2)))))))))))
(check-sat)
(push 1)
(assert (or (or (not x3) (and x3 x0)) (not (and x3 x1))))
(assert (not x0))
(check-sat)
(push 1)
(check-sat)
(pop 1)
(assert (or (not (or (or (and (and (not (or (not x1) (and x1 x1))) (and (and (or x3 x3) (not x2)) (and (not x0) (or x2 x1)))) (not (or (or (and x0 x2) (not x2)) (not (and x0 x1))))) (not (and (or (and (and x0 x1) (not x0)) (or (and x0 x2) (or x1 x3))) (and (or (or x3 x1) (and x3 x1)) (or (or x3 x1) (not x0)))))) (and (and (not (not (not (or x1 x2)))) (or (or (or (not x1) (and x0 x3)) (and (not x2) (not x0))) (or (or (not x1) (not x1)) (and (and x2 x1) (not x2))))) (not (not (and (not (or x2 x2)) (and (not x2) (and x1 x2)))))))) (not (or (and (and (not (not (and (and x3 x2) (and x0 x3)))) (not (not (not (not x1))))) (and (not (not (and (not x2) (not x1)))) (not (or (or (or x2 x3) (not x1)) (and (and x0 x1) (or x3 x0)))))) (and (not (and (and (and (not x3) (not x0)) (and (not x0) (or x3 x2))) (not (and (and x0 x2) (and x3 x0))))) (not (and (and (not (and x1 x1)) (or (and x1 x1) (or x0 x1))) (not (or (or x0 x0) (and x2 x3))))))))))
(check-sat)
(pop 1)
(assert (not (and (and (and (or (or (or (and x0 x2) (and x1 x3)) (or (not x0) (and x2 x1))) (and (or (and x0 x2) (not x2)) (or (not x3) (and x1 x0)))) (or (not (or (and x1 x1) (or x1 x3))) (and (and (and x0 x0) (and x2 x2)) (and (not x0) (or x2 x3))))) (not (not (and (not (or x0 x2)) (or (and x1 x2) (or x2 x3)))))) (or (and (or (not (or (not x3) (or x1 x1))) (and (not (or x2 x2)) (or (or x3 x3) (and x3 x3)))) (not (or (or (and x2 x2) (and x1 x2)) (not (not x1))))) (not (not (not (and (or x0 x3) (or x3 x2)))))))))
(assert (or (not (and (not x1) (not x3))) (or (not (and x2 x0)) (and (or x1 x0) (or x2 x1)))))
(assert (and (not (or (and x2 x0) (not x0))) (or (not (and x1 x1)) (and (and x1 x3) (and x3 x3)))))
(check-sat)
