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
(declare-fun x4 () Bool)
(check-sat)
(push 1)
(check-sat)
(pop 1)
(assert (or (or (not (and (not (or (or (and (not (and x0 x3)) (not (not x1))) (or (not (and x4 x4)) (or (not x4) (not x4)))) (or (not (or (or x4 x0) (and x4 x2))) (not (or (and x4 x0) (or x1 x3)))))) (not (or (and (or (or (or x4 x2) (and x3 x2)) (or (not x3) (or x3 x4))) (or (not (or x2 x2)) (and (or x1 x1) (not x4)))) (or (and (not (or x0 x4)) (and (or x0 x3) (not x0))) (not (and (and x1 x2) (and x1 x4)))))))) (not (and (not (and (or (and (not (or x0 x4)) (or (and x1 x4) (and x3 x3))) (or (or (not x3) (or x1 x1)) (not (not x4)))) (not (and (and (and x2 x4) (and x2 x4)) (not (not x4)))))) (and (and (not (not (or (not x4) (and x4 x0)))) (not (and (not (and x0 x0)) (or (not x4) (or x3 x2))))) (not (not (and (and (not x2) (and x4 x4)) (not (and x1 x2))))))))) (and (or (and (not (and (not (or (or (and x1 x2) (not x0)) (or (not x4) (and x3 x0)))) (or (not (or (or x1 x3) (not x0))) (and (or (or x3 x0) (and x2 x0)) (not (not x0)))))) (or (and (and (and (and (not x0) (and x0 x1)) (and (not x1) (or x1 x3))) (not (not (or x1 x1)))) (or (not (or (or x2 x3) (or x2 x1))) (or (not (not x4)) (and (and x0 x4) (not x0))))) (or (and (or (not (not x1)) (or (not x2) (or x1 x4))) (or (or (not x3) (not x4)) (not (and x2 x2)))) (or (and (or (and x3 x1) (and x1 x1)) (not (and x4 x2))) (and (or (not x2) (and x4 x3)) (and (not x2) (or x0 x2))))))) (and (or (and (or (or (and (not x1) (or x0 x4)) (not (not x3))) (not (or (or x3 x1) (and x1 x0)))) (or (and (or (and x3 x3) (not x3)) (or (and x0 x2) (not x4))) (and (not (not x2)) (and (and x3 x2) (and x4 x3))))) (and (not (not (or (not x2) (and x0 x3)))) (not (and (and (not x3) (not x4)) (not (not x4)))))) (or (not (or (not (not (not x2))) (and (and (not x0) (and x3 x4)) (or (not x4) (and x0 x1))))) (not (or (and (or (and x2 x1) (or x3 x2)) (not (and x1 x4))) (and (not (or x0 x4)) (not (not x1)))))))) (or (and (and (not (or (or (and (and x3 x0) (not x2)) (and (or x0 x4) (and x3 x2))) (and (or (and x1 x3) (and x2 x0)) (or (not x0) (or x0 x3))))) (not (not (and (or (and x4 x3) (or x1 x0)) (not (and x2 x3)))))) (not (or (not (and (and (and x3 x4) (or x3 x4)) (or (or x1 x2) (and x1 x4)))) (not (not (or (and x2 x2) (and x4 x4))))))) (or (or (not (or (or (or (or x2 x0) (not x2)) (or (not x0) (or x4 x4))) (or (or (and x2 x0) (or x1 x1)) (and (or x3 x0) (not x0))))) (or (or (and (not (not x3)) (not (and x3 x4))) (not (and (not x0) (not x0)))) (and (or (or (or x2 x3) (and x3 x0)) (or (or x0 x3) (or x2 x2))) (not (not (and x3 x0)))))) (or (or (not (or (not (not x4)) (and (and x4 x0) (and x2 x2)))) (or (and (or (or x4 x2) (and x0 x3)) (and (and x0 x3) (not x0))) (not (and (or x3 x0) (and x0 x4))))) (and (or (and (or (and x2 x2) (and x0 x2)) (not (not x1))) (not (or (and x1 x1) (and x1 x2)))) (and (not (not (not x2))) (or (or (not x1) (and x0 x4)) (or (not x0) (not x0)))))))))))
(assert (or (or (or (and x2 x1) (and x4 x4)) (or (or x1 x4) (and x2 x3))) (not (and (and x3 x4) (not x0)))))
(check-sat)
(push 1)
(check-sat)
(push 1)
(check-sat)
(pop 1)
(assert (and (not (and (not (and (not (or (or x3 x0) (and x0 x2))) (not (and (and x2 x0) (not x3))))) (and (or (or (not (and x3 x1)) (not (and x4 x4))) (or (or (or x0 x3) (or x4 x4)) (not (not x3)))) (not (or (not (not x0)) (and (or x1 x0) (and x3 x2))))))) (not (and (and (and (or (or (or x2 x1) (and x0 x1)) (and (or x3 x0) (or x0 x0))) (or (and (and x3 x1) (or x3 x4)) (not (not x4)))) (not (and (or (and x2 x1) (and x4 x0)) (not (not x0))))) (and (and (or (or (and x3 x3) (or x1 x4)) (and (and x2 x3) (not x1))) (not (and (or x4 x2) (or x4 x4)))) (not (not (or (and x1 x1) (and x4 x3)))))))))
(assert (not (not (not (not (and (or (not (or (and (not x4) (not x2)) (and (not x4) (not x1)))) (not (and (and (and x2 x2) (and x4 x3)) (not (and x1 x0))))) (not (or (and (not (and x3 x2)) (not (not x2))) (not (not (not x2)))))))))))
(check-sat)
(push 1)
(assert (or (or (or (or (not x4) (not x1)) (not (not x1))) (and (and (and x4 x1) (and x4 x4)) (and (and x4 x0) (or x0 x2)))) (not (and (not (and x3 x0)) (and (not x2) (or x1 x0))))))
(check-sat)
(pop 1)
(assert (not (or (not (not x3)) (or (not x2) (not x4)))))
(assert (and (or x3 x4) (and x4 x0)))
(assert (and (not (not (not (or (or (or (and (and (or x2 x3) (or x3 x1)) (and (or x0 x3) (and x4 x4))) (and (not (and x2 x4)) (or (and x4 x0) (or x4 x3)))) (not (or (and (and x0 x4) (not x4)) (not (or x3 x4))))) (and (and (or (not (and x1 x4)) (or (not x1) (and x4 x2))) (not (or (or x1 x2) (and x4 x3)))) (not (or (or (not x2) (not x4)) (and (or x1 x3) (not x3))))))))) (not (or (and (not (and (and (and (not (and x3 x3)) (not (and x1 x1))) (not (or (not x4) (or x2 x1)))) (and (not (or (not x4) (and x4 x2))) (or (or (and x1 x2) (not x4)) (and (or x3 x4) (not x0)))))) (and (or (or (or (or (or x3 x2) (or x1 x3)) (or (not x4) (or x1 x4))) (or (not (and x1 x0)) (and (and x4 x3) (and x0 x0)))) (and (or (not (not x0)) (or (or x0 x3) (or x4 x4))) (and (not (or x2 x2)) (not (and x2 x4))))) (or (not (and (or (and x1 x1) (or x1 x1)) (not (or x0 x0)))) (and (not (and (or x1 x3) (or x3 x3))) (or (and (or x0 x1) (not x2)) (or (or x3 x0) (or x3 x1))))))) (not (not (or (and (not (or (or x2 x2) (or x0 x3))) (or (and (and x4 x3) (not x4)) (or (or x0 x4) (and x3 x0)))) (and (or (and (or x1 x0) (or x0 x1)) (not (and x3 x4))) (and (or (or x2 x2) (or x1 x3)) (not (or x0 x1)))))))))))
(assert (or (not (and (and (or (and x3 x4) (not x3)) (not (or x1 x0))) (and (and (or x3 x2) (or x2 x1)) (and (and x0 x1) (and x0 x2))))) (not (not (or (not (not x1)) (or (or x1 x3) (or x1 x4)))))))
(check-sat)
(pop 1)
(assert (not (or x1 x2)))
(assert (or (and (or (or x2 x0) (not x4)) (or (not x4) (or x2 x2))) (not (not (or x2 x3)))))
(check-sat)
