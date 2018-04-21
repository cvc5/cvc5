; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: sat
(set-logic QF_LIA)
(declare-fun x0 () Bool)
(declare-fun x1 () Bool)
(declare-fun x2 () Bool)
(declare-fun x3 () Bool)
(declare-fun x4 () Bool)
(declare-fun x5 () Bool)
(declare-fun x6 () Bool)
(assert (or (or (not (and (or (or (not (and (or x6 x3) (not x4))) (and (or (and x2 x3) (not x3)) (and (or x4 x1) (or x4 x3)))) (or (and (not (and x2 x5)) (and (and x2 x0) (and x5 x0))) (and (or (or x1 x4) (and x0 x0)) (or (and x1 x2) (not x5))))) (or (or (or (and (and x6 x5) (not x6)) (and (and x2 x3) (not x4))) (and (not (or x5 x0)) (or (and x1 x3) (and x1 x5)))) (and (not (or (and x0 x5) (and x2 x0))) (or (or (or x6 x2) (not x1)) (or (and x3 x6) (and x4 x2))))))) (and (not (or (or (not (not (or x4 x0))) (or (not (or x2 x4)) (and (not x2) (or x1 x3)))) (or (or (not (not x3)) (and (and x0 x4) (or x0 x0))) (not (and (not x0) (or x3 x2)))))) (or (or (or (or (and (not x3) (or x5 x6)) (and (or x6 x4) (or x5 x5))) (not (or (or x1 x2) (and x6 x4)))) (not (or (and (and x2 x4) (and x5 x2)) (and (not x5) (and x2 x1))))) (not (or (or (not (not x4)) (not (not x1))) (or (not (not x2)) (or (or x4 x6) (and x6 x1)))))))) (not (not (or (or (or (not (and (or x3 x2) (or x1 x4))) (and (or (and x3 x2) (and x4 x0)) (or (not x2) (and x2 x6)))) (and (not (and (and x3 x4) (not x1))) (or (not (and x3 x5)) (and (not x4) (or x5 x5))))) (not (or (or (or (or x6 x5) (or x1 x4)) (or (or x1 x4) (and x6 x0))) (not (not (not x6))))))))))
(assert (or (and (or (and (or (and (not (and (and x5 x5) (not x6))) (not (not (not x3)))) (and (and (and (and x5 x0) (and x4 x3)) (not (and x2 x1))) (not (or (and x1 x3) (and x0 x6))))) (not (and (not (and (or x4 x1) (not x0))) (and (not (or x3 x3)) (or (or x4 x4) (not x3)))))) (or (or (not (or (and (or x3 x2) (or x3 x1)) (not (and x6 x4)))) (not (and (not (or x1 x6)) (or (not x2) (or x1 x6))))) (and (not (or (and (not x3) (and x1 x4)) (and (or x4 x1) (and x6 x6)))) (not (or (and (or x2 x2) (or x3 x1)) (or (not x2) (and x3 x1))))))) (and (not (and (not (not (or (and x6 x1) (and x1 x6)))) (or (or (and (or x5 x6) (not x5)) (or (and x5 x2) (not x5))) (and (or (and x1 x0) (or x6 x3)) (or (and x0 x5) (and x1 x3)))))) (or (and (not (or (not (or x3 x5)) (or (and x4 x2) (not x5)))) (and (not (or (not x6) (and x5 x4))) (and (or (not x3) (or x6 x3)) (not (and x1 x2))))) (and (not (and (not (or x5 x0)) (not (and x1 x3)))) (not (or (and (not x3) (or x0 x6)) (not (or x5 x3)))))))) (and (not (not (and (not (and (or (and x2 x3) (or x5 x6)) (and (not x0) (or x4 x1)))) (or (not (and (and x0 x4) (or x6 x4))) (and (not (or x3 x5)) (or (and x2 x1) (and x6 x3))))))) (not (not (not (or (and (not (or x1 x0)) (or (and x4 x1) (not x4))) (and (not (not x2)) (and (not x2) (and x3 x3))))))))))
(check-sat)
(push 1)
(assert (or (not (not (not x6))) (and (or (and x1 x1) (not x2)) (and (or x4 x3) (not x1)))))
(assert (not (and (and x0 x3) (or x3 x4))))
(assert (or (and x5 x3) (not x4)))
(assert (or (or (or (not (not (or (or (and x3 x2) (and x1 x2)) (and (or x5 x5) (not x6))))) (not (and (and (and (not x6) (or x1 x0)) (or (or x3 x3) (or x3 x3))) (and (or (and x0 x4) (not x3)) (or (not x1) (and x0 x6)))))) (and (and (or (or (not (and x6 x5)) (and (not x5) (or x6 x2))) (not (and (and x6 x2) (not x3)))) (not (or (or (not x5) (not x4)) (or (and x3 x6) (or x6 x1))))) (or (or (not (and (not x6) (or x1 x6))) (and (or (not x3) (and x1 x0)) (not (not x6)))) (not (not (not (not x2))))))) (not (and (and (or (not (not (not x2))) (or (and (not x3) (and x3 x4)) (not (and x1 x3)))) (or (or (and (not x0) (or x0 x0)) (or (not x3) (and x1 x0))) (not (not (and x5 x6))))) (and (and (and (not (not x2)) (not (or x6 x3))) (or (and (not x1) (not x1)) (and (and x1 x5) (and x2 x6)))) (not (not (and (not x1) (or x4 x5)))))))))
(assert (or (and (not (not (not (or (and (or (or x3 x5) (not x3)) (not (or x0 x5))) (or (or (not x3) (or x0 x2)) (or (not x3) (not x4))))))) (not (or (not (and (or (and (or x5 x1) (and x5 x2)) (not (not x5))) (not (or (not x1) (and x6 x6))))) (and (or (and (or (or x3 x1) (or x5 x4)) (and (not x2) (and x1 x2))) (and (or (and x0 x2) (and x6 x6)) (and (and x3 x4) (not x2)))) (or (and (not (not x2)) (and (not x3) (and x1 x5))) (and (not (or x1 x1)) (or (and x2 x5) (not x2)))))))) (and (or (not (not (not (and (and (not x4) (not x0)) (and (and x0 x3) (and x1 x0)))))) (and (or (not (and (and (or x2 x3) (not x2)) (or (not x2) (and x5 x4)))) (not (not (not (and x1 x4))))) (or (and (or (not (or x0 x4)) (and (not x4) (not x2))) (not (and (and x5 x0) (or x5 x1)))) (not (and (and (or x2 x4) (not x0)) (not (not x2))))))) (and (or (not (or (or (or (not x6) (not x1)) (not (or x6 x4))) (and (and (not x6) (not x4)) (not (and x3 x6))))) (not (not (not (not (not x1)))))) (not (or (or (and (not (and x4 x0)) (and (not x6) (or x4 x5))) (not (and (not x6) (or x5 x1)))) (or (and (or (or x1 x2) (or x5 x5)) (not (not x1))) (or (and (and x6 x6) (not x4)) (or (or x2 x0) (and x3 x0))))))))))
(check-sat)
(pop 1)
(assert (or (and (not (and x2 x5)) (and (or x3 x4) (or x0 x3))) (or (or (not x1) (and x3 x3)) (not (or x5 x1)))))
(check-sat)
(push 1)
(assert (not (not (not (or (or x2 x3) (and x2 x1))))))
(assert (not (and (not (and (or (or x4 x4) (or x1 x5)) (or (and x1 x1) (or x4 x3)))) (or (or (and (not x6) (not x6)) (and (not x1) (or x3 x6))) (not (not (and x4 x0)))))))
(check-sat)
(push 1)
(check-sat)
(push 1)
(assert (and (and (not (not (and (or (and x6 x6) (and x4 x4)) (or (or x2 x1) (or x0 x2))))) (and (and (not (or (and x0 x5) (or x2 x4))) (not (or (not x1) (not x1)))) (or (and (and (not x1) (not x3)) (not (or x4 x6))) (or (or (or x2 x6) (or x3 x4)) (and (and x3 x3) (or x0 x1)))))) (or (not (not (or (not (not x4)) (and (or x6 x0) (or x2 x0))))) (or (not (and (and (and x1 x3) (not x4)) (not (and x0 x1)))) (or (and (or (or x6 x4) (or x0 x6)) (or (or x6 x4) (not x4))) (and (not (or x5 x3)) (and (or x2 x2) (not x5))))))))
(check-sat)
(push 1)
(check-sat)
(pop 1)
(check-sat)
(pop 1)
(assert (or (and (or (not (or (or (or (or x1 x4) (and x3 x2)) (or (or x5 x1) (or x6 x2))) (or (not (and x3 x5)) (or (and x0 x1) (not x6))))) (and (and (and (or (and x3 x3) (or x2 x5)) (not (and x0 x4))) (not (not (not x4)))) (or (and (or (or x2 x1) (and x2 x2)) (not (or x1 x4))) (not (and (not x1) (and x0 x2)))))) (not (or (not (and (and (not x1) (and x3 x4)) (and (not x6) (or x6 x1)))) (not (not (and (or x2 x2) (and x4 x6))))))) (not (or (and (and (not (and (or x6 x5) (and x5 x2))) (not (or (not x4) (or x6 x1)))) (or (or (and (not x0) (not x4)) (or (and x4 x5) (not x4))) (or (and (or x6 x1) (and x3 x6)) (or (not x6) (or x4 x1))))) (not (or (and (and (or x2 x6) (not x3)) (or (or x3 x6) (or x1 x4))) (not (and (not x5) (not x0)))))))))
(check-sat)
(pop 1)
(check-sat)
(push 1)
