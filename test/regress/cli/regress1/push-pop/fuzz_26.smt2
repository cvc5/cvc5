; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
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
(declare-fun x5 () Bool)
(declare-fun x6 () Bool)
(check-sat)
(push 1)
(check-sat)
(push 1)
(assert (or (or x4 x2) (or x4 x2)))
(assert (not (not (or (not (or (and x3 x5) (not x6))) (or (or (or x1 x5) (or x0 x3)) (not (or x3 x6)))))))
(assert (or (and (and (or (and x1 x6) (or x2 x4)) (and (and x1 x0) (or x1 x4))) (and (not (and x3 x6)) (not (not x0)))) (and (not (not (and x4 x0))) (not (or (not x6) (and x6 x5))))))
(assert (or (and (and (and (or (not (and (or (or (not x4) (not x3)) (not (and x3 x3))) (and (not (not x3)) (not (and x0 x2))))) (and (and (not (and (and x1 x0) (or x2 x2))) (or (or (or x3 x4) (not x0)) (not (not x5)))) (or (not (and (not x3) (or x4 x4))) (or (not (and x0 x2)) (not (or x3 x0)))))) (or (or (or (not (and (and x0 x6) (not x3))) (or (not (not x3)) (and (not x3) (or x5 x0)))) (or (and (or (or x0 x5) (and x6 x3)) (and (and x3 x6) (not x3))) (and (or (not x1) (or x4 x5)) (and (or x1 x6) (not x4))))) (and (not (and (and (or x0 x4) (or x3 x6)) (or (and x2 x3) (not x6)))) (and (not (or (not x5) (not x2))) (not (not (not x2))))))) (not (or (or (or (and (or (and x3 x5) (or x0 x0)) (not (and x5 x5))) (and (and (and x0 x1) (or x6 x4)) (or (not x4) (and x6 x5)))) (and (and (not (not x0)) (or (not x4) (and x4 x2))) (or (or (and x6 x1) (not x6)) (not (or x4 x2))))) (and (or (or (not (not x1)) (or (and x4 x4) (not x5))) (and (not (not x5)) (not (and x0 x6)))) (and (or (not (or x3 x0)) (not (or x3 x5))) (or (not (and x2 x2)) (and (and x2 x4) (or x4 x1)))))))) (and (not (or (or (and (or (not (not x5)) (or (or x3 x1) (not x1))) (and (not (or x5 x3)) (not (or x3 x0)))) (not (and (not (or x2 x5)) (and (or x1 x0) (and x0 x5))))) (and (or (and (not (and x3 x1)) (or (and x1 x4) (not x5))) (or (or (not x2) (not x4)) (not (not x4)))) (and (not (or (and x5 x1) (or x4 x5))) (not (and (or x2 x1) (not x1))))))) (or (not (not (and (and (not (not x0)) (and (or x0 x3) (not x0))) (or (and (and x0 x6) (and x0 x4)) (not (and x6 x5)))))) (and (and (or (not (not (and x4 x3))) (or (or (and x1 x4) (or x3 x4)) (not (or x2 x2)))) (or (not (or (and x6 x0) (or x2 x3))) (not (or (and x3 x2) (and x6 x5))))) (or (and (not (and (and x6 x0) (not x0))) (or (and (not x5) (and x3 x3)) (not (or x0 x2)))) (and (not (or (and x5 x3) (not x0))) (or (and (and x6 x4) (or x2 x5)) (or (or x5 x1) (or x0 x2))))))))) (or (not (or (or (not (and (or (or (not x2) (or x3 x0)) (not (and x0 x2))) (or (not (and x3 x4)) (or (and x3 x4) (or x2 x6))))) (not (not (not (not (not x1)))))) (not (or (and (or (not (or x2 x3)) (or (or x4 x3) (or x3 x4))) (and (or (not x0) (and x3 x3)) (and (not x2) (and x0 x0)))) (and (or (and (and x1 x3) (and x0 x0)) (and (and x2 x2) (not x3))) (and (or (and x4 x0) (or x4 x4)) (not (or x5 x0)))))))) (and (or (not (not (and (or (and (not x2) (not x6)) (and (and x3 x4) (not x5))) (or (not (not x2)) (and (not x0) (not x3)))))) (and (and (or (or (or (not x0) (not x3)) (or (or x3 x1) (not x0))) (and (not (not x2)) (or (and x6 x2) (not x2)))) (and (and (not (or x4 x4)) (not (or x0 x0))) (and (not (and x5 x5)) (and (not x2) (and x0 x0))))) (not (or (or (or (and x4 x5) (and x2 x5)) (not (and x6 x3))) (not (not (or x5 x4))))))) (or (not (not (and (or (not (or x6 x3)) (not (not x1))) (not (or (or x6 x0) (or x4 x6)))))) (or (not (and (not (not (and x3 x4))) (not (not (not x5))))) (and (and (not (or (or x5 x4) (not x4))) (not (not (or x6 x1)))) (and (not (and (and x1 x0) (or x0 x1))) (and (and (and x5 x2) (and x2 x5)) (or (not x1) (or x6 x4)))))))))))
(check-sat)
(push 1)
(assert (and (and (or (not (or (not x5) (and x3 x3))) (or (or (not x4) (or x5 x2)) (not (or x2 x0)))) (and (not (not (not x4))) (and (and (not x3) (or x5 x0)) (not (or x3 x5))))) (and (or (or (not (and x6 x4)) (or (and x2 x6) (and x2 x1))) (or (not (not x4)) (not (and x6 x3)))) (or (and (not (and x3 x3)) (not (or x0 x2))) (or (not (or x5 x4)) (or (and x2 x2) (and x1 x5)))))))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(check-sat)
(push 1)
(check-sat)
(pop 1)
(check-sat)
(push 1)
(check-sat)
(pop 1)
(assert (not (not (or (or (or (and (or (not (or x1 x0)) (not (or x2 x0))) (not (and (and x4 x3) (or x0 x6)))) (and (and (and (or x4 x1) (or x1 x2)) (or (not x1) (not x6))) (not (and (not x4) (and x6 x1))))) (or (and (and (not (not x6)) (or (and x6 x3) (not x1))) (or (or (and x5 x6) (or x5 x5)) (or (or x4 x6) (or x5 x6)))) (and (not (or (or x5 x2) (not x3))) (or (or (and x6 x6) (or x0 x5)) (or (and x1 x2) (and x6 x5)))))) (and (and (and (or (or (and x6 x2) (or x3 x5)) (and (or x6 x1) (and x1 x1))) (not (not (not x5)))) (or (or (not (or x3 x1)) (not (not x0))) (or (or (and x0 x4) (or x6 x6)) (and (not x2) (or x6 x1))))) (and (and (not (not (or x0 x1))) (not (or (or x2 x1) (not x1)))) (or (and (not (or x5 x2)) (or (not x0) (not x6))) (and (and (or x2 x4) (not x5)) (or (and x6 x5) (and x0 x6))))))))))
(assert (or (or (or (and x2 x5) (and x5 x3)) (not (not x5))) (not (not (or x6 x2)))))
(assert (not x3))
(check-sat)
(pop 1)
(check-sat)
