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
(set-logic QF_LIA)
(declare-fun x0 () Bool)
(declare-fun x1 () Bool)
(declare-fun x2 () Bool)
(declare-fun x3 () Bool)
(declare-fun x4 () Bool)
(declare-fun x5 () Bool)
(declare-fun x6 () Bool)
(assert (and (or (and (or (not (and (or (and (not x1) (or x0 x2)) (and (not x3) (and x1 x1))) (not (or (not x0) (not x6))))) (and (not (and (not (and x6 x5)) (not (and x2 x3)))) (or (or (or (not x0) (and x4 x0)) (or (and x3 x3) (and x4 x1))) (and (not (and x1 x2)) (or (and x4 x3) (or x2 x0)))))) (or (and (and (not (and (and x5 x0) (and x4 x2))) (or (not (and x1 x5)) (and (not x0) (or x0 x0)))) (not (not (and (not x0) (and x6 x2))))) (not (and (or (and (or x5 x5) (and x3 x3)) (and (not x0) (or x5 x1))) (not (or (or x0 x0) (or x0 x2))))))) (or (or (not (not (and (or (or x0 x6) (and x2 x0)) (and (and x3 x1) (and x2 x4))))) (and (or (or (not (or x6 x3)) (or (and x0 x4) (or x5 x5))) (not (and (not x4) (not x3)))) (or (and (and (or x2 x6) (and x4 x6)) (and (not x6) (not x5))) (and (not (and x2 x5)) (or (and x0 x2) (or x5 x4)))))) (not (or (or (not (not (not x0))) (or (not (or x4 x1)) (not (not x4)))) (or (and (or (or x5 x6) (not x0)) (not (or x5 x3))) (and (and (or x3 x1) (or x3 x2)) (or (and x0 x4) (or x3 x1)))))))) (not (not (not (not (not (and (or (and x6 x1) (or x4 x4)) (and (not x0) (and x1 x2))))))))))
(check-sat)
(push 1)
(assert (not (or (not (or x6 x1)) (and (not x0) (and x3 x0)))))
(assert (not (or (and (and (not (not x4)) (or (and x6 x1) (not x1))) (not (and (not x1) (and x5 x3)))) (not (not (not (not x2)))))))
(check-sat)
(pop 1)
(assert (or (not (not (and (and (and (or (or (not (and x0 x3)) (or (not x2) (not x5))) (or (and (not x1) (not x5)) (or (not x1) (and x3 x0)))) (and (or (or (or x4 x1) (not x4)) (or (not x1) (not x4))) (or (not (and x3 x4)) (not (not x1))))) (not (or (not (not (and x2 x2))) (not (or (and x3 x5) (not x0)))))) (and (and (or (or (and (and x5 x1) (or x6 x6)) (not (and x4 x3))) (or (not (not x6)) (and (not x3) (or x2 x3)))) (not (or (not (or x4 x5)) (not (not x6))))) (and (and (and (and (or x2 x2) (or x1 x4)) (or (and x4 x2) (not x3))) (or (not (not x6)) (and (and x1 x0) (or x2 x4)))) (and (not (or (and x1 x5) (or x4 x1))) (not (or (or x3 x2) (and x5 x4))))))))) (not (or (not (not (and (or (and (or (not x4) (or x5 x6)) (not (and x1 x4))) (and (or (or x5 x5) (not x0)) (not (and x1 x2)))) (not (and (and (not x2) (not x2)) (and (or x5 x4) (not x2))))))) (or (not (or (or (or (not (or x2 x1)) (and (and x6 x5) (not x2))) (not (or (not x6) (not x4)))) (not (not (and (not x4) (and x6 x0)))))) (and (or (and (or (or (and x6 x0) (not x0)) (and (or x6 x1) (not x3))) (and (not (or x6 x2)) (not (or x1 x2)))) (and (and (or (or x1 x2) (and x0 x3)) (not (and x0 x4))) (and (and (not x0) (not x1)) (or (not x2) (and x4 x1))))) (or (and (or (or (or x1 x0) (not x3)) (or (and x6 x0) (or x2 x0))) (not (not (and x5 x0)))) (or (and (or (and x5 x5) (or x0 x2)) (or (not x1) (or x0 x6))) (or (and (not x3) (not x3)) (or (not x0) (and x1 x5)))))))))))
(assert (or (not (or x6 x5)) (and (not x3) (or x1 x3))))
(check-sat)
(push 1)
(check-sat)
(pop 1)
(assert (or (not (or (not (or (or (or (not x0) (not x3)) (and (or x3 x5) (or x3 x1))) (not (or (not x4) (or x1 x5))))) (not (or (and (and (not x2) (and x5 x5)) (not (not x1))) (or (not (and x2 x4)) (not (or x0 x5))))))) (and (and (or (not (and (not (and x1 x0)) (or (not x1) (and x6 x4)))) (or (not (and (and x1 x5) (not x4))) (and (or (or x3 x3) (and x3 x6)) (not (not x3))))) (not (not (and (and (and x1 x0) (or x3 x5)) (and (or x3 x1) (not x5)))))) (or (and (or (and (or (or x2 x5) (not x5)) (or (or x1 x2) (and x0 x0))) (and (not (not x2)) (and (and x3 x5) (not x1)))) (and (and (not (not x3)) (and (or x0 x3) (and x2 x6))) (and (and (not x6) (or x1 x6)) (and (and x0 x5) (or x0 x0))))) (not (or (and (not (not x4)) (and (not x0) (and x1 x3))) (or (or (not x3) (and x6 x2)) (and (not x5) (and x0 x3)))))))))
(check-sat)
(push 1)
(assert (and (not (or (or (not (not x2)) (not (not x2))) (not (or (or x3 x6) (and x6 x4))))) (or (and (or (or (not x3) (not x6)) (not (not x5))) (not (or (or x4 x6) (and x3 x6)))) (not (not (not (and x3 x6)))))))
(assert (or (and x4 x1) (and x6 x3)))
(assert (not (and (not (not (and x3 x0))) (and (not (not x1)) (or (or x0 x6) (and x2 x5))))))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(check-sat)
(pop 1)
(assert (and x4 x3))
(assert (not (or (not (not x5)) (and (and x6 x6) (or x1 x0)))))
(assert (not (and (and (not (or (not (not x6)) (and (and x0 x5) (or x2 x1)))) (or (not (or (or x6 x3) (or x1 x2))) (and (and (and x5 x5) (or x3 x6)) (not (or x0 x6))))) (not (and (or (or (or x2 x2) (or x4 x4)) (and (or x1 x1) (or x4 x5))) (not (and (and x5 x2) (or x3 x3))))))))
(check-sat)
