; COMMAND-LINE: --incremental
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
(assert (or (or x1 x1) (not x4)))
(assert (not (and (or (not (or (and (and x2 x0) (and x1 x4)) (and (or x4 x1) (and x2 x6)))) (and (or (not (and x4 x2)) (or (and x4 x3) (not x3))) (or (or (not x0) (or x2 x2)) (not (or x5 x6))))) (not (not (not (or (or x5 x6) (or x0 x3))))))))
(check-sat)
(push 1)
(assert (not (not (or (not x4) (not x6)))))
(assert (not (and (not (or (and (and (or (not (or x3 x4)) (or (and x0 x3) (or x3 x3))) (and (or (and x2 x1) (or x2 x4)) (and (not x2) (or x6 x2)))) (not (not (and (or x0 x1) (and x6 x4))))) (and (or (and (and (not x3) (not x2)) (or (or x3 x0) (and x4 x0))) (and (and (and x5 x0) (not x6)) (not (not x0)))) (or (and (not (and x2 x4)) (not (or x0 x2))) (not (not (and x6 x3))))))) (and (or (or (or (or (not (or x4 x1)) (not (and x6 x4))) (and (and (or x3 x0) (and x3 x2)) (or (or x6 x6) (and x5 x5)))) (not (not (and (and x6 x3) (or x2 x2))))) (or (or (and (not (not x3)) (or (and x5 x4) (or x3 x1))) (and (or (not x6) (or x6 x2)) (or (not x4) (or x4 x6)))) (or (and (not (and x0 x2)) (not (not x0))) (not (or (or x5 x1) (and x0 x4)))))) (and (or (and (or (not (and x0 x6)) (not (and x1 x5))) (or (or (or x2 x4) (or x1 x6)) (or (not x4) (or x3 x4)))) (and (or (not (or x6 x0)) (and (and x2 x0) (or x0 x4))) (not (or (not x3) (or x4 x0))))) (or (not (not (or (and x6 x5) (and x6 x6)))) (and (not (or (or x4 x5) (or x3 x0))) (not (and (not x2) (not x5))))))))))
(assert (or (not (not (and (not (and (and (not (or x1 x2)) (and (not x6) (or x3 x5))) (and (not (or x0 x2)) (not (or x4 x1))))) (or (or (not (not (and x4 x6))) (or (and (or x6 x4) (or x2 x3)) (or (and x6 x6) (not x3)))) (not (and (and (or x1 x3) (or x3 x0)) (or (not x2) (not x4)))))))) (not (or (not (and (not (or (or (not x6) (and x0 x1)) (and (or x5 x0) (and x0 x6)))) (not (not (and (and x5 x6) (and x4 x5)))))) (not (and (not (or (and (not x6) (or x1 x5)) (or (or x5 x6) (and x3 x6)))) (and (not (not (or x1 x4))) (and (or (or x4 x6) (or x2 x2)) (not (or x2 x6))))))))))
(check-sat)
(push 1)
(check-sat)
(push 1)
(check-sat)
(push 1)
(check-sat)
(push 1)
(assert (and (or (not (or (or (and (not (not (or x4 x6))) (not (not (or x6 x1)))) (or (not (or (and x6 x5) (or x4 x1))) (or (or (or x3 x4) (not x4)) (not (not x3))))) (or (or (and (or (and x3 x0) (and x2 x1)) (or (not x4) (or x4 x1))) (and (and (or x1 x2) (and x6 x6)) (not (or x3 x5)))) (or (and (and (and x5 x5) (not x3)) (not (or x0 x0))) (or (or (or x4 x2) (or x5 x1)) (and (or x1 x2) (not x0))))))) (or (and (not (not (and (or (and x6 x2) (and x2 x4)) (or (and x2 x1) (and x1 x1))))) (and (or (or (and (or x3 x0) (or x4 x2)) (or (or x0 x2) (and x0 x0))) (and (not (and x4 x6)) (not (and x5 x6)))) (and (and (and (not x1) (not x6)) (and (not x0) (and x1 x0))) (and (not (or x4 x6)) (or (or x0 x5) (not x0)))))) (or (and (not (or (not (and x1 x5)) (not (not x5)))) (or (or (and (and x6 x3) (and x0 x1)) (not (or x5 x1))) (and (and (or x6 x1) (not x4)) (and (or x1 x5) (or x4 x6))))) (and (not (or (and (not x4) (and x4 x3)) (or (not x1) (not x1)))) (or (or (and (and x3 x1) (and x4 x5)) (not (and x5 x0))) (and (not (not x3)) (or (and x5 x6) (and x3 x5)))))))) (or (and (not (or (and (not (not (and x5 x6))) (or (and (not x1) (not x4)) (or (and x0 x5) (not x1)))) (not (or (and (and x1 x3) (or x2 x1)) (and (or x6 x2) (not x5)))))) (not (and (and (or (and (not x3) (not x5)) (or (or x1 x3) (or x1 x2))) (and (or (and x4 x4) (not x1)) (and (or x6 x0) (not x1)))) (and (and (or (or x1 x2) (and x2 x3)) (and (not x6) (and x2 x2))) (or (not (or x4 x6)) (not (or x1 x3))))))) (and (or (not (or (not (not (not x3))) (or (not (not x0)) (not (and x2 x1))))) (or (not (or (not (not x3)) (not (not x6)))) (or (and (not (and x5 x3)) (not (or x3 x2))) (or (and (or x0 x2) (and x1 x2)) (or (not x2) (not x6)))))) (not (not (not (and (and (and x0 x0) (not x3)) (and (and x6 x4) (and x1 x5))))))))))
(check-sat)
(push 1)
(assert (not (not (and x3 x3))))
(check-sat)
(pop 1)
(assert (not (or x4 x2)))
(assert (and (not (and x3 x3)) (or (not x2) (or x4 x2))))
(assert (and (or x0 x1) (or x2 x5)))
(check-sat)
