; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
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
(assert (and (or (or (or (not (and (and (or (and x2 x1) (and x0 x4)) (and (and x0 x2) (not x1))) (or (not (not x3)) (not (and x6 x0))))) (and (and (or (or (and x2 x0) (and x0 x0)) (and (and x1 x6) (not x6))) (or (not (and x1 x4)) (or (or x0 x0) (or x3 x0)))) (not (or (or (and x1 x2) (and x1 x4)) (not (and x3 x2)))))) (or (or (and (and (and (or x1 x4) (not x1)) (or (not x1) (and x4 x5))) (and (not (or x3 x2)) (and (not x4) (not x6)))) (or (not (not (not x6))) (not (not (or x0 x2))))) (and (and (or (or (or x6 x3) (or x3 x1)) (not (and x4 x1))) (and (not (or x1 x3)) (or (or x3 x4) (or x4 x1)))) (or (not (or (not x0) (and x4 x5))) (not (not (or x4 x4))))))) (or (not (or (or (and (or (not x1) (and x3 x3)) (not (or x4 x0))) (and (and (not x6) (and x6 x3)) (and (not x1) (not x6)))) (or (or (not (and x5 x0)) (or (not x1) (or x3 x0))) (and (not (and x0 x0)) (and (and x5 x6) (not x2)))))) (and (not (and (not (not (not x0))) (and (or (and x2 x2) (or x1 x4)) (or (and x1 x6) (and x5 x3))))) (and (not (not (not (or x0 x0)))) (or (or (and (or x0 x2) (or x5 x2)) (not (not x2))) (not (or (and x3 x2) (or x5 x3)))))))) (or (and (or (or (not (not (or (not x6) (and x1 x2)))) (not (and (not (and x1 x3)) (and (not x2) (and x1 x4))))) (not (or (and (and (or x1 x2) (or x0 x2)) (and (or x6 x6) (and x4 x0))) (and (and (or x0 x4) (or x6 x0)) (and (and x0 x2) (or x3 x6)))))) (or (and (or (or (and (and x4 x6) (or x2 x6)) (and (not x6) (or x6 x1))) (not (not (not x3)))) (or (and (not (and x5 x2)) (or (or x5 x1) (or x4 x6))) (and (not (or x3 x4)) (or (not x2) (not x2))))) (or (or (not (not (or x1 x1))) (and (not (or x6 x4)) (and (or x6 x1) (not x5)))) (and (and (not (or x0 x0)) (and (or x0 x6) (not x6))) (or (and (not x0) (or x2 x1)) (or (and x6 x3) (not x3))))))) (not (or (not (not (or (or (and x3 x0) (and x3 x5)) (and (or x3 x0) (and x3 x0))))) (not (or (not (or (or x6 x4) (not x5))) (not (or (and x5 x2) (and x4 x4))))))))))
(assert (or x3 x5))
(assert (or (and (not x1) (not x6)) (not (not x6))))
(assert (not (not (and (and (or (or (and (not (or (or x0 x4) (and x4 x1))) (and (and (or x4 x5) (or x3 x1)) (or (not x0) (or x3 x4)))) (or (or (or (or x5 x5) (or x1 x4)) (or (and x5 x6) (not x1))) (or (or (or x2 x0) (or x0 x3)) (and (or x0 x4) (or x5 x6))))) (not (or (not (not (or x0 x2))) (and (and (and x0 x1) (and x0 x5)) (not (and x6 x0)))))) (and (not (or (not (or (or x2 x3) (and x6 x6))) (and (or (not x1) (or x2 x6)) (or (and x6 x4) (and x6 x5))))) (not (not (not (and (not x5) (or x1 x4))))))) (or (not (or (not (not (or (or x4 x0) (and x2 x6)))) (and (and (not (not x0)) (not (not x2))) (not (not (and x5 x6)))))) (or (and (and (and (or (not x4) (not x1)) (and (not x3) (not x1))) (not (and (not x1) (not x0)))) (or (or (or (or x3 x3) (not x3)) (or (not x0) (and x5 x5))) (or (not (and x0 x6)) (and (and x6 x1) (or x0 x3))))) (not (or (or (and (and x1 x5) (and x3 x6)) (and (not x0) (not x4))) (and (and (and x6 x0) (or x4 x0)) (or (and x0 x4) (not x5)))))))))))
(check-sat)
(push 1)
(check-sat)
(push 1)
(assert (and x2 x0))
(check-sat)
(push 1)
(assert (and (not (and (or x3 x3) (and x6 x0))) (or (not (or x6 x4)) (or (or x1 x2) (and x4 x6)))))
(assert (and (not (or (and (and (and x4 x2) (not x3)) (or (or x5 x6) (not x2))) (not (or (not x0) (not x4))))) (or (or (not (or (not x0) (or x2 x2))) (and (and (not x5) (not x1)) (or (not x6) (not x5)))) (and (and (not (and x2 x1)) (not (or x6 x0))) (or (not (or x0 x2)) (not (and x1 x2)))))))
(check-sat)
(pop 1)
(check-sat)
(pop 1)
(assert (and (not (or (not (not x4)) (or (or x1 x6) (and x2 x4)))) (not (and (and (or x1 x1) (and x1 x6)) (not (not x2))))))
(assert (not (not x3)))
(check-sat)
