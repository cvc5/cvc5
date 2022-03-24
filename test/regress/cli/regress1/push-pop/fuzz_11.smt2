; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
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
(assert (not (not (or (or (not (or (not (or (or (not x3) (or x3 x3)) (not (not x3)))) (and (not (and (and x2 x1) (not x3))) (and (or (or x3 x1) (not x5)) (or (not x3) (or x4 x0)))))) (and (not (or (not (and (and x3 x0) (and x4 x5))) (or (not (and x0 x0)) (and (and x5 x4) (not x3))))) (and (and (or (not (and x3 x0)) (or (not x2) (or x5 x1))) (not (and (and x2 x0) (or x5 x4)))) (not (or (not (and x2 x1)) (or (not x4) (and x3 x5))))))) (or (or (and (and (or (not (or x5 x0)) (or (not x2) (not x3))) (not (not (and x1 x1)))) (and (or (or (or x2 x5) (not x1)) (or (or x2 x0) (and x0 x4))) (or (and (and x3 x5) (and x1 x4)) (and (or x5 x0) (and x1 x2))))) (not (or (not (or (and x2 x2) (or x4 x3))) (not (or (or x3 x4) (and x0 x0)))))) (or (not (not (not (and (and x1 x2) (or x5 x0))))) (or (and (or (and (and x0 x5) (and x0 x3)) (or (or x2 x0) (or x3 x3))) (or (and (or x4 x4) (or x0 x5)) (not (not x5)))) (or (not (or (or x4 x1) (and x4 x2))) (and (not (not x5)) (or (or x5 x4) (and x2 x1)))))))))))
(check-sat)
(push 1)
(assert (not (not (not x1))))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (or (or (or (or (and (or (and (and (not (and x1 x4)) (and (not x1) (not x1))) (or (not (or x2 x4)) (or (not x5) (and x2 x4)))) (or (not (and (and x0 x2) (and x2 x3))) (or (and (not x1) (or x4 x3)) (or (not x4) (and x2 x0))))) (not (not (and (or (not x3) (and x5 x0)) (not (and x1 x4)))))) (not (and (not (not (and (or x1 x4) (not x5)))) (not (and (not (and x2 x5)) (not (or x1 x4))))))) (and (and (or (or (and (or (or x1 x4) (not x5)) (and (and x3 x1) (or x4 x2))) (not (or (or x4 x4) (not x4)))) (and (and (or (and x1 x4) (and x3 x0)) (not (not x0))) (not (and (or x2 x3) (not x3))))) (and (and (and (not (not x3)) (and (not x5) (or x1 x3))) (not (and (and x4 x0) (and x5 x3)))) (not (and (and (not x1) (not x3)) (and (or x1 x5) (not x5)))))) (or (and (and (and (not (or x5 x3)) (or (or x3 x2) (not x1))) (not (and (not x3) (or x3 x1)))) (or (or (and (and x5 x5) (not x4)) (and (not x3) (not x1))) (not (or (not x1) (and x3 x2))))) (not (not (not (or (not x0) (or x1 x0)))))))) (not (not (or (not (and (not (and (or x5 x5) (not x2))) (not (not (and x5 x0))))) (or (and (and (and (and x1 x4) (or x0 x4)) (and (or x3 x4) (not x5))) (or (and (and x5 x3) (not x5)) (and (and x5 x3) (not x0)))) (or (not (and (or x5 x2) (and x0 x5))) (or (or (and x4 x4) (and x3 x0)) (and (or x3 x3) (or x0 x3))))))))) (or (not (or (not (and (not (or (and (and x5 x2) (and x5 x4)) (not (and x4 x2)))) (not (not (and (or x3 x5) (not x1)))))) (or (or (not (and (or (not x4) (and x3 x5)) (or (or x4 x0) (not x1)))) (and (or (or (or x1 x1) (and x5 x1)) (not (or x5 x5))) (not (or (or x3 x3) (not x5))))) (and (and (or (and (or x2 x2) (not x2)) (or (and x1 x3) (and x3 x4))) (or (and (and x0 x1) (not x5)) (and (not x3) (and x3 x5)))) (and (or (or (not x0) (not x3)) (not (not x1))) (not (not (not x4)))))))) (not (not (and (not (not (or (or (not x1) (or x2 x0)) (or (and x5 x4) (or x3 x4))))) (and (and (and (and (and x5 x3) (or x1 x4)) (or (or x1 x5) (not x3))) (not (not (not x0)))) (not (or (or (not x3) (and x5 x1)) (not (and x5 x4)))))))))))
(assert (not (and (and (and (not (or (not x3) (and x0 x2))) (and (not (not x5)) (not (not x1)))) (not (or (or (or x5 x1) (not x5)) (not (not x3))))) (and (not (and (or (or x2 x2) (and x5 x5)) (not (not x5)))) (not (not (not (and x4 x2))))))))
(assert (not (or (not (not (and (and (not (and (and x3 x5) (or x4 x3))) (and (and (or x0 x1) (and x3 x1)) (and (not x0) (and x4 x3)))) (and (and (not (or x0 x4)) (or (not x3) (not x1))) (or (or (or x4 x5) (and x3 x4)) (or (and x5 x2) (and x4 x0))))))) (not (or (not (or (and (or (or x3 x4) (or x5 x2)) (not (or x1 x0))) (or (not (not x0)) (not (and x1 x4))))) (not (not (or (and (and x0 x2) (or x1 x1)) (not (not x5))))))))))
(check-sat)
(push 1)
(check-sat)
(pop 1)
(assert (not (and (or (or (or (not x0) (or x1 x4)) (not (not x4))) (and (and (or x0 x1) (not x1)) (or (and x4 x5) (and x4 x5)))) (or (and (and (or x3 x3) (or x4 x0)) (or (and x1 x2) (and x3 x2))) (or (not (or x0 x0)) (not (and x5 x0)))))))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (and (and (or (or x5 x1) (or x3 x0)) (and (and x2 x3) (or x3 x5))) (or (and (not x3) (or x0 x3)) (and (not x3) (or x4 x0)))))
(assert (not (and (and (not x2) (or x0 x5)) (and (not x1) (or x3 x1)))))
(assert (not (or (or x3 x4) (or x5 x5))))
(assert (and (not (and (and (or (or (or (not (or x3 x3)) (and (not x4) (or x1 x0))) (and (or (not x4) (or x0 x5)) (and (not x2) (and x2 x3)))) (and (or (or (not x2) (and x4 x3)) (and (not x0) (not x0))) (or (and (and x1 x4) (not x1)) (and (and x2 x2) (or x4 x5))))) (and (not (and (and (and x5 x5) (and x5 x1)) (or (not x4) (not x0)))) (or (not (or (not x1) (not x1))) (or (and (not x0) (and x2 x4)) (or (and x5 x3) (and x2 x2)))))) (and (not (and (or (and (and x3 x5) (or x3 x3)) (or (and x5 x1) (and x4 x5))) (not (and (or x5 x1) (not x5))))) (or (and (or (not (or x5 x0)) (or (or x1 x2) (not x4))) (not (not (not x0)))) (not (and (or (and x2 x2) (and x2 x1)) (not (and x2 x1)))))))) (not (or (not (not (not (and (not (or x1 x3)) (and (and x5 x0) (or x4 x5)))))) (or (and (and (or (or (and x5 x4) (and x4 x3)) (or (and x2 x2) (and x3 x2))) (not (and (and x5 x0) (not x4)))) (and (and (not (and x3 x2)) (and (not x1) (not x5))) (or (or (and x1 x4) (not x2)) (not (or x5 x2))))) (or (and (not (and (and x5 x4) (or x1 x3))) (or (and (and x0 x0) (or x3 x5)) (not (not x2)))) (not (and (and (not x2) (and x1 x0)) (and (and x3 x0) (and x5 x5))))))))))
(assert (or (not (and (and (or (or (and (and (or (not x4) (not x0)) (or (or x2 x0) (not x2))) (not (and (not x3) (and x3 x3)))) (not (or (and (or x1 x4) (and x3 x2)) (and (or x4 x3) (and x4 x5))))) (not (and (or (or (or x3 x5) (or x5 x4)) (or (or x5 x1) (not x0))) (and (or (or x1 x5) (and x4 x1)) (and (or x3 x5) (not x5)))))) (and (and (or (and (and (not x3) (and x3 x2)) (or (or x3 x3) (and x5 x3))) (and (or (not x2) (not x4)) (and (and x2 x2) (and x1 x5)))) (and (not (and (not x5) (and x4 x2))) (not (not (and x0 x0))))) (not (and (not (not (and x0 x2))) (and (or (not x3) (not x3)) (not (not x5))))))) (not (and (and (not (and (or (and x2 x3) (or x2 x0)) (or (or x0 x3) (and x4 x4)))) (or (and (and (not x5) (and x0 x2)) (not (or x1 x2))) (not (and (or x3 x5) (not x4))))) (not (or (or (and (or x4 x4) (not x5)) (or (or x3 x4) (not x0))) (and (not (and x1 x4)) (and (not x4) (and x5 x2))))))))) (and (not (not (and (and (and (not (not (not x0))) (or (not (or x4 x5)) (or (and x1 x5) (not x2)))) (not (and (and (and x3 x4) (not x1)) (and (not x3) (and x1 x5))))) (or (not (and (or (not x2) (and x1 x5)) (not (and x3 x2)))) (or (and (and (or x1 x3) (or x5 x0)) (not (or x1 x3))) (not (not (not x4)))))))) (not (not (and (not (or (and (and (not x3) (not x2)) (not (or x4 x2))) (and (and (or x5 x1) (or x3 x5)) (not (and x4 x3))))) (or (or (not (not (or x3 x1))) (not (or (or x4 x0) (and x0 x3)))) (or (not (not (or x0 x3))) (or (and (not x2) (not x1)) (and (or x5 x0) (and x4 x5)))))))))))
(check-sat)
(push 1)
(assert (or (and (and (not (not (not (and (or (or x3 x0) (or x3 x1)) (not (not x2)))))) (not (not (or (and (or (and x4 x0) (not x4)) (not (or x4 x1))) (and (or (not x1) (or x3 x2)) (or (or x5 x1) (not x1))))))) (and (not (and (or (not (and (or x3 x1) (not x2))) (and (and (and x4 x5) (not x5)) (and (and x0 x0) (and x1 x2)))) (not (not (or (not x2) (and x3 x1)))))) (not (or (or (or (and (not x0) (and x4 x5)) (or (not x2) (and x2 x1))) (not (or (not x0) (not x0)))) (and (not (and (and x2 x0) (not x5))) (or (and (or x4 x0) (not x0)) (or (and x4 x3) (or x4 x5)))))))) (and (and (not (and (and (and (not (and x3 x0)) (and (not x1) (or x5 x1))) (or (not (not x1)) (not (or x0 x2)))) (and (or (not (not x0)) (or (and x4 x4) (and x2 x4))) (or (not (not x4)) (not (and x3 x4)))))) (not (or (not (not (and (or x0 x0) (or x4 x0)))) (not (and (not (not x4)) (or (and x0 x5) (or x3 x3))))))) (and (not (not (not (or (and (or x2 x3) (and x2 x2)) (not (or x0 x3)))))) (or (or (and (or (and (or x2 x4) (and x1 x4)) (and (and x5 x1) (not x0))) (not (not (or x0 x3)))) (not (and (and (not x4) (not x2)) (or (not x1) (or x3 x4))))) (not (and (not (or (or x4 x2) (and x2 x5))) (or (not (not x5)) (not (not x3))))))))))
(check-sat)
(push 1)
(check-sat)
(pop 1)
(assert (or (and (not x3) (not x3)) (and (and x2 x3) (or x4 x1))))
(assert (not (and (or (or (and (or (or (or (or x4 x0) (and x3 x0)) (or (or x3 x4) (not x4))) (or (or (and x2 x4) (and x4 x2)) (not (or x4 x0)))) (or (and (or (and x2 x4) (or x1 x0)) (and (not x1) (and x0 x5))) (or (and (not x4) (not x3)) (not (not x1))))) (not (or (and (and (or x3 x1) (or x2 x3)) (or (not x5) (and x4 x5))) (not (and (or x5 x2) (not x5)))))) (or (or (or (or (or (and x0 x5) (or x1 x4)) (not (and x1 x2))) (or (or (not x1) (or x4 x5)) (and (and x5 x0) (not x4)))) (or (or (or (or x0 x5) (and x0 x0)) (and (or x1 x2) (not x3))) (not (or (or x3 x1) (or x4 x0))))) (not (and (not (or (or x0 x3) (not x0))) (or (or (and x0 x5) (or x4 x3)) (or (and x4 x0) (or x0 x2))))))) (and (and (or (or (not (and (and x4 x0) (and x2 x1))) (and (or (and x3 x3) (and x2 x1)) (not (not x5)))) (not (not (and (not x3) (not x0))))) (or (and (and (and (and x3 x0) (or x2 x1)) (not (not x0))) (and (not (not x4)) (or (and x0 x1) (or x3 x4)))) (and (or (or (and x4 x2) (and x2 x0)) (or (and x5 x1) (not x0))) (and (and (not x1) (and x5 x0)) (or (or x0 x3) (and x5 x3)))))) (not (or (and (not (and (or x5 x3) (and x5 x1))) (or (or (and x2 x3) (or x3 x2)) (or (and x0 x5) (not x5)))) (or (or (not (not x5)) (or (and x0 x3) (and x5 x0))) (or (not (or x2 x1)) (or (or x3 x5) (and x0 x0))))))))))
(check-sat)
(pop 1)
(assert (or (and (and (and (not x1) (or x5 x5)) (and (or x2 x1) (not x0))) (and (not (or x1 x3)) (and (not x0) (or x3 x5)))) (or (or (and (or x0 x2) (not x1)) (and (and x3 x2) (or x0 x5))) (and (or (or x0 x0) (and x2 x5)) (or (or x0 x3) (not x1))))))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(check-sat)
(pop 1)
(assert (and (not (and (or (not (not (or (not (not x5)) (and (not x5) (not x1))))) (and (not (or (or (or x0 x0) (not x5)) (not (or x5 x2)))) (or (or (not (or x3 x2)) (or (not x2) (or x5 x5))) (or (and (not x2) (and x0 x2)) (and (and x5 x5) (or x3 x4)))))) (not (not (or (not (not (and x2 x2))) (and (and (not x2) (or x5 x0)) (or (not x4) (and x5 x4)))))))) (or (and (and (not (not (or (and (or x0 x0) (or x4 x1)) (or (and x5 x4) (or x1 x2))))) (and (and (not (and (and x0 x0) (or x5 x3))) (or (or (and x4 x3) (not x2)) (and (not x0) (not x3)))) (and (or (and (not x3) (not x1)) (not (not x0))) (or (and (and x4 x1) (not x0)) (and (not x0) (not x5)))))) (not (not (and (not (and (and x3 x3) (or x5 x5))) (and (or (not x4) (and x4 x3)) (and (and x4 x3) (or x4 x5))))))) (and (or (not (not (not (and (not x3) (or x4 x4))))) (or (not (not (or (not x2) (and x5 x4)))) (or (and (or (and x3 x5) (or x0 x1)) (and (not x2) (not x1))) (not (or (or x2 x0) (and x0 x2)))))) (and (and (not (and (or (not x3) (or x4 x1)) (and (or x2 x1) (not x0)))) (and (and (not (or x2 x2)) (not (not x3))) (or (and (and x2 x2) (or x4 x0)) (or (or x1 x2) (and x1 x5))))) (or (not (not (not (or x2 x3)))) (not (not (or (not x4) (or x3 x0))))))))))
(check-sat)
(push 1)
(assert (and (or (not (not (not (or (not x0) (and x3 x1))))) (or (not (not (or (not x2) (and x2 x3)))) (or (and (or (and x0 x3) (not x4)) (or (not x0) (not x1))) (or (and (or x4 x5) (and x0 x2)) (not (and x2 x5)))))) (not (not (not (and (and (not x1) (and x1 x0)) (not (and x2 x4))))))))
(assert (not x0))
(check-sat)
(pop 1)
(check-sat)
(push 1)
