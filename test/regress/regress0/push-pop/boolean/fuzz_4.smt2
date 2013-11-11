; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: unsat
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
(declare-fun x7 () Bool)
(assert (or (and (not (or (or (or (and (or (and (and x7 x2) (or x6 x4)) (not (not x3))) (or (not (or x1 x2)) (and (or x1 x1) (and x5 x5)))) (or (and (and (or x2 x5) (and x6 x6)) (not (and x5 x6))) (and (and (and x5 x5) (or x1 x6)) (or (or x0 x3) (and x2 x4))))) (not (and (and (or (and x4 x4) (and x2 x4)) (or (and x0 x6) (or x6 x5))) (not (or (and x6 x7) (or x4 x4)))))) (and (not (or (or (or (not x6) (and x5 x6)) (or (and x2 x4) (or x6 x7))) (or (or (or x2 x5) (and x3 x6)) (or (and x5 x1) (and x1 x6))))) (and (not (and (and (not x1) (and x1 x7)) (and (or x2 x6) (or x0 x5)))) (and (not (and (not x4) (or x0 x2))) (and (not (and x4 x0)) (not (and x4 x1)))))))) (or (not (not (or (and (or (or (and x2 x7) (not x1)) (not (or x3 x7))) (and (not (not x4)) (or (or x7 x2) (and x3 x2)))) (or (or (and (or x2 x5) (or x0 x4)) (or (not x5) (not x5))) (and (not (and x0 x2)) (or (and x2 x7) (not x2))))))) (not (or (and (or (or (not (not x2)) (or (or x5 x2) (or x5 x7))) (and (and (or x0 x1) (or x7 x6)) (not (and x3 x0)))) (and (and (or (or x7 x5) (not x7)) (and (and x4 x5) (or x7 x2))) (or (or (not x1) (not x3)) (or (or x4 x7) (and x2 x0))))) (or (or (or (and (or x4 x6) (not x2)) (not (and x4 x4))) (not (or (and x2 x3) (not x1)))) (and (and (not (or x6 x3)) (not (or x4 x4))) (not (and (not x7) (and x2 x3))))))))) (or (not (or (or (and (and (not (or (and x0 x5) (and x7 x6))) (or (or (not x0) (not x3)) (or (and x0 x6) (or x7 x0)))) (or (or (and (not x4) (or x2 x3)) (not (not x7))) (not (and (and x2 x6) (not x0))))) (not (or (or (or (and x4 x2) (not x4)) (or (not x3) (and x5 x2))) (or (or (not x7) (not x1)) (not (and x1 x0)))))) (and (or (or (or (or (not x6) (and x3 x6)) (not (and x1 x0))) (or (or (and x7 x3) (not x1)) (not (or x7 x7)))) (and (or (or (not x1) (and x4 x2)) (or (not x3) (not x0))) (or (or (not x1) (not x7)) (not (or x1 x5))))) (or (or (and (and (not x0) (not x3)) (or (and x5 x4) (and x6 x0))) (or (or (and x4 x1) (and x7 x4)) (and (or x6 x0) (not x3)))) (not (and (or (not x4) (not x3)) (and (not x7) (not x7)))))))) (and (or (not (and (not (not (or (and x2 x6) (or x1 x2)))) (and (not (or (or x2 x4) (or x0 x4))) (or (or (and x2 x1) (and x1 x4)) (not (and x3 x0)))))) (and (not (not (and (and (not x3) (not x2)) (not (or x4 x6))))) (and (or (and (not (not x6)) (not (not x0))) (not (not (not x7)))) (and (not (not (and x6 x5))) (not (and (not x2) (or x5 x3))))))) (not (or (and (or (or (or (and x4 x3) (or x3 x6)) (and (and x4 x1) (or x4 x2))) (or (not (and x2 x6)) (or (not x0) (and x4 x5)))) (and (or (not (not x0)) (or (or x3 x7) (and x4 x2))) (or (not (and x0 x3)) (or (and x5 x0) (or x2 x3))))) (or (or (or (not (not x6)) (or (or x3 x1) (and x3 x4))) (and (or (or x0 x3) (or x3 x4)) (or (and x7 x0) (not x4)))) (or (not (not (and x7 x5))) (not (or (and x4 x3) (not x7)))))))))))
(assert (or (or x2 x1) (or x2 x4)))
(check-sat)
(push 1)
(check-sat)
(push 1)
(check-sat)
(pop 1)
(assert (not (or (and (not (or (or x5 x0) (or x7 x1))) (and (not (not x4)) (not (not x6)))) (not (not (or (or x4 x3) (not x2)))))))
(assert (and (and (and (and (not (not (and (or (and x7 x4) (and x7 x6)) (or (or x6 x5) (or x5 x3))))) (or (not (not (or (and x6 x6) (or x2 x6)))) (not (or (and (or x7 x5) (not x3)) (or (not x7) (not x0)))))) (or (or (and (or (not (not x1)) (and (or x0 x0) (and x4 x7))) (not (or (or x4 x5) (and x2 x5)))) (not (and (or (or x7 x0) (or x3 x1)) (not (and x3 x2))))) (and (not (and (not (or x4 x0)) (not (not x7)))) (and (not (not (and x1 x0))) (or (and (or x5 x5) (and x4 x5)) (not (not x6))))))) (not (and (or (not (or (or (and x0 x7) (not x0)) (or (and x7 x0) (and x0 x4)))) (and (not (not (not x0))) (or (and (not x3) (or x4 x2)) (not (and x1 x1))))) (and (and (or (or (and x0 x7) (or x0 x3)) (and (not x3) (or x4 x4))) (or (or (not x3) (or x7 x4)) (not (or x1 x2)))) (not (not (and (and x2 x5) (not x5)))))))) (not (not (and (or (and (or (not (not x3)) (or (or x0 x3) (and x3 x6))) (not (not (and x5 x4)))) (not (and (and (or x3 x7) (and x0 x2)) (or (and x5 x7) (not x1))))) (not (not (and (and (or x5 x3) (not x4)) (not (not x1))))))))))
(check-sat)
(push 1)
(check-sat)
(pop 1)
(check-sat)
(pop 1)
(assert (not (and (not (not (and (or (or (and x3 x5) (or x2 x6)) (not (not x7))) (or (not (and x2 x7)) (or (and x0 x1) (or x6 x1)))))) (not (and (not (not (or (or x0 x7) (and x1 x1)))) (not (or (not (or x4 x4)) (or (or x1 x4) (and x3 x3)))))))))
(assert (or x5 x7))
(check-sat)
(push 1)
(assert (and (or (not (not (or x5 x3))) (and (or (or x4 x5) (or x2 x1)) (and (not x5) (and x1 x3)))) (not (and (or (not x0) (not x7)) (not (not x5))))))
(assert (or (and (not (and (or (and (or (and x2 x3) (not x4)) (or (and x1 x1) (or x3 x5))) (or (not (and x4 x7)) (and (and x1 x2) (or x4 x0)))) (and (not (not (or x0 x3))) (or (not (not x4)) (and (and x1 x5) (not x2)))))) (and (or (not (not (or (and x1 x5) (not x5)))) (and (or (and (not x6) (or x7 x3)) (or (and x7 x0) (and x4 x4))) (not (not (not x5))))) (and (and (not (and (and x2 x4) (or x4 x1))) (or (and (and x4 x0) (not x2)) (and (or x6 x2) (and x5 x2)))) (not (not (not (not x7))))))) (or (and (or (and (and (not (or x3 x4)) (and (not x5) (not x1))) (not (or (not x7) (or x5 x0)))) (and (not (and (and x1 x7) (or x7 x5))) (not (and (not x0) (or x2 x0))))) (not (and (or (or (not x1) (or x6 x6)) (and (and x5 x4) (or x5 x6))) (not (or (not x4) (and x5 x4)))))) (not (not (or (and (and (not x5) (not x2)) (and (not x3) (or x3 x2))) (not (and (not x5) (and x6 x1)))))))))
(assert (or (not (or (not (not (or (and (and (and x5 x4) (not x4)) (or (not x6) (and x2 x1))) (or (and (or x0 x7) (not x5)) (not (and x7 x4)))))) (not (and (and (or (and (or x7 x3) (not x3)) (or (not x5) (not x3))) (not (not (not x7)))) (not (or (not (or x2 x4)) (not (and x3 x0)))))))) (and (not (not (or (and (or (and (not x7) (not x1)) (not (not x4))) (not (and (or x4 x1) (or x3 x5)))) (or (not (and (not x3) (and x3 x6))) (and (not (or x0 x5)) (not (and x5 x6))))))) (or (not (not (not (and (not (and x4 x3)) (not (not x1)))))) (not (and (or (and (or (or x2 x7) (and x0 x7)) (or (and x7 x7) (and x7 x4))) (and (and (not x6) (or x2 x2)) (and (and x5 x3) (and x6 x2)))) (or (and (not (or x5 x3)) (or (or x3 x3) (or x1 x2))) (not (not (or x3 x1))))))))))
(assert (not (or (or (and (and (and (or (and (or x5 x5) (or x6 x6)) (and (and x1 x2) (not x5))) (and (or (not x7) (or x1 x1)) (and (and x2 x2) (and x2 x5)))) (not (not (and (not x4) (not x1))))) (and (or (not (not (not x2))) (and (and (not x7) (or x4 x5)) (and (and x6 x2) (not x1)))) (not (and (not (or x4 x0)) (or (and x3 x4) (or x4 x6)))))) (and (and (or (and (not (not x5)) (not (not x6))) (or (not (not x0)) (and (or x5 x4) (not x5)))) (and (or (not (and x2 x3)) (and (or x7 x0) (and x6 x3))) (and (not (or x3 x4)) (or (or x2 x0) (not x0))))) (and (not (and (not (or x5 x3)) (not (or x5 x7)))) (and (or (not (and x7 x3)) (not (and x6 x6))) (or (or (not x0) (and x4 x2)) (not (and x3 x4))))))) (and (or (and (not (not (not (and x1 x3)))) (or (or (or (or x3 x3) (and x7 x1)) (or (not x5) (or x7 x6))) (and (or (and x0 x7) (or x4 x5)) (or (and x3 x1) (not x1))))) (or (and (and (not (and x6 x1)) (not (or x1 x2))) (and (not (not x4)) (and (or x0 x2) (or x0 x1)))) (or (not (and (not x4) (or x2 x2))) (and (and (or x1 x2) (not x7)) (and (and x0 x5) (or x2 x4)))))) (and (and (not (and (and (not x7) (not x5)) (or (and x4 x2) (and x6 x4)))) (and (or (not (not x2)) (and (not x1) (not x3))) (and (and (or x3 x0) (and x2 x2)) (or (not x7) (or x0 x4))))) (and (not (or (and (or x6 x4) (not x7)) (or (not x1) (and x2 x2)))) (and (or (or (not x5) (and x2 x1)) (or (not x7) (not x4))) (or (not (and x2 x7)) (or (not x5) (or x6 x7))))))))))
(assert (not x0))
(assert (and x0 x7))
(assert (not (not (or (and x6 x2) (and x0 x6)))))
(assert (or (not x2) (and x5 x0)))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (not (not (and (or (or x0 x0) (and x3 x5)) (not (not x4))))))
(check-sat)
(pop 1)
(assert (and (not (or (and x6 x2) (not x4))) (not (and (or x1 x7) (or x0 x6)))))
(check-sat)
