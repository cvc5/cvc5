; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
(set-logic QF_LIA)
(declare-fun x0 () Bool)
(declare-fun x1 () Bool)
(declare-fun x2 () Bool)
(declare-fun x3 () Bool)
(declare-fun x4 () Bool)
(declare-fun x5 () Bool)
(declare-fun x6 () Bool)
(declare-fun x7 () Bool)
(assert (not (and (not x3) (or x2 x1))))
(assert (or (not (or (and (not (or (or (or (not x2) (not x7)) (and (or x7 x4) (or x6 x7))) (not (not (or x6 x4))))) (not (or (or (and (or x1 x5) (and x4 x7)) (or (and x4 x6) (and x0 x0))) (not (and (and x5 x7) (and x0 x5)))))) (and (or (not (and (not (or x1 x7)) (and (or x1 x5) (and x6 x1)))) (or (and (not (not x5)) (not (not x5))) (and (or (or x0 x5) (and x1 x3)) (or (or x0 x6) (and x2 x7))))) (not (or (not (and (and x0 x4) (not x2))) (not (and (or x1 x3) (not x7)))))))) (not (and (and (not (or (or (or (not x7) (and x0 x5)) (not (or x4 x3))) (or (and (and x3 x1) (and x7 x4)) (or (and x5 x4) (not x6))))) (not (not (or (or (not x1) (or x7 x1)) (and (or x1 x5) (or x3 x1)))))) (or (and (not (and (and (and x2 x7) (or x4 x5)) (not (or x6 x4)))) (not (and (or (or x5 x2) (and x4 x3)) (or (or x4 x0) (and x0 x1))))) (not (and (and (and (not x1) (or x2 x1)) (not (or x7 x6))) (not (or (and x4 x4) (not x2))))))))))
(assert (and (or (and (not (or (and (and (or (not x0) (and x1 x7)) (and (not x0) (or x4 x5))) (or (or (and x6 x7) (or x3 x3)) (or (or x2 x2) (and x5 x6)))) (not (not (and (or x3 x6) (and x6 x0)))))) (and (not (not (not (not (and x7 x6))))) (or (not (or (not (or x7 x4)) (or (or x7 x4) (or x4 x2)))) (not (and (and (not x3) (or x3 x1)) (not (or x5 x4))))))) (and (and (and (not (not (and (not x5) (and x7 x5)))) (not (not (and (not x4) (and x5 x6))))) (or (not (and (and (or x4 x3) (not x6)) (and (and x2 x5) (or x5 x2)))) (or (and (or (and x0 x1) (not x3)) (or (not x4) (or x0 x2))) (not (or (not x6) (not x0)))))) (not (not (or (and (and (and x3 x0) (not x0)) (not (not x3))) (not (and (and x5 x3) (not x7)))))))) (and (or (not (and (or (and (and (not x0) (or x4 x2)) (or (and x3 x0) (or x6 x0))) (or (or (not x6) (not x7)) (not (and x5 x0)))) (and (not (or (and x1 x5) (not x2))) (or (not (and x3 x4)) (and (and x2 x0) (and x1 x6)))))) (not (and (or (and (and (or x5 x5) (not x2)) (or (or x6 x7) (or x7 x5))) (not (and (and x0 x4) (or x5 x1)))) (and (or (or (not x0) (or x7 x2)) (or (not x3) (and x1 x0))) (or (not (not x3)) (and (or x0 x0) (and x0 x2))))))) (or (or (and (and (and (and (not x5) (and x7 x6)) (and (and x0 x2) (or x3 x4))) (not (and (not x7) (or x3 x1)))) (and (not (or (or x4 x3) (or x5 x1))) (not (and (and x0 x0) (or x7 x6))))) (not (and (not (not (and x2 x6))) (and (and (or x3 x6) (or x4 x3)) (or (and x2 x1) (and x7 x6)))))) (and (not (and (and (not (not x3)) (not (or x3 x1))) (not (or (or x2 x3) (not x0))))) (not (or (not (or (and x2 x1) (or x4 x2))) (not (or (not x4) (or x2 x7))))))))))
(check-sat)
(push 1)
(assert (not (not (not (or (and (or (and x6 x5) (or x6 x7)) (or (not x2) (not x7))) (or (or (and x6 x3) (and x7 x7)) (or (and x6 x4) (or x0 x6))))))))
(assert (not (or (not (and (not (or (not (and (or x0 x1) (not x1))) (or (or (and x3 x1) (and x2 x0)) (or (and x1 x3) (or x7 x3))))) (or (or (and (and (not x2) (not x0)) (and (not x4) (not x2))) (not (and (not x6) (not x7)))) (not (not (not (or x0 x2))))))) (and (and (or (not (or (and (or x4 x2) (and x6 x4)) (and (or x4 x3) (and x1 x6)))) (and (or (or (not x5) (and x1 x5)) (and (and x6 x0) (not x0))) (or (and (or x5 x2) (and x7 x4)) (not (not x6))))) (or (and (or (not (or x7 x4)) (and (and x3 x3) (or x4 x0))) (not (not (or x0 x3)))) (or (not (not (and x3 x2))) (or (not (or x1 x6)) (or (and x5 x6) (and x6 x6)))))) (or (and (and (or (and (or x3 x7) (not x4)) (not (not x0))) (or (not (and x4 x3)) (not (and x6 x1)))) (not (not (or (and x1 x5) (and x7 x3))))) (and (or (or (not (and x4 x0)) (or (and x5 x0) (or x5 x4))) (or (and (and x6 x7) (not x4)) (and (not x0) (and x3 x1)))) (or (not (or (not x6) (or x2 x4))) (or (or (or x1 x5) (not x1)) (or (not x5) (and x3 x6))))))))))
(assert (not (or (not (not x4)) (and (and x5 x0) (and x6 x7)))))
(assert (not (not (and (and (or (not x5) (or x4 x5)) (or (and x7 x5) (or x7 x0))) (not (not (and x1 x7)))))))
(check-sat)
(push 1)
(check-sat)
(pop 1)
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (or (not (or x0 x6)) (not (and x1 x7))))
(check-sat)
(push 1)
(assert (or (and (not x7) (not x4)) (or (not x3) (or x7 x7))))
(assert (not (and (or (and (not (or (and (not (and (and x0 x0) (and x3 x3))) (and (and (not x3) (or x2 x5)) (not (not x0)))) (not (not (or (or x3 x5) (not x4)))))) (and (not (not (not (or (or x3 x4) (or x3 x6))))) (not (or (or (or (or x5 x1) (not x2)) (and (not x3) (and x1 x2))) (not (and (not x5) (and x1 x5))))))) (not (and (or (not (not (or (or x3 x0) (not x2)))) (and (or (or (and x2 x6) (or x5 x6)) (and (or x7 x7) (not x3))) (not (not (and x0 x7))))) (or (or (and (or (not x7) (or x0 x0)) (and (and x2 x4) (not x1))) (not (or (not x3) (and x7 x2)))) (and (not (and (or x4 x0) (not x4))) (not (or (or x5 x7) (or x5 x3)))))))) (or (not (not (and (or (and (not (or x0 x2)) (not (and x4 x1))) (or (not (and x4 x3)) (and (or x4 x0) (not x0)))) (and (or (or (not x7) (and x7 x4)) (and (and x3 x3) (or x3 x4))) (or (or (or x7 x7) (or x5 x7)) (not (not x3))))))) (not (not (or (not (not (and (and x3 x6) (not x5)))) (and (and (or (or x6 x2) (and x2 x6)) (not (or x6 x0))) (not (and (or x6 x6) (not x1)))))))))))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (not (or (and (or (not x6) (and x4 x4)) (not (and x3 x3))) (and (not (or x2 x4)) (and (not x1) (or x4 x6))))))
(check-sat)
