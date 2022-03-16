; COMMAND-LINE: --incremental
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
(declare-fun x5 () Bool)
(declare-fun x6 () Bool)
(declare-fun x7 () Bool)
(declare-fun x8 () Bool)
(check-sat)
(push 1)
(assert (or x1 x3))
(assert (or (or x5 x0) (not x0)))
(check-sat)
(push 1)
(assert (and (not (or (or (not (or (or (or (and (not x2) (not x0)) (or (and x1 x0) (not x3))) (not (or (and x2 x8) (and x6 x6)))) (or (not (not (not x4))) (and (or (and x1 x1) (not x1)) (or (not x1) (not x6)))))) (not (or (and (or (and (not x4) (and x0 x6)) (and (not x1) (or x8 x1))) (not (not (not x0)))) (not (and (not (not x4)) (and (not x3) (and x2 x0))))))) (or (and (or (and (not (or (not x7) (and x1 x2))) (and (not (not x1)) (and (not x1) (or x3 x2)))) (or (or (and (and x2 x0) (or x3 x2)) (and (and x0 x1) (or x0 x5))) (not (and (and x3 x8) (not x4))))) (and (and (not (and (and x1 x5) (or x1 x6))) (and (or (or x4 x7) (and x4 x3)) (or (or x2 x0) (or x5 x1)))) (or (or (not (not x1)) (or (and x6 x1) (or x4 x2))) (not (and (and x0 x8) (and x7 x1)))))) (and (or (or (and (and (and x6 x8) (and x3 x7)) (and (and x7 x0) (or x5 x6))) (and (or (or x5 x6) (and x8 x7)) (and (and x0 x6) (and x1 x1)))) (and (not (or (not x1) (or x1 x2))) (and (and (or x2 x8) (not x5)) (not (or x0 x3))))) (or (and (and (not (not x3)) (not (or x1 x6))) (and (not (not x8)) (or (and x0 x6) (or x0 x8)))) (not (and (or (not x3) (or x4 x3)) (and (not x7) (not x7))))))))) (and (or (not (or (and (or (or (not (or x2 x2)) (not (and x0 x8))) (or (or (not x8) (not x8)) (and (not x0) (and x1 x4)))) (and (or (not (or x4 x0)) (not (or x1 x6))) (and (and (and x4 x7) (or x3 x5)) (and (or x6 x6) (and x0 x3))))) (or (or (or (and (not x6) (and x2 x6)) (and (not x6) (or x5 x5))) (and (or (or x2 x8) (not x1)) (or (or x8 x4) (or x3 x5)))) (and (or (or (and x7 x8) (not x2)) (or (and x8 x2) (and x3 x2))) (or (or (and x2 x5) (and x1 x8)) (or (not x8) (not x5))))))) (not (not (and (and (or (not (and x8 x0)) (or (not x0) (not x8))) (or (and (and x3 x7) (not x8)) (and (and x4 x7) (and x8 x0)))) (or (and (or (and x1 x5) (not x2)) (not (and x8 x5))) (and (and (and x1 x8) (not x2)) (and (not x7) (or x5 x6)))))))) (not (and (and (or (or (not (and (not x6) (not x7))) (or (or (and x3 x7) (and x7 x0)) (not (not x8)))) (not (and (not (or x4 x6)) (and (not x1) (and x4 x3))))) (not (not (and (or (not x8) (and x5 x8)) (and (or x0 x5) (and x7 x3)))))) (not (and (not (and (not (and x6 x8)) (or (not x7) (and x3 x0)))) (or (not (not (and x8 x0))) (or (or (not x0) (not x6)) (or (not x8) (or x0 x7)))))))))))
(check-sat)
(push 1)
(assert (or (or x5 x6) (not x3)))
(assert (or (and (not (and (not (or (not (or x1 x5)) (or (and x2 x4) (and x1 x1)))) (and (or (and (or x5 x1) (and x2 x6)) (not (or x7 x6))) (or (not (and x7 x3)) (or (and x3 x7) (or x8 x4)))))) (and (or (and (or (not (not x6)) (or (and x6 x0) (not x7))) (or (not (not x0)) (or (not x8) (or x5 x6)))) (and (or (not (or x5 x2)) (not (or x8 x6))) (and (not (or x5 x2)) (and (and x7 x1) (and x3 x1))))) (and (not (not (or (or x8 x4) (not x3)))) (not (not (or (or x8 x2) (and x0 x8))))))) (and (not (or (and (not (not (not x4))) (or (or (or x5 x3) (not x1)) (not (not x2)))) (not (or (and (not x7) (not x5)) (and (and x5 x5) (not x3)))))) (and (not (or (or (not (not x3)) (or (and x4 x7) (and x7 x1))) (not (and (and x2 x1) (not x1))))) (and (and (or (and (not x0) (and x6 x2)) (and (and x8 x2) (not x5))) (not (not (or x6 x2)))) (not (not (and (and x2 x7) (not x2)))))))))
(check-sat)
(push 1)
(assert (or (or (not x6) (or x4 x3)) (or (or x8 x6) (not x4))))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (or (or (or (and (or (and (not (not (and (and x6 x0) (not x1)))) (not (or (and (and x4 x3) (and x1 x0)) (not (not x7))))) (and (not (not (and (and x3 x7) (or x5 x8)))) (and (not (and (or x4 x0) (or x1 x8))) (or (and (and x8 x6) (and x4 x7)) (not (or x1 x4)))))) (not (not (or (and (or (and x6 x0) (and x6 x3)) (or (not x3) (not x6))) (not (or (or x3 x5) (not x2))))))) (or (and (and (and (and (not (and x2 x4)) (or (not x3) (and x1 x8))) (or (or (not x6) (and x2 x7)) (and (and x0 x2) (not x1)))) (or (and (or (or x5 x6) (or x3 x3)) (not (or x7 x2))) (not (or (or x0 x8) (or x7 x2))))) (and (or (not (and (and x0 x8) (and x2 x1))) (not (and (not x7) (and x8 x1)))) (and (not (and (not x8) (or x2 x8))) (and (or (not x3) (not x7)) (not (not x7)))))) (or (and (not (or (or (not x7) (or x4 x7)) (and (not x7) (or x2 x7)))) (and (and (or (not x4) (or x6 x3)) (not (and x2 x4))) (and (not (or x1 x6)) (or (not x3) (or x1 x1))))) (not (or (not (not (not x5))) (not (or (or x4 x1) (not x0)))))))) (not (and (or (not (not (or (and (and x8 x7) (and x3 x5)) (or (and x1 x3) (or x0 x1))))) (not (not (or (or (not x0) (and x7 x8)) (not (not x2)))))) (or (or (not (or (or (or x8 x6) (or x4 x0)) (or (and x2 x7) (and x8 x8)))) (not (or (not (or x1 x2)) (not (not x7))))) (not (not (and (not (or x7 x4)) (and (not x0) (and x2 x1))))))))) (not (or (and (and (or (and (and (and (or x7 x1) (or x5 x2)) (or (not x8) (not x1))) (not (or (and x5 x4) (not x4)))) (and (or (or (and x7 x2) (not x4)) (not (or x8 x6))) (and (or (not x3) (and x7 x3)) (not (or x2 x4))))) (or (not (not (and (or x4 x7) (and x1 x5)))) (not (not (and (not x5) (not x2)))))) (not (not (not (and (not (not x7)) (not (and x1 x7))))))) (or (and (or (or (and (or (not x7) (not x6)) (or (or x2 x3) (or x2 x7))) (not (and (or x8 x8) (and x1 x8)))) (and (not (and (not x7) (not x6))) (or (and (and x5 x4) (or x1 x7)) (and (and x2 x1) (not x6))))) (or (or (or (or (and x3 x8) (not x4)) (and (or x2 x6) (and x0 x0))) (and (and (and x1 x3) (or x4 x2)) (not (or x4 x8)))) (or (and (not (or x8 x8)) (and (or x0 x3) (or x3 x0))) (and (not (and x5 x3)) (and (not x0) (and x3 x1)))))) (not (and (and (and (or (or x0 x3) (and x3 x7)) (and (or x3 x1) (and x4 x8))) (and (not (and x7 x6)) (or (not x0) (not x0)))) (and (or (and (or x0 x3) (not x0)) (or (or x1 x2) (or x8 x3))) (and (or (not x0) (or x2 x4)) (not (or x1 x1)))))))))))
(check-sat)
(pop 1)
(check-sat)
