; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
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
(declare-fun x7 () Bool)
(declare-fun x8 () Bool)
(assert (or (or (not (or (or (not (or (and x4 x4) (not x7))) (not (and (and x5 x7) (not x7)))) (and (and (and (and x6 x6) (not x0)) (not (or x3 x1))) (and (or (not x1) (and x5 x3)) (or (or x7 x6) (not x4)))))) (not (or (or (or (not (or x3 x7)) (not (and x2 x8))) (and (not (not x1)) (or (and x0 x3) (or x2 x5)))) (or (or (or (and x8 x1) (or x3 x0)) (and (not x5) (and x8 x6))) (not (not (and x2 x5))))))) (not (not (and (not (or (or (not x7) (and x8 x2)) (not (or x6 x3)))) (not (and (not (and x8 x3)) (or (not x3) (or x8 x2)))))))))
(check-sat)
(push 1)
(assert (and (and (or (or (and (and (or x1 x5) (not x8)) (and (not x8) (and x0 x8))) (or (or (and x0 x3) (and x0 x6)) (and (or x7 x7) (and x7 x0)))) (or (and (or (and x8 x7) (or x3 x2)) (not (not x7))) (not (and (not x8) (not x5))))) (or (or (and (and (or x2 x6) (or x7 x4)) (and (or x4 x3) (not x5))) (and (or (not x2) (or x2 x7)) (not (and x8 x7)))) (and (and (and (and x5 x4) (not x3)) (not (not x8))) (or (and (or x6 x1) (or x0 x7)) (not (and x8 x4)))))) (and (not (and (or (not (or x5 x5)) (and (and x6 x3) (or x0 x0))) (and (not (or x0 x0)) (and (not x6) (and x8 x6))))) (or (and (not (not (and x3 x8))) (or (not (not x0)) (and (and x5 x6) (or x0 x4)))) (or (and (and (not x2) (not x0)) (and (and x4 x2) (or x1 x6))) (or (and (not x5) (not x8)) (not (and x5 x3))))))))
(check-sat)
(push 1)
(assert (and (or x7 x5) (and x2 x6)))
(check-sat)
(push 1)
(check-sat)
(push 1)
(assert (not (and x1 x6)))
(assert (or x7 x7))
(assert (not (or x0 x7)))
(check-sat)
(push 1)
(assert (and (not (or (or (and x6 x2) (or x2 x8)) (or (and x7 x3) (or x2 x5)))) (and (or (not (not x4)) (and (not x4) (not x2))) (not (not (or x1 x7))))))
(assert (not (and (or (and (and (not (and x6 x1)) (or (and x5 x3) (or x3 x1))) (or (or (not x2) (or x0 x1)) (not (or x7 x5)))) (not (or (not (not x8)) (and (not x4) (and x5 x8))))) (not (or (or (or (or x1 x1) (and x2 x3)) (and (and x5 x8) (not x7))) (and (not (or x5 x8)) (or (not x5) (and x2 x2))))))))
(assert (not x4))
(assert (not (and (not (or (not (or (not (or x8 x1)) (or (not x6) (not x4)))) (or (or (and (and x0 x7) (or x2 x7)) (or (or x7 x3) (and x5 x2))) (or (or (and x7 x0) (and x1 x1)) (and (not x7) (or x6 x7)))))) (or (and (and (and (not (not x0)) (and (or x7 x4) (or x3 x6))) (not (not (not x6)))) (or (or (and (and x1 x5) (or x7 x5)) (not (and x2 x3))) (not (or (not x8) (and x1 x8))))) (not (and (not (and (not x8) (and x1 x6))) (or (and (and x0 x0) (not x0)) (not (not x7)))))))))
(assert (or x1 x2))
(check-sat)
(pop 1)
(check-sat)
(pop 1)
(assert (not (and (not (and (not x5) (not x7))) (and (or (not x1) (and x4 x1)) (not (and x5 x8))))))
(assert (not (and (or (and (not (and (and (not (or (not x5) (and x4 x7))) (and (and (and x6 x1) (not x3)) (not (and x5 x1)))) (and (or (or (or x7 x2) (or x2 x6)) (not (not x2))) (and (and (not x6) (and x4 x8)) (and (not x5) (or x1 x6)))))) (or (not (or (not (and (and x3 x5) (or x7 x3))) (or (not (not x7)) (not (not x0))))) (or (not (not (and (or x3 x6) (and x6 x2)))) (or (not (or (or x7 x3) (not x5))) (or (or (and x1 x2) (and x4 x2)) (not (not x7))))))) (and (not (not (or (not (or (not x0) (not x4))) (or (and (and x3 x2) (and x8 x3)) (and (not x1) (not x6)))))) (not (not (or (or (and (or x8 x3) (not x8)) (or (or x7 x5) (or x7 x7))) (and (or (or x4 x4) (or x3 x3)) (and (not x8) (not x7)))))))) (and (not (or (not (or (or (not (and x4 x4)) (or (and x5 x8) (or x5 x4))) (not (not (and x6 x3))))) (not (or (or (or (not x3) (or x5 x2)) (not (not x0))) (and (or (or x6 x4) (and x0 x3)) (and (not x2) (not x0))))))) (and (not (not (or (or (or (or x6 x6) (and x6 x8)) (or (or x1 x5) (or x8 x4))) (and (and (not x6) (or x8 x0)) (not (or x0 x5)))))) (or (not (not (or (or (not x0) (and x3 x4)) (or (and x3 x3) (not x2))))) (and (or (or (or (not x1) (not x0)) (not (or x0 x2))) (and (and (and x8 x7) (and x8 x2)) (or (or x7 x4) (and x1 x3)))) (or (or (or (or x8 x1) (or x8 x6)) (not (not x6))) (or (or (and x8 x7) (or x4 x6)) (and (not x3) (and x0 x0)))))))))))
(check-sat)
(pop 1)
(check-sat)
(pop 1)
(assert (not (and (and x7 x2) (or x4 x6))))
(check-sat)
(push 1)
