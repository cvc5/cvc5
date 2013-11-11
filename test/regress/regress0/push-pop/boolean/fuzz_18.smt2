; COMMAND-LINE: --incremental
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
(assert (or (not (and (or (and (and (or (or (or (and x3 x6) (not x8)) (or (or x3 x0) (or x5 x8))) (and (and (or x0 x5) (not x0)) (not (not x4)))) (not (and (and (or x8 x3) (and x6 x0)) (or (and x7 x3) (and x5 x0))))) (not (not (and (and (and x2 x5) (not x0)) (not (not x1)))))) (not (not (or (not (or (and x3 x3) (not x8))) (and (not (or x0 x1)) (or (not x7) (and x4 x1))))))) (not (not (or (not (not (or (not x0) (or x3 x3)))) (not (not (or (not x6) (and x6 x0))))))))) (or (not (and (and (or (not (and (or (and x2 x1) (or x2 x7)) (and (and x7 x5) (or x5 x0)))) (and (or (not (and x7 x8)) (and (not x3) (or x6 x6))) (and (and (or x7 x5) (or x7 x5)) (not (not x7))))) (and (or (not (or (not x6) (or x0 x5))) (or (or (or x1 x3) (or x7 x4)) (or (and x1 x2) (not x8)))) (or (not (or (and x1 x6) (and x6 x7))) (and (not (and x2 x5)) (not (or x2 x6)))))) (or (or (not (or (or (or x2 x0) (and x3 x2)) (and (or x1 x3) (or x6 x4)))) (and (not (and (or x1 x7) (or x1 x2))) (not (not (not x0))))) (not (not (not (and (or x0 x0) (or x5 x2)))))))) (and (and (or (not (not (not (or (and x0 x2) (or x4 x2))))) (or (and (or (or (and x5 x8) (and x3 x1)) (not (not x2))) (or (or (and x6 x6) (not x8)) (and (not x5) (or x2 x4)))) (or (or (not (not x5)) (not (and x6 x5))) (or (and (and x2 x4) (and x5 x1)) (or (not x7) (not x6)))))) (not (and (not (or (and (not x1) (not x3)) (not (or x6 x2)))) (or (not (or (or x0 x4) (and x2 x5))) (or (or (and x4 x2) (and x1 x1)) (not (or x7 x8))))))) (and (or (not (or (not (not (not x2))) (not (and (or x3 x0) (and x3 x2))))) (or (not (and (and (and x0 x2) (and x8 x1)) (or (and x5 x7) (or x1 x2)))) (or (and (not (or x4 x3)) (or (or x6 x1) (and x1 x2))) (and (not (or x6 x1)) (and (or x1 x6) (or x3 x6)))))) (and (not (not (or (and (not x0) (or x5 x1)) (not (not x0))))) (or (or (and (not (not x4)) (and (not x1) (not x0))) (or (or (not x3) (and x5 x0)) (or (not x3) (and x1 x6)))) (not (not (or (and x7 x2) (not x5)))))))))))
(check-sat)
(push 1)
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (or (not (or x1 x2)) (and (or x3 x3) (or x1 x0))))
(check-sat)
(pop 1)
(assert (or (not (and (and x1 x3) (not x4))) (or (not (or x0 x0)) (or (and x1 x8) (not x0)))))
(assert (or (not x7) (and x1 x7)))
(assert (and (or (not (or (not x4) (or x3 x6))) (and (and (and x1 x1) (not x2)) (not (and x8 x5)))) (and (and (or (not x7) (and x0 x8)) (and (or x2 x5) (or x5 x4))) (and (or (and x5 x7) (not x6)) (or (and x5 x2) (or x8 x2))))))
(assert (or (and (or (or (or (not x4) (or x6 x7)) (not (or x3 x4))) (and (and (or x8 x3) (not x7)) (and (not x5) (or x8 x3)))) (or (and (or (or x3 x2) (and x0 x2)) (and (not x7) (and x8 x6))) (and (not (or x7 x7)) (or (or x8 x2) (not x6))))) (not (not (and (and (and x7 x7) (not x0)) (and (not x7) (not x2)))))))
(check-sat)
(push 1)
(assert (and x0 x5))
(check-sat)
(pop 1)
(check-sat)
