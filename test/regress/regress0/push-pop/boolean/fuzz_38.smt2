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
(assert (not (not (not (and (not (or (or (or (and x8 x3) (not x7)) (and (and x4 x3) (not x8))) (or (or (and x2 x7) (and x8 x0)) (and (or x2 x2) (or x8 x2))))) (or (not (or (or (or x5 x6) (or x8 x3)) (not (and x7 x6)))) (and (and (and (and x8 x1) (not x4)) (or (and x2 x7) (and x4 x2))) (and (and (not x3) (not x5)) (and (not x3) (or x5 x6))))))))))
(assert (and (and (not (or (or (not (not (and (not x1) (or x6 x3)))) (not (not (or (and x4 x8) (and x5 x4))))) (and (and (and (not (not x7)) (or (not x2) (or x4 x5))) (or (not (and x1 x5)) (or (not x2) (not x4)))) (and (not (and (not x6) (or x7 x0))) (or (or (and x2 x8) (and x0 x0)) (and (and x3 x3) (and x4 x3))))))) (not (not (not (or (or (and (or x1 x3) (not x0)) (not (not x7))) (not (or (and x2 x5) (and x8 x5)))))))) (not (not (or (and (or (or (not (or x1 x2)) (not (or x6 x3))) (not (or (and x0 x4) (and x3 x4)))) (or (not (and (not x2) (not x4))) (and (not (not x8)) (not (or x6 x0))))) (or (or (or (not (and x7 x0)) (and (and x8 x6) (and x3 x8))) (not (and (or x8 x4) (or x8 x4)))) (and (not (or (or x7 x2) (and x2 x0))) (not (and (or x7 x8) (or x6 x7))))))))))
(check-sat)
(push 1)
(assert (or x8 x2))
(assert (not (and (and (or (not (not (not (and x3 x3)))) (or (not (not (not x4))) (and (or (not x1) (or x8 x7)) (not (and x3 x7))))) (or (not (or (not (or x1 x7)) (or (and x0 x2) (and x1 x4)))) (not (not (or (and x5 x2) (and x3 x3)))))) (not (and (or (or (or (not x4) (and x0 x6)) (or (not x1) (not x1))) (and (and (not x8) (or x1 x3)) (or (and x1 x7) (and x2 x0)))) (and (not (not (not x5))) (or (or (not x1) (or x5 x5)) (and (not x7) (or x1 x5)))))))))
(check-sat)
(push 1)
(check-sat)
(push 1)
(check-sat)
(push 1)
(check-sat)
(push 1)
(assert (and x0 x2))
(check-sat)
(pop 1)
(assert (not (or (not (not x3)) (or (not x8) (and x8 x6)))))
(check-sat)
