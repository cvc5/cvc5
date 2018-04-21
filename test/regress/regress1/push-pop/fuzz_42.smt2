; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
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
(declare-fun x7 () Bool)
(declare-fun x8 () Bool)
(declare-fun x9 () Bool)
(assert (or (and (and (or (or (not (not (not (and x3 x2)))) (and (and (or (and x1 x1) (not x9)) (or (or x9 x5) (not x5))) (or (not (or x6 x3)) (not (not x5))))) (or (not (or (and (and x2 x5) (or x5 x6)) (not (or x0 x5)))) (not (or (or (or x0 x6) (not x1)) (not (not x9)))))) (or (and (not (or (or (not x2) (and x9 x9)) (or (not x6) (and x8 x5)))) (and (or (not (not x8)) (not (not x5))) (and (or (or x7 x1) (and x6 x9)) (or (and x5 x5) (and x0 x8))))) (and (and (or (or (not x9) (and x3 x0)) (and (or x6 x4) (and x0 x2))) (not (not (not x3)))) (or (or (or (or x2 x4) (or x8 x5)) (not (not x5))) (and (not (or x9 x9)) (not (not x1))))))) (and (or (and (and (not (not (or x9 x7))) (not (or (or x1 x5) (and x5 x0)))) (and (and (or (and x4 x3) (or x4 x4)) (and (or x7 x7) (or x6 x3))) (not (or (not x5) (or x8 x5))))) (or (or (not (and (or x1 x1) (and x4 x7))) (or (or (or x0 x3) (or x6 x8)) (and (not x5) (not x9)))) (and (and (and (and x8 x4) (and x5 x7)) (and (not x5) (not x5))) (not (not (not x8)))))) (not (or (and (or (or (not x6) (and x6 x9)) (and (and x0 x3) (or x4 x3))) (not (and (not x8) (and x3 x2)))) (or (and (not (or x6 x9)) (and (or x2 x4) (or x6 x4))) (not (and (or x1 x4) (and x1 x9)))))))) (or (not (and (not (and (or (not (not x0)) (not (or x5 x5))) (or (or (not x9) (or x8 x5)) (and (or x2 x1) (or x4 x4))))) (not (and (or (and (and x5 x6) (or x2 x3)) (or (not x3) (and x1 x0))) (and (and (and x3 x9) (and x1 x7)) (or (not x9) (and x7 x5))))))) (or (not (or (or (not (not (and x5 x0))) (or (and (not x3) (not x8)) (or (and x5 x7) (not x8)))) (or (and (and (or x3 x9) (or x5 x6)) (or (or x0 x7) (and x7 x6))) (or (or (or x3 x3) (not x7)) (not (or x4 x4)))))) (not (not (and (not (or (or x8 x5) (not x9))) (not (or (and x3 x3) (or x3 x2))))))))))
(check-sat)
(push 1)
(check-sat)
(push 1)
(check-sat)
(pop 1)
(assert (and (or (or x0 x9) (not x9)) (not (or x8 x3))))
(check-sat)
(push 1)
(assert (or (not (not (and x5 x8))) (not (not (not x7)))))
(check-sat)
(pop 1)
(assert (not (not (or (or (not x4) (not x5)) (not (not x6))))))
(assert (not (not (and (and x8 x5) (or x4 x1)))))
(assert (and (not (not (or (or (and (and (or (and x7 x6) (or x2 x3)) (or (or x3 x4) (not x6))) (or (not (or x9 x1)) (not (and x7 x8)))) (and (not (not (and x2 x0))) (not (and (not x7) (or x3 x3))))) (and (or (and (not (and x2 x0)) (and (or x5 x9) (and x4 x2))) (or (or (not x2) (and x4 x4)) (or (and x4 x7) (not x0)))) (and (or (not (not x8)) (or (or x2 x0) (or x2 x6))) (and (and (not x3) (or x9 x9)) (or (not x2) (and x4 x6)))))))) (not (or (not (not (and (not (or (and x7 x9) (or x0 x0))) (not (not (or x7 x9)))))) (and (not (or (and (not (or x0 x6)) (and (and x7 x3) (and x7 x8))) (or (and (not x7) (or x5 x6)) (and (not x9) (or x4 x2))))) (and (not (or (or (and x2 x2) (not x3)) (or (and x2 x0) (or x5 x4)))) (not (or (or (not x7) (or x0 x5)) (or (or x4 x8) (and x8 x2))))))))))
(assert (or (not (and x0 x3)) (or (or x0 x1) (or x2 x7))))
(check-sat)
(pop 1)
(assert (or x4 x9))
(check-sat)
(push 1)
(assert (or (or (or (not (or x9 x3)) (and (and x1 x9) (not x3))) (not (or (or x6 x1) (or x9 x8)))) (and (and (not (and x0 x6)) (and (not x0) (not x2))) (and (and (or x4 x5) (or x2 x8)) (and (and x5 x1) (and x4 x9))))))
(check-sat)
(pop 1)
(assert (and (not (or (and (not (not (not (or x9 x5)))) (not (or (not (or x5 x4)) (not (or x8 x9))))) (and (or (not (and (or x0 x0) (not x8))) (not (or (and x7 x5) (or x0 x2)))) (or (not (not (not x2))) (and (and (or x0 x4) (and x2 x2)) (and (and x6 x7) (not x9))))))) (and (and (not (not (or (or (not x8) (and x9 x1)) (and (and x5 x8) (or x9 x3))))) (and (and (not (or (not x7) (and x0 x9))) (and (not (and x3 x4)) (not (or x4 x0)))) (or (or (and (and x0 x0) (or x1 x5)) (and (and x7 x5) (and x6 x0))) (and (and (or x4 x7) (not x6)) (not (and x1 x0)))))) (or (or (and (and (or (and x5 x1) (not x5)) (not (and x2 x4))) (and (and (not x6) (or x1 x6)) (not (and x1 x1)))) (and (and (and (or x1 x6) (or x7 x2)) (not (not x8))) (not (and (and x6 x1) (not x1))))) (not (or (or (and (or x0 x9) (not x6)) (not (not x8))) (and (and (or x7 x2) (or x7 x0)) (not (not x5)))))))))
(check-sat)
