; COMMAND-LINE: --bitblast=eager
; EXPECT: sat
; DISABLE-TESTER: model
(set-logic QF_UFBV)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(declare-fun v0 () (_ BitVec 4))
(declare-fun f ((_ BitVec 4)) (_ BitVec 4))
(declare-fun g ((_ BitVec 4)) (_ BitVec 4))

(assert (= (f v0) (g (f v0))))
(assert (= (f (f v0)) (g (f v0))))
(assert (= (f (f (f v0))) (g (f v0))))

(check-sat)
(exit)
