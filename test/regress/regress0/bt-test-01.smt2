; EXPECT: unsat
(set-logic QF_UF)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)

(declare-fun x0 () Bool)
(declare-fun y0 () Bool)
(declare-fun z0 () Bool)

(assert (or x0 y0))
(assert (or (not y0) z0))

(declare-fun x1 () Bool)
(declare-fun y1 () Bool)

(assert x1)
(assert y1)

(declare-fun f (Bool) Bool)

(assert (not (= (f (or x0 z0)) (f (and x1 y1)))))

(check-sat)

(exit)
