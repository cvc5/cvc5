; EXPECT: unsat
(set-logic QF_UF)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)

(declare-fun f (Bool) Bool)
(declare-fun g (Bool) Bool)
(declare-fun h (Bool) Bool)

(declare-fun x () Bool)
(declare-fun y () Bool)
(declare-fun z () Bool)

(assert (not (= (f x) (f y))))
(assert (not (= (g y) (g z))))
(assert (not (= (h z) (h x))))

(check-sat)

(exit)
