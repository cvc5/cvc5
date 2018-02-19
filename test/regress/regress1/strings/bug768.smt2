(set-logic QF_S)
(set-info :status sat)
(declare-fun f0 () String)
(declare-fun c0 () String)
(declare-fun f1 () String)
(declare-fun f2 () String)

(assert (= (str.++ f0 f1 f0 c0 f1 c0 f2 f2) "f(,f(c,c))"))

(check-sat)
