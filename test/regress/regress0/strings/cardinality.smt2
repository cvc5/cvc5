(set-logic QF_S)
(set-info :status unsat)

(set-option :strings-alphabet-card 2)

(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun w () String)
(declare-fun i () Int)

(assert (= i 1))
(assert (= (str.len x) i))
(assert (= (str.len y) i))
(assert (= (str.len z) i))
(assert (= (str.len w) 2))

(assert (not (=  x y)))
(assert (not (=  x z)))
(assert (not (=  z y)))


(check-sat)
