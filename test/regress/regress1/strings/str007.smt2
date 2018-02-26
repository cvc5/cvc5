(set-logic QF_S)
(set-info :status unsat)

(declare-fun x () String)
(declare-fun y () String)


(assert (or (= x y) (= x y)))

(assert (= (str.++ x "ba") (str.++ "ab" x)))
(assert (= (str.++ y "ab") (str.++ "ab" y)))

(check-sat)
