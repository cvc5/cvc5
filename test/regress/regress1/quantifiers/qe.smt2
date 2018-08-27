; COMMAND-LINE:
; EXPECT: (not (>= (+ a (* (- 1) b)) 1))
(set-logic LIA)
(set-info :status unsat)
(declare-fun a () Int)
(declare-fun b () Int)
(get-qe (exists ((x Int)) (and (<= a x) (<= x b))))
