; COMMAND-LINE: --no-check-models
(set-logic ALL)
(set-info :status sat)
(set-option :produce-models true)
(declare-fun A () (Set Int))
(declare-fun a () Int)
(assert (not (= A (as emptyset (Set Int)))))
(assert (member 10 A))
; this line raises an assertion error
(assert (= a (choose A)))
; this line raises an assertion error
;(assert (exists ((x Int)) (and (= x (choose A)) (= x a))))
(check-sat)