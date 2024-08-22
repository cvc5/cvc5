; COMMAND-LINE: --mbqi
; EXPECT: unsat
(set-logic HO_ALL)
(declare-sort $ 0)
(declare-fun t ($ $) Bool)
(declare-fun tp ($ (-> $ Bool)) $)
(assert (and (forall ((X $) (p (-> $ Bool))) (not (@ (t X) (@ (tp X) (lambda ((Xy $)) (p Xy)))))) (exists ((X $)) (@ (t X) (@ (@ (lambda ((X $) (X $)) (@ (tp X) (lambda ((X $)) (@ (t X) X)))) X) X)))))
(check-sat)
