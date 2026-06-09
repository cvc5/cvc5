; COMMAND-LINE: --mbqi
; EXPECT: sat
(set-logic HO_ALL)
(declare-sort $ 0)
(declare-fun t ($ $) Bool)
(declare-fun tp ($ (-> $ Bool)) $)
(assert (and (exists ((X $)) (@ (t X) (@ (@ (lambda ((X1 $) (p $)) (@ (tp p) (lambda ((X $)) (@ (t X) X)))) X) X)))))
(check-sat)
