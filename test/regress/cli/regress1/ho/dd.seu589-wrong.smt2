; COMMAND-LINE: --mbqi
; EXPECT: unsat
(set-logic HO_ALL)
(declare-sort $ 0)
(declare-fun t ($ $) Bool)
(declare-fun tp ($ (-> $ Bool)) $)
(declare-fun p ($ $) $)
(assert (= p (lambda ((A $) (B $)) (@ (tp A) (lambda ((X $)) (@ (t X) B))))))
(assert (and (exists ((A $) (B $) (X $)) (and (@ (t X) B) (not (@ (t X) (@ (p A) B))))) (forall ((A $) (X $) (p (-> $ Bool))) (or (@ (t X) (@ (tp A) (lambda ((Xy $)) (p Xy))))))))
(check-sat)
